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
* **`partial_fixpoint` gives no induction principle**, so each walk is an
  induction either on the `ExprWF` derivation (`get_app_fn`, `pi_result`,
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

/-- `expr_ops::get_app_fn` refines `Expr.getAppFn` (`ExprOps.lean:915-918`). -/
theorem get_app_fn_refines {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.get_app_fn e = ok r) :
    absExpr r = ConLeche.Expr.getAppFn (absExpr e) ∧ ExprWF r := by
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.mk_const hn hus h1⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨habs, hwf⟩ := ihf h
    exact ⟨by rw [habs]; simp [ConLeche.Expr.getAppFn], hwf⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.forall_e hty hbo hm h1⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.let_e hty hw hbo h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.lit hl h1⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [expr_ops.get_app_fn.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.getAppFn], ExprWF.proj hs hx h1⟩

/-- `expr_ops::pi_result` refines `Expr.piResult` (`ExprOps.lean:1134-1138`). -/
theorem pi_result_refines {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.pi_result e = ok r) :
    absExpr r = ConLeche.Expr.piResult (absExpr e) ∧ ExprWF r := by
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.fvar hty h1⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.mk_const hn hus h1⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.app hf ha h1⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨habs, hwf⟩ := ihbo h
    exact ⟨by rw [habs]; simp [ConLeche.Expr.piResult], hwf⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.let_e hty hw hbo h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.lit hl h1⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [expr_ops.pi_result.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.piResult], ExprWF.proj hs hx h1⟩

/-- `expr_ops::fvar_type_d` refines `Expr.fvarTypeD` (`ExprOps.lean:1210-1215`).
No recursion, so the node's shape is all that is needed. -/
theorem fvar_type_d_refines {e r : expr.Expr} (he : ExprWF e)
    (h : expr_ops.fvar_type_d e = ok r) :
    absExpr r = ConLeche.Expr.fvarTypeD (absExpr e) ∧ ExprWF r := by
  cases he with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.bvar h1⟩
  | @fvar idx ty e hty h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], hty⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.sort hu h1⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.mk_const hn hus h1⟩
  | @app f a e hf ha h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.app hf ha h1⟩
  | @lam ty bo m e hty hbo hm h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.lam hty hbo hm h1⟩
  | @forall_e ty bo m e hty hbo hm h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.forall_e hty hbo hm h1⟩
  | @let_e ty w bo e hty hw hbo h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.let_e hty hw hbo h1⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.lit hl h1⟩
  | @proj s i x e hs hx h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [expr_ops.fvar_type_d] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [Expr.dup_eq h]
    exact ⟨by simp [ConLeche.Expr.fvarTypeD], ExprWF.proj hs hx h1⟩

/-- `expr_ops::pi_arity` refines `Expr.piArity` (`ExprOps.lean:1269-1272`).  A
`u64` result, so the equation is on `.val`; nothing is claimed when the count
overflows, which is the exact-result-on-success convention. -/
theorem pi_arity_refines {e : expr.Expr} {r : Std.U64} (he : ExprWF e)
    (h : expr_ops.pi_arity e = ok r) :
    r.val = ConLeche.Expr.piArity (absExpr e) := by
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨i, hi, hr⟩ := bind_eq_ok_iff.mp h
    rw [HashMap.uscalar_add_eq hr, ihbo hi]
    simp [ConLeche.Expr.piArity]
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [expr_ops.pi_arity.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]; simp [ConLeche.Expr.piArity]

/-- `expr_ops::result_sort` refines `Expr.resultSort` (`ExprOps.lean:1274-1278`).
An `Option Level` result, so the equation is `Option.map absLevel` — which makes
the `none` case a claim too — and well-formedness of the level is the second
clause. -/
theorem result_sort_refines {e : expr.Expr} {r : Option level.Level} (he : ExprWF e)
    (h : expr_ops.result_sort e = ok r) :
    Option.map absLevel r = ConLeche.Expr.resultSort (absExpr e) ∧
      ∀ u, r = some u → LevelWF u := by
  induction he generalizing r with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨c, hc, hr⟩ := h
    have hcu : c = u := Result.ok_injective (hc.symm.trans (level_dup_eq u))
    subst hcu
    rw [← Result.ok_injective hr]
    refine ⟨by simp [ConLeche.Expr.resultSort], ?_⟩
    intro u' hu'
    simp only [Option.some.injEq] at hu'
    rw [← hu']; exact hu
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    obtain ⟨habs, hwf⟩ := ihbo h
    exact ⟨by rw [habs]; simp [ConLeche.Expr.resultSort], hwf⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    rw [expr_ops.result_sort.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.resultSort], by simp⟩

/-- `expr_ops::get_app_args_go` refines `Expr.getAppArgs`
(`ExprOps.lean:920-923`) *with an accumulator*: the port pushes after the
recursive call where Lean writes `getAppArgs f ++ [a]` (task #13's deviation
3), so the lemma carries `absExprs out ++ …`. -/
theorem get_app_args_go_refines {e : expr.Expr} (he : ExprWF e) :
    ∀ (out r : alloc.vec.Vec expr.Expr), ExprsWF out →
      expr_ops.get_app_args_go e out = ok r →
      absExprs r = absExprs out ++ ConLeche.Expr.getAppArgs (absExpr e) ∧ ExprsWF r := by
  induction he with
  | @bvar i e h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @fvar idx ty e hty h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @sort u e hu h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @mk_const n us e hn hus h1 =>
    obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @app f a e hf ha h1 ihf iha =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
    obtain ⟨out2, hrec, c, hdup, hpush⟩ := h
    obtain ⟨habs, hwf⟩ := ihf out out2 hout hrec
    rw [Expr.dup_eq hdup] at hpush
    refine ⟨?_, exprsWF_push hwf ha hpush⟩
    rw [absExprs_push hpush, habs, List.append_assoc]
    simp [ConLeche.Expr.getAppArgs]
  | @lam ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @forall_e ty bo m e hty hbo hm h1 ihty ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @let_e ty w bo e hty hw hbo h1 ihty ihw ihbo =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @lit l e hl h1 =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩
  | @proj s i x e hs hx h1 ih =>
    obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
    intro out r hout h
    rw [expr_ops.get_app_args_go.eq_def] at h
    simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
    rw [← Result.ok_injective h]
    exact ⟨by simp [ConLeche.Expr.getAppArgs], hout⟩

/-- `expr_ops::get_app_args` refines `Expr.getAppArgs` (`ExprOps.lean:920-923`):
the `out = []` wrapper. -/
theorem get_app_args_refines {e : expr.Expr} {r : alloc.vec.Vec expr.Expr}
    (he : ExprWF e) (h : expr_ops.get_app_args e = ok r) :
    absExprs r = ConLeche.Expr.getAppArgs (absExpr e) ∧ ExprsWF r := by
  rw [expr_ops.get_app_args] at h
  obtain ⟨habs, hwf⟩ := get_app_args_go_refines he _ r exprsWF_new h
  exact ⟨by rw [habs]; simp, hwf⟩

/-- `expr_ops::mk_app_n_from` refines `Expr.mkAppN` (`ExprOps.lean:925-928`) at
the arguments from `i` on.  The induction is on the `Nat` measure
`args.length - i`: the generated function is a `partial_fixpoint`. -/
theorem mk_app_n_from_refines (N : Nat) :
    ∀ (f : expr.Expr) (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (r : expr.Expr),
      args.val.length - i.val = N → ExprWF f → ExprsWF args →
      expr_ops.mk_app_n_from f args i = ok r →
      absExpr r = ConLeche.Expr.mkAppN (absExpr f) ((absExprs args).drop i.val) ∧
        ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro f args i r hN hf hargs h
    rw [expr_ops.mk_app_n_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      rw [← Result.ok_injective h]
      refine ⟨?_, hf⟩
      rw [List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      simp [ConLeche.Expr.mkAppN]
    · rename_i hge
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, c, hdup, a2, happ, i2, hi2, hrec⟩ := h
      obtain ⟨hlt, hxwf, hdrop⟩ := vec_index_expr hargs hidx
      rw [Expr.dup_eq hdup] at happ
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) a2 args i2 r rfl
        (Expr.app_wf hf hxwf happ) hargs hrec
      refine ⟨?_, hwf⟩
      rw [habs, Expr.app_refines happ, hi2v, hdrop]
      simp [ConLeche.Expr.mkAppN]

/-- `expr_ops::mk_app_n` refines `Expr.mkAppN` (`ExprOps.lean:925-928`): the
`i = 0` wrapper. -/
theorem mk_app_n_refines {f : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : expr.Expr} (hf : ExprWF f) (hargs : ExprsWF args)
    (h : expr_ops.mk_app_n f args = ok r) :
    absExpr r = ConLeche.Expr.mkAppN (absExpr f) (absExprs args) ∧ ExprWF r := by
  rw [expr_ops.mk_app_n] at h
  obtain ⟨habs, hwf⟩ := mk_app_n_from_refines _ f args 0#usize r rfl hf hargs h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]

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

/-- A binder list is well formed when every domain and datum is. -/
def BindersWF (bs : alloc.vec.Vec (expr.Expr × expr.BinderMeta)) : Prop :=
  ∀ p ∈ bs.val, ExprWF p.1 ∧ BinderMetaWF p.2

@[simp] theorem absBinders_new :
    absBinders (alloc.vec.Vec.new (expr.Expr × expr.BinderMeta)) = [] := rfl

theorem bindersWF_new : BindersWF (alloc.vec.Vec.new (expr.Expr × expr.BinderMeta)) := by
  intro p hp; simp at hp

theorem absBinders_push {bs bs' : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {t : expr.Expr} {m : expr.BinderMeta}
    (h : alloc.vec.Vec.push bs (t, m) = ok bs') :
    absBinders bs' = absBinders bs ++ [(absExpr t, absBinderMeta m)] := by
  rw [absBinders, absBinders, vec_push_val h, List.map_append]; rfl

theorem bindersWF_push {bs bs' : alloc.vec.Vec (expr.Expr × expr.BinderMeta)}
    {t : expr.Expr} {m : expr.BinderMeta} (hbs : BindersWF bs) (ht : ExprWF t)
    (hm : BinderMetaWF m) (h : alloc.vec.Vec.push bs (t, m) = ok bs') :
    BindersWF bs' := by
  intro p hp
  rw [vec_push_val h] at hp
  rcases List.mem_append.1 hp with h1 | h1
  · exact hbs p h1
  · simp only [List.mem_singleton] at h1; rw [h1]; exact ⟨ht, hm⟩

/-- `expr_ops::strip_pis_go` refines `Expr.stripPis` (`ExprOps.lean:1126-1132`)
with the binder list accumulated on the way *in* (task #13's deviation 3: Lean
conses on the way out, and both orders give the same outermost-first list).
The `Option.map` equation makes the `none` case a claim too; well-formedness of
the two components is the second clause. -/
theorem strip_pis_go_refines (N : Nat) :
    ∀ (k : Std.U64) (e : expr.Expr)
      (out : alloc.vec.Vec (expr.Expr × expr.BinderMeta))
      (r : Option ((alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr)),
      k.val = N → ExprWF e → BindersWF out →
      expr_ops.strip_pis_go k e out = ok r →
      (Option.map (fun p => (absBinders p.1, absExpr p.2)) r =
        Option.map (fun p => (absBinders out ++ p.1, p.2))
          (ConLeche.Expr.stripPis k.val (absExpr e))) ∧
      (∀ p, r = some p → BindersWF p.1 ∧ ExprWF p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k e out r hN he hout h
    rw [expr_ops.strip_pis_go.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.stripPis], fun p hp => by
        simp only [Option.some.injEq] at hp; rw [← hp]; exact ⟨hout, he⟩⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨c, hdup, bm, hbm, out1, hpush, i, hi, hrec⟩ := h
        rw [Expr.dup_eq hdup] at hpush
        rw [Expr.binder_meta_dup_eq hbm] at hpush
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) i bo out1 r hiv hbo
          (bindersWF_push hout hty hm hpush) hrec
        refine ⟨?_, hwf⟩
        rw [habs, absBinders_push hpush, hn]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.stripPis, hiv, Option.map_map]
        cases ConLeche.Expr.stripPis n (absExpr bo) with
        | none => simp
        | some q => simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripPis], by simp⟩

/-- `expr_ops::strip_pis` refines `Expr.stripPis` (`ExprOps.lean:1126-1132`):
the `out = []` wrapper. -/
theorem strip_pis_refines {k : Std.U64} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr)}
    (he : ExprWF e) (h : expr_ops.strip_pis k e = ok r) :
    Option.map (fun p => (absBinders p.1, absExpr p.2)) r =
        ConLeche.Expr.stripPis k.val (absExpr e) ∧
      (∀ p, r = some p → BindersWF p.1 ∧ ExprWF p.2) := by
  rw [expr_ops.strip_pis] at h
  obtain ⟨habs, hwf⟩ := strip_pis_go_refines _ k e _ r rfl he bindersWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  cases ConLeche.Expr.stripPis k.val (absExpr e) with
  | none => simp
  | some q => simp

/-- `expr_ops::strip_lams_go` refines `Expr.stripLams` (`ExprOps.lean:1118-1124`)
with the binder list accumulated on the way *in* (task #13's deviation 3: Lean
conses on the way out, and both orders give the same outermost-first list).
The `Option.map` equation makes the `none` case a claim too; well-formedness of
the two components is the second clause. -/
theorem strip_lams_go_refines (N : Nat) :
    ∀ (k : Std.U64) (e : expr.Expr)
      (out : alloc.vec.Vec (expr.Expr × expr.BinderMeta))
      (r : Option ((alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr)),
      k.val = N → ExprWF e → BindersWF out →
      expr_ops.strip_lams_go k e out = ok r →
      (Option.map (fun p => (absBinders p.1, absExpr p.2)) r =
        Option.map (fun p => (absBinders out ++ p.1, p.2))
          (ConLeche.Expr.stripLams k.val (absExpr e))) ∧
      (∀ p, r = some p → BindersWF p.1 ∧ ExprWF p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k e out r hN he hout h
    rw [expr_ops.strip_lams_go.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.stripLams], fun p hp => by
        simp only [Option.some.injEq] at hp; rw [← hp]; exact ⟨hout, he⟩⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨c, hdup, bm, hbm, out1, hpush, i, hi, hrec⟩ := h
        rw [Expr.dup_eq hdup] at hpush
        rw [Expr.binder_meta_dup_eq hbm] at hpush
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) i bo out1 r hiv hbo
          (bindersWF_push hout hty hm hpush) hrec
        refine ⟨?_, hwf⟩
        rw [habs, absBinders_push hpush, hn]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.stripLams, hiv, Option.map_map]
        cases ConLeche.Expr.stripLams n (absExpr bo) with
        | none => simp
        | some q => simp
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.stripLams], by simp⟩

/-- `expr_ops::strip_lams` refines `Expr.stripLams` (`ExprOps.lean:1118-1124`):
the `out = []` wrapper. -/
theorem strip_lams_refines {k : Std.U64} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec (expr.Expr × expr.BinderMeta)) × expr.Expr)}
    (he : ExprWF e) (h : expr_ops.strip_lams k e = ok r) :
    Option.map (fun p => (absBinders p.1, absExpr p.2)) r =
        ConLeche.Expr.stripLams k.val (absExpr e) ∧
      (∀ p, r = some p → BindersWF p.1 ∧ ExprWF p.2) := by
  rw [expr_ops.strip_lams] at h
  obtain ⟨habs, hwf⟩ := strip_lams_go_refines _ k e _ r rfl he bindersWF_new h
  refine ⟨?_, hwf⟩
  rw [habs]
  cases ConLeche.Expr.stripLams k.val (absExpr e) with
  | none => simp
  | some q => simp

/-! ## The instantiation cascade

`instPis`/`instPisAt`/`instLamsAt`/`instSpine` fold `Expr.instantiate1` over the
argument list, so each of these proofs is an induction on `args.length - i`
whose step is `instantiate1_refines` (the foundation's headline lemma).  The
con-leche side matches on the *list*, which `vec_index_expr` supplies:
`(absExprs args).drop i = absExpr args[i] :: (absExprs args).drop (i+1)`. -/

/-- `expr_ops::inst_pis_from` refines `Expr.instPis` (`ExprOps.lean:1140-1144`)
at the arguments from `i` on. -/
theorem inst_pis_from_refines (N : Nat) :
    ∀ (e : expr.Expr) (args : alloc.vec.Vec expr.Expr) (i : Std.Usize)
      (r : Option expr.Expr),
      args.val.length - i.val = N → ExprWF e → ExprsWF args →
      expr_ops.inst_pis_from e args i = ok r →
      (Option.map absExpr r =
        ConLeche.Expr.instPis (absExpr e) ((absExprs args).drop i.val)) ∧
      (∀ t, r = some t → ExprWF t) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro e args i r hN he hargs h
    rw [expr_ops.inst_pis_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr,
        List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.Expr.instPis], fun t ht => by
        simp only [Option.some.injEq] at ht; rw [← ht]; exact he⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      obtain ⟨a0, rest0, hd⟩ :
          ∃ a0 rest0, (absExprs args).drop i.val = a0 :: rest0 := by
        rcases hh : (absExprs args).drop i.val with _ | ⟨a0, rest0⟩
        · exfalso
          have hz : ((absExprs args).drop i.val).length = 0 := by rw [hh]; rfl
          rw [List.length_drop, absExprs, List.length_map] at hz
          omega
        · exact ⟨a0, rest0, rfl⟩
      cases he with
      | @bvar i2 e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨x, hidx, b, hinst, i2, hi2, hrec⟩ := h
        obtain ⟨hlt, hxwf, hdrop⟩ := vec_index_expr hargs hidx
        obtain ⟨hiabs, hiwf⟩ := instantiate1_refines hbo hxwf hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) b args i2 r rfl
          hiwf hargs hrec
        refine ⟨?_, hwf⟩
        rw [habs, hi2v, hdrop, hiabs,
          show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
        simp [ConLeche.Expr.instPis]
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩
      | @proj s i2 x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPis], by simp⟩

/-- `expr_ops::inst_pis` refines `Expr.instPis` (`ExprOps.lean:1140-1144`). -/
theorem inst_pis_refines {e : expr.Expr} {args : alloc.vec.Vec expr.Expr}
    {r : Option expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : expr_ops.inst_pis e args = ok r) :
    Option.map absExpr r = ConLeche.Expr.instPis (absExpr e) (absExprs args) ∧
      (∀ t, r = some t → ExprWF t) := by
  rw [expr_ops.inst_pis] at h
  obtain ⟨habs, hwf⟩ := inst_pis_from_refines _ e args 0#usize r rfl he hargs h
  exact ⟨by rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero], hwf⟩

/-- `expr_ops::inst_pis_at_from` refines `Expr.instPisAt`
(`ExprOps.lean:1146-1154`): the domains are accumulated on the way in, so the
lemma carries `absExprs out ++ …`. -/
theorem inst_pis_at_from_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprWF e → ExprsWF args → ExprsWF out →
      expr_ops.inst_pis_at_from args i e out = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r =
        Option.map (fun p => (absExprs out ++ p.1, p.2))
          (ConLeche.Expr.instPisAt ((absExprs args).drop i.val) (absExpr e))) ∧
      (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i e out r hN he hargs hout h
    rw [expr_ops.inst_pis_at_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr,
        List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.Expr.instPisAt], fun p hp => by
        simp only [Option.some.injEq] at hp; rw [← hp]; exact ⟨hout, he⟩⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      obtain ⟨a0, rest0, hd⟩ :
          ∃ a0 rest0, (absExprs args).drop i.val = a0 :: rest0 := by
        rcases hh : (absExprs args).drop i.val with _ | ⟨a0, rest0⟩
        · exfalso
          have hz : ((absExprs args).drop i.val).length = 0 := by rw [hh]; rfl
          rw [List.length_drop, absExprs, List.length_map] at hz
          omega
        · exact ⟨a0, rest0, rfl⟩
      cases he with
      | @bvar i2 e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨c, hdup, out1, hpush, x, hidx, b, hinst, i2, hi2, hrec⟩ := h
        rw [Expr.dup_eq hdup] at hpush
        obtain ⟨-, hxwf, hdrop⟩ := vec_index_expr hargs hidx
        obtain ⟨hiabs, hiwf⟩ := instantiate1_refines hbo hxwf hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) args i2 b out1 r
          rfl hiwf hargs (exprsWF_push hout hty hpush) hrec
        refine ⟨?_, hwf⟩
        rw [habs, absExprs_push hpush, hi2v, hdrop, hiabs,
          show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instPisAt, Option.map_map]
        cases ConLeche.Expr.instPisAt ((absExprs args).drop (i.val + 1))
            ((absExpr bo).instantiate1 (absExpr x) 0) with
        | none => simp
        | some q => simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩
      | @proj s i2 x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instPisAt], by simp⟩

/-- `expr_ops::inst_pis_at` refines `Expr.instPisAt` (`ExprOps.lean:1146-1154`):
the `out = []` wrapper. -/
theorem inst_pis_at_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (he : ExprWF e) (hargs : ExprsWF args)
    (h : expr_ops.inst_pis_at args e = ok r) :
    Option.map (fun p => (absExprs p.1, absExpr p.2)) r =
        ConLeche.Expr.instPisAt (absExprs args) (absExpr e) ∧
      (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  rw [expr_ops.inst_pis_at] at h
  obtain ⟨habs, hwf⟩ := inst_pis_at_from_refines _ args 0#usize e _ r rfl he hargs
    exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
  cases ConLeche.Expr.instPisAt (absExprs args) (absExpr e) with
  | none => simp
  | some q => simp

/-- `expr_ops::inst_lams_at_from` refines `Expr.instPisAt`
(`ExprOps.lean:1156-1162`): the domains are accumulated on the way in, so the
lemma carries `absExprs out ++ …`. -/
theorem inst_lams_at_from_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprWF e → ExprsWF args → ExprsWF out →
      expr_ops.inst_lams_at_from args i e out = ok r →
      (Option.map (fun p => (absExprs p.1, absExpr p.2)) r =
        Option.map (fun p => (absExprs out ++ p.1, p.2))
          (ConLeche.Expr.instLamsAt ((absExprs args).drop i.val) (absExpr e))) ∧
      (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i e out r hN he hargs hout h
    rw [expr_ops.inst_lams_at_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr,
        List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.Expr.instLamsAt], fun p hp => by
        simp only [Option.some.injEq] at hp; rw [← hp]; exact ⟨hout, he⟩⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      obtain ⟨a0, rest0, hd⟩ :
          ∃ a0 rest0, (absExprs args).drop i.val = a0 :: rest0 := by
        rcases hh : (absExprs args).drop i.val with _ | ⟨a0, rest0⟩
        · exfalso
          have hz : ((absExprs args).drop i.val).length = 0 := by rw [hh]; rfl
          rw [List.length_drop, absExprs, List.length_map] at hz
          omega
        · exact ⟨a0, rest0, rfl⟩
      cases he with
      | @bvar i2 e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨c, hdup, out1, hpush, x, hidx, b, hinst, i2, hi2, hrec⟩ := h
        rw [Expr.dup_eq hdup] at hpush
        obtain ⟨-, hxwf, hdrop⟩ := vec_index_expr hargs hidx
        obtain ⟨hiabs, hiwf⟩ := instantiate1_refines hbo hxwf hinst
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) args i2 b out1 r
          rfl hiwf hargs (exprsWF_push hout hty hpush) hrec
        refine ⟨?_, hwf⟩
        rw [habs, absExprs_push hpush, hi2v, hdrop, hiabs,
          show ((0#u64 : Std.U64)).val = 0 by scalar_tac]
        simp only [absExpr_mk, absExprKind, ConLeche.Expr.instLamsAt, Option.map_map]
        cases ConLeche.Expr.instLamsAt ((absExprs args).drop (i.val + 1))
            ((absExpr bo).instantiate1 (absExpr x) 0) with
        | none => simp
        | some q => simp
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩
      | @proj s i2 x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hd]
        exact ⟨by simp [ConLeche.Expr.instLamsAt], by simp⟩

/-- `expr_ops::inst_lams_at` refines `Expr.instPisAt` (`ExprOps.lean:1156-1162`):
the `out = []` wrapper. -/
theorem inst_lams_at_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (he : ExprWF e) (hargs : ExprsWF args)
    (h : expr_ops.inst_lams_at args e = ok r) :
    Option.map (fun p => (absExprs p.1, absExpr p.2)) r =
        ConLeche.Expr.instLamsAt (absExprs args) (absExpr e) ∧
      (∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2) := by
  rw [expr_ops.inst_lams_at] at h
  obtain ⟨habs, hwf⟩ := inst_lams_at_from_refines _ args 0#usize e _ r rfl he hargs
    exprsWF_new h
  refine ⟨?_, hwf⟩
  rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero]
  cases ConLeche.Expr.instLamsAt (absExprs args) (absExpr e) with
  | none => simp
  | some q => simp

/-- `expr_ops::inst_spine_from` refines `Expr.instSpine`
(`ExprOps.lean:1217-1225`) at the arguments from `i` on.  The cursor's `t - 1`
is Lean's truncated subtraction, hence `sub_nat` (task #13). -/
theorem inst_spine_from_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (t : Std.U64)
      (e r : expr.Expr),
      args.val.length - i.val = N → ExprWF e → ExprsWF args →
      expr_ops.inst_spine_from args i t e = ok r →
      absExpr r = ConLeche.Expr.instSpine ((absExprs args).drop i.val) t.val (absExpr e) ∧
        ExprWF r := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args i t e r hN he hargs h
    rw [expr_ops.inst_spine_from.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hlen : args.val.length ≤ i.val := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      rw [Expr.dup_eq h, List.drop_eq_nil_of_le (by simpa [absExprs] using hlen)]
      exact ⟨by simp [ConLeche.Expr.instSpine], he⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by
        have := alloc.vec.Vec.len_val args; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨x, hidx, e2, hinst, i2, hi2, t2, ht2, hrec⟩ := h
      obtain ⟨-, hxwf, hdrop⟩ := vec_index_expr hargs hidx
      obtain ⟨hiabs, hiwf⟩ := instantiate1_refines he hxwf hinst
      have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
      have ht2v : t2.val = t.val - 1 := by
        rw [sub_nat_val ht2, show ((1#u64 : Std.U64)).val = 1 by scalar_tac]
      obtain ⟨habs, hwf⟩ := ih (args.val.length - i2.val) (by omega) args i2 t2 e2 r rfl
        hiwf hargs hrec
      refine ⟨?_, hwf⟩
      rw [habs, hi2v, ht2v, hdrop, hiabs]
      simp [ConLeche.Expr.instSpine]

/-- `expr_ops::inst_spine` refines `Expr.instSpine` (`ExprOps.lean:1217-1225`). -/
theorem inst_spine_refines {args : alloc.vec.Vec expr.Expr} {t : Std.U64}
    {e r : expr.Expr} (he : ExprWF e) (hargs : ExprsWF args)
    (h : expr_ops.inst_spine args t e = ok r) :
    absExpr r = ConLeche.Expr.instSpine (absExprs args) t.val (absExpr e) ∧ ExprWF r := by
  rw [expr_ops.inst_spine] at h
  obtain ⟨habs, hwf⟩ := inst_spine_from_refines _ args 0#usize t e r rfl he hargs h
  exact ⟨by rw [habs, show ((0#usize : Std.Usize)).val = 0 by scalar_tac, List.drop_zero], hwf⟩

/-! ## `recRulePlain`

con-leche compares two *lists*: `dom.getAppArgs.take cnP` against
`(List.range cnP).map (fun k => .bvar (mI - 1 - k))`.  The port walks the index
instead (task #13's deviation 6), so `rec_rule_args_eq`'s lemma is the
*pointwise* reading of that equality, and `take_eq_range_map_iff` is the bridge
between the two at `k = 0`. -/

/-- A prefix equals a `range`-map exactly when it agrees pointwise below `n`. -/
theorem take_eq_range_map_iff {α : Type} {l : List α} {n : Nat} {f : Nat → α} :
    l.take n = (List.range n).map f ↔ ∀ j, j < n → l[j]? = some (f j) := by
  constructor
  · intro h j hj
    have hg := congrArg (fun L => L[j]?) h
    simp only [List.getElem?_take, List.getElem?_map, List.getElem?_range, hj,
      if_true] at hg
    simpa using hg
  · intro h
    apply List.ext_getElem?
    intro j
    by_cases hj : j < n
    · simp [hj, h j hj]
    · simp [hj]

/-- `expr_ops::rec_rule_args_eq` refines the list comparison inside
`Expr.recRulePlain` (`ExprOps.lean:1227-1242`), one index at a time: the
arguments from `k` to `cn_p` are the recursor's own leading bound variables. -/
theorem rec_rule_args_eq_refines (N : Nat) :
    ∀ (args : alloc.vec.Vec expr.Expr) (m_i cn_p k : Std.U64) (b : Bool),
      cn_p.val - k.val = N → ExprsWF args →
      expr_ops.rec_rule_args_eq args m_i cn_p k = ok b →
      b = decide (∀ j, k.val ≤ j → j < cn_p.val →
        (absExprs args)[j]? = some (ConLeche.Expr.bvar (m_i.val - 1 - j))) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro args m_i cn_p k b hN hargs h
    rw [expr_ops.rec_rule_args_eq.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : cn_p.val ≤ k.val := by scalar_tac
      rw [← Result.ok_injective h]
      refine (decide_eq_true ?_).symm
      intro j hj1 hj2
      omega
    · rename_i hge
      have hlt : k.val < cn_p.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨i1, hi1, h⟩ := h
      have hi1v : i1.val = args.val.length := by
        simp only [lift_eq, Result.ok.injEq] at hi1
        rw [← hi1, usize_cast_u64_val, alloc.vec.Vec.len_val]
      split at h
      · rename_i hge2
        have hklen : args.val.length ≤ k.val := by scalar_tac
        rw [← Result.ok_injective h]
        refine (decide_eq_false ?_).symm
        intro hall
        have := hall k.val (le_refl _) hlt
        rw [absExprs, List.getElem?_map,
          List.getElem?_eq_none (by omega)] at this
        simp at this
      · rename_i hge2
        have hklt : k.val < args.val.length := by scalar_tac
        simp only [bind_eq_ok_iff] at h
        obtain ⟨i2, hi2, i3, hi3, want, hwant, i4, hi4, x, hidx, b1, hbeq, h⟩ := h
        have hi3v : i3.val = m_i.val - 1 - k.val := by
          rw [sub_nat_val hi3, sub_nat_val hi2,
            show ((1#u64 : Std.U64)).val = 1 by scalar_tac]
        have hi4v : i4.val = k.val := by
          simp only [lift_eq, Result.ok.injEq] at hi4
          have hlen : args.val.length ≤ Std.Usize.max := by scalar_tac
          rw [← hi4, u64_cast_usize_val (by omega)]
        obtain ⟨-, hxwf, -⟩ := vec_index_expr hargs hidx
        have hxg : (absExprs args)[k.val]? = some (absExpr x) := by
          have hg := vec_index_getElem? hidx
          rw [hi4v] at hg
          rw [absExprs, List.getElem?_map, hg]
          rfl
        have hb1 : b1 = decide (absExpr x = ConLeche.Expr.bvar (m_i.val - 1 - k.val)) := by
          rw [Expr.beq_refines hxwf (Expr.bvar_wf hwant) hbeq,
            Expr.bvar_refines hwant, hi3v]
        cases hc : b1 with
        | false =>
          rw [hc] at h
          simp only [Bool.false_eq_true, if_false] at h
          rw [← Result.ok_injective h]
          refine (decide_eq_false ?_).symm
          intro hall
          have hk := hall k.val (le_refl _) hlt
          rw [hxg, Option.some.injEq] at hk
          rw [hc] at hb1
          exact (of_decide_eq_false hb1.symm) hk
        | true =>
          rw [hc] at h
          simp only [if_true, bind_eq_ok_iff] at h
          obtain ⟨i5, hi5, hrec⟩ := h
          have hi5v : i5.val = k.val + 1 := HashMap.uscalar_add_eq hi5
          rw [ih (cn_p.val - i5.val) (by omega) args m_i cn_p i5 b rfl hargs hrec, hi5v]
          rw [hc] at hb1
          have hkeq : absExpr x = ConLeche.Expr.bvar (m_i.val - 1 - k.val) :=
            of_decide_eq_true hb1.symm
          refine decide_eq_decide.2 ⟨?_, ?_⟩
          · intro hall j hj1 hj2
            rcases Nat.eq_or_lt_of_le hj1 with hj | hj
            · rw [← hj, hxg, hkeq]
            · exact hall j (by omega) hj2
          · intro hall j hj1 hj2
            exact hall j (by omega) hj2

/-- `==` on a `List Expr` is `decide (· = ·)`: con-leche's `Expr` has a
`LawfulBEq` instance (`Expr.lean:983-988`). -/
theorem list_beq_decide (l m : List ConLeche.Expr) : (l == m) = decide (l = m) := by
  by_cases hlm : l = m <;> simp [hlm]

/-- `expr_ops::rec_rule_plain` refines `Expr.recRulePlain`
(`ExprOps.lean:1227-1242`).  The `&&` cascade is an `if` nest in the port
(task #3's pattern 9) and the list comparison is the index walk above. -/
theorem rec_rule_plain_refines {rec_ty : expr.Expr} {m_i r_p cn_p : Std.U64} {b : Bool}
    (he : ExprWF rec_ty)
    (h : expr_ops.rec_rule_plain rec_ty m_i r_p cn_p = ok b) :
    b = ConLeche.Expr.recRulePlain (absExpr rec_ty) m_i.val r_p.val cn_p.val := by
  rw [expr_ops.rec_rule_plain] at h
  rw [ConLeche.Expr.recRulePlain]
  split at h
  · rename_i hle1
    have hle1' : cn_p.val ≤ r_p.val := by scalar_tac
    split at h
    · rename_i hle2
      have hle2' : r_p.val ≤ m_i.val := by scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨o, hsp, h⟩ := h
      obtain ⟨habs, hwf⟩ := strip_pis_refines he hsp
      rw [decide_eq_true hle1', decide_eq_true hle2']
      simp only [Bool.and_self, Bool.true_and]
      cases o with
      | none =>
        simp only [Option.map_none] at habs
        simp only [] at h
        rw [← habs, ← Result.ok_injective h]
      | some q =>
        obtain ⟨bs, t⟩ := q
        obtain ⟨hbs, ht⟩ := hwf (bs, t) rfl
        simp only [Option.map_some] at habs
        rw [← habs]
        simp only [] at h
        clear habs hwf hsp hbs
        cases ht with
        | @bvar i e h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @fvar idx ty e hty h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @sort u e hu h1 =>
          obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.sort_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @mk_const n us e hn hus h1 =>
          obtain ⟨d, bb, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @app f a e hf ha h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @lam ty bo m e hty hbo hm h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @forall_e ty bo m e hty hbo hm h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          obtain ⟨args, hga, hre⟩ := bind_eq_ok_iff.mp h
          obtain ⟨hgabs, hgwf⟩ := get_app_args_refines hty hga
          have hb := rec_rule_args_eq_refines _ args m_i cn_p 0#u64 b rfl hgwf hre
          rw [show ((0#u64 : Std.U64)).val = 0 from by scalar_tac] at hb
          rw [hb]
          simp only [absExpr_mk, absExprKind, list_beq_decide]
          refine decide_eq_decide.2 ?_
          rw [← hgabs, take_eq_range_map_iff]
          exact ⟨fun hall j hj => hall j (Nat.zero_le _) hj,
            fun hall j _ hj => hall j hj⟩
        | @let_e ty w bo e hty hw hbo h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @lit l e hl h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
        | @proj s i x e hs hx h1 =>
          obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
          simp only [arc_deref_eq, bind_tc_ok] at h
          rw [← Result.ok_injective h]; simp
    · rename_i hle2
      have hle2' : ¬ (r_p.val ≤ m_i.val) := by scalar_tac
      rw [decide_eq_false hle2', ← Result.ok_injective h]
      simp
  · rename_i hle1
    have hle1' : ¬ (cn_p.val ≤ r_p.val) := by scalar_tac
    rw [decide_eq_false hle1', ← Result.ok_injective h]
    simp

/-! ## Rebuilding a telescope

`pisToLams` and `replacePiBody` build on the way *out* of the recursion, so
there is no accumulator here (task #13's deviation 5); the induction is on the
binder count with a `cases` on the `ExprWF` derivation inside.  `pisToLams`
emits the parse placeholder `⟨.never⟩` as the binder datum, which is
`prop_when::never` on the port side (`PropWhen.never_refines`). -/

/-- `expr_ops::pis_to_lams` refines `Expr.pisToLams` (`ExprOps.lean:1244-1259`). -/
theorem pis_to_lams_refines (N : Nat) :
    ∀ (k : Std.U64) (e body : expr.Expr) (r : Option expr.Expr),
      k.val = N → ExprWF e → ExprWF body →
      expr_ops.pis_to_lams k e body = ok r →
      (Option.map absExpr r =
        ConLeche.Expr.pisToLams k.val (absExpr e) (absExpr body)) ∧
      (∀ t, r = some t → ExprWF t) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k e body r hN he hbody h
    rw [expr_ops.pis_to_lams.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.pisToLams], fun t ht => by
        simp only [Option.some.injEq] at ht; rw [← ht]; exact hbody⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o, hrec, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) i bo body o hiv hbo hbody hrec
        rw [hiv] at habs
        cases o with
        | none =>
          simp only [Option.map_none] at habs
          rw [← Result.ok_injective h, hn]
          refine ⟨?_, by simp⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.pisToLams, ← habs]
          simp
        | some c =>
          obtain ⟨c2, hdup, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨pw, hpw, h⟩ := bind_eq_ok_iff.mp h
          -- task #38: the binder datum goes through `expr::binder_meta`.
          simp only [binder_meta_eq, bind_tc_ok] at h
          obtain ⟨e2, hlam, hr⟩ := bind_eq_ok_iff.mp h
          rw [Expr.dup_eq hdup] at hlam
          simp only [Option.map_some] at habs
          have hwfc : ExprWF c := hwf c rfl
          refine ⟨?_, ?_⟩
          · rw [← Result.ok_injective hr, hn]
            simp only [Option.map_some, absExpr_mk, absExprKind,
              ConLeche.Expr.pisToLams, ← habs, Option.map_some]
            rw [Expr.lam_refines hlam, absBinderMeta, PropWhen.never_refines hpw]
          · intro t ht
            rw [← Result.ok_injective hr] at ht
            simp only [Option.some.injEq] at ht
            rw [← ht]
            exact Expr.lam_wf hty hwfc (PropWhen.never_wf hpw) hlam
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.pisToLams], by simp⟩

/-- `expr_ops::replace_pi_body` refines `Expr.replacePiBody`
(`ExprOps.lean:1261-1267`).  The binder datum is carried over, which is what
con-leche's `⟨m.pw⟩` is. -/
theorem replace_pi_body_refines (N : Nat) :
    ∀ (k : Std.U64) (e b : expr.Expr) (r : Option expr.Expr),
      k.val = N → ExprWF e → ExprWF b →
      expr_ops.replace_pi_body k e b = ok r →
      (Option.map absExpr r =
        ConLeche.Expr.replacePiBody k.val (absExpr e) (absExpr b)) ∧
      (∀ t, r = some t → ExprWF t) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro k e b r hN he hb h
    rw [expr_ops.replace_pi_body.eq_def] at h
    split at h
    · rename_i hk0
      have hkv : k.val = 0 := by rw [hk0]; scalar_tac
      simp only [bind_eq_ok_iff] at h
      obtain ⟨c, hdup, hr⟩ := h
      rw [Expr.dup_eq hdup] at hr
      rw [← Result.ok_injective hr, hkv]
      exact ⟨by simp [ConLeche.Expr.replacePiBody], fun t ht => by
        simp only [Option.some.injEq] at ht; rw [← ht]; exact hb⟩
    · rename_i hk0
      obtain ⟨n, hn⟩ : ∃ n, k.val = n + 1 := by
        have : k.val ≠ 0 := fun hc => hk0 (Std.UScalar.eq_of_val_eq (by rw [hc]; scalar_tac))
        exact ⟨k.val - 1, by omega⟩
      cases he with
      | @bvar i e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b2, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @mk_const n2 us e hn2 hus h1 =>
        obtain ⟨d, b2, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        obtain ⟨i, hi, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨o, hrec, h⟩ := bind_eq_ok_iff.mp h
        have hiv : i.val = n := by rw [HashMap.uscalar_sub_eq hi, hn]; scalar_tac
        obtain ⟨habs, hwf⟩ := ih n (by omega) i bo b o hiv hbo hb hrec
        rw [hiv] at habs
        cases o with
        | none =>
          simp only [Option.map_none] at habs
          rw [← Result.ok_injective h, hn]
          refine ⟨?_, by simp⟩
          simp only [absExpr_mk, absExprKind, ConLeche.Expr.replacePiBody, ← habs]
          simp
        | some c =>
          obtain ⟨c2, hdup, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨bm, hbm, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨e2, hfa, hr⟩ := bind_eq_ok_iff.mp h
          rw [Expr.dup_eq hdup] at hfa
          rw [Expr.binder_meta_dup_eq hbm] at hfa
          simp only [Option.map_some] at habs
          have hwfc : ExprWF c := hwf c rfl
          refine ⟨?_, ?_⟩
          · rw [← Result.ok_injective hr, hn]
            simp only [Option.map_some, absExpr_mk, absExprKind,
              ConLeche.Expr.replacePiBody, ← habs, Option.map_some]
            rw [Expr.forall_e_refines hfa, absBinderMeta]
          · intro t ht
            rw [← Result.ok_injective hr] at ht
            simp only [Option.some.injEq] at ht
            rw [← ht]
            exact Expr.forall_e_wf hty hwfc hm hfa
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩
      | @proj s i x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h, hn]
        exact ⟨by simp [ConLeche.Expr.replacePiBody], by simp⟩

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

/-- The abstracted argument list, one index step on: what the port's `i` and
con-leche's `a :: as` have in common. -/
theorem absExprs_drop_cons_lt {args : alloc.vec.Vec expr.Expr} {i : Nat}
    (hi : i < args.val.length) :
    (absExprs args).drop i = absExpr args.val[i] :: (absExprs args).drop (i + 1) := by
  rw [absExprs, ← List.map_drop, List.drop_eq_getElem_cons hi, List.map_cons,
    List.map_drop]

/-- `Vec::push` preserves well-formedness. -/
theorem ExprsWF_push {out out1 : alloc.vec.Vec expr.Expr} {x : expr.Expr}
    (hout : ExprsWF out) (hx : ExprWF x) (h : alloc.vec.Vec.push out x = ok out1) :
    ExprsWF out1 := by
  intro y hy
  rw [vec_push_val h] at hy
  rcases List.mem_append.1 hy with hy | hy
  · exact hout y hy
  · rw [List.mem_singleton.1 hy]; exact hx

/-- An entry of a well-formed `Vec<Expr>` is well formed. -/
theorem ExprsWF_getElem {args : alloc.vec.Vec expr.Expr} {i : Nat}
    (hargs : ExprsWF args) (hi : i < args.val.length) : ExprWF args.val[i] :=
  hargs _ (List.getElem_mem hi)

/-- `cons_expr`, as the abstraction and the invariant see it. -/
theorem cons_expr_refines {a : expr.Expr} {acc r : alloc.vec.Vec expr.Expr}
    (ha : ExprWF a) (hacc : ExprsWF acc) (h : expr_ops.cons_expr a acc = ok r) :
    absExprs r = absExpr a :: absExprs acc ∧ ExprsWF r := by
  refine ⟨by rw [absExprs, absExprs, cons_expr_val h, List.map_cons], ?_⟩
  intro y hy
  rw [cons_expr_val h] at hy
  rcases List.mem_cons.1 hy with hy | hy
  · rw [hy]; exact ha
  · exact hacc y hy

/-! ## The one-pass walks -/

/-- **`expr_ops::inst_pis_at_f_go` refines `Expr.instPisAtFGo`**
(`ExprOps.lean:1183-1188`): the domains already accumulated in `out` are
prepended to con-leche's answer, and `acc` -- the pending substitutions,
innermost first -- is what each domain and the residual are `instantiateList`ed
with. -/
theorem inst_pis_at_f_go_refines (N : Nat) :
    ∀ (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF acc → ExprsWF args → ExprWF e →
      ExprsWF out → expr_ops.inst_pis_at_f_go acc args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instPisAtFGo (absExprs acc) ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro acc args i e out r hN hacc hargs he hout h
    rw [expr_ops.inst_pis_at_f_go.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hfast, hr⟩ := h
      obtain ⟨habs, hwf⟩ := instantiate_list_fast_refines he hacc hfast
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨?_, ?_⟩
      · rw [Option.map_some, habs, Expr.val_zero, ConLeche.Expr.instPisAtFGo]
        simp
      · intro p hp
        rw [← Option.some.inj hp]
        exact ⟨hout, hwf⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons_lt hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdom, out1, hpush, e2, hidx, acc2, hcons, i2, hi2, hrec⟩ := h
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habsd, hwfd⟩ := instantiate_list_fast_refines hty hacc hdom
        obtain ⟨habsa, hwfa⟩ :=
          cons_expr_refines (ExprsWF_getElem hargs hlt2) hacc hcons
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) acc2 args i2 bo
          out1 r rfl hwfa hargs hbo (ExprsWF_push hout hwfd hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habsa, absExprs_push hpush, habsd, Expr.val_zero]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instPisAtFGo]
        cases ConLeche.Expr.instPisAtFGo (absExpr args.val[i.val] :: absExprs acc)
            ((absExprs args).drop (i.val + 1)) (absExpr bo) with
        | none => rfl
        | some q => simp
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instPisAtFGo], by simp⟩

/-- **`expr_ops::inst_pis_at_f` refines `Expr.instPisAtF`**
(`ExprOps.lean:1191-1194`), *unconditionally*: on `none` the port falls back to
the sequential `inst_pis_at`, exactly as the cited definition does. -/
theorem inst_pis_at_f_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_pis_at_f args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instPisAtF (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_pis_at_f] at h
  obtain ⟨o, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hgo1, hgo2⟩ := inst_pis_at_f_go_refines
    (args.val.length - (0#usize : Std.Usize).val) (alloc.vec.Vec.new expr.Expr) args
    0#usize e (alloc.vec.Vec.new expr.Expr) o rfl (by intro x hx; simp at hx) hargs he
    (by intro x hx; simp at hx) hgo
  rw [show (0#usize : Std.Usize).val = 0 by scalar_tac,
    show absExprs (alloc.vec.Vec.new expr.Expr) = [] from by
      simp [absExprs, alloc.vec.Vec.new]] at hgo1
  simp only [List.drop_zero] at hgo1
  cases o with
  | none =>
    -- the one-pass walk gave up: the port falls back to `inst_pis_at`, and
    -- `instPisAtF`'s own `none` arm falls back to `instPisAt`.
    have hnone : ConLeche.Expr.instPisAtFGo [] (absExprs args) (absExpr e) = none := by
      simpa using hgo1.symm
    rw [ConLeche.Expr.instPisAtF.eq_def, hnone]
    exact inst_pis_at_refines he hargs h
  | some q =>
    have hr : r = some q := (Result.ok_injective h).symm
    subst hr
    cases hc : ConLeche.Expr.instPisAtFGo [] (absExprs args) (absExpr e) with
    | none => rw [hc] at hgo1; simp at hgo1
    | some q' =>
      rw [ConLeche.Expr.instPisAtF.eq_def, hc]
      refine ⟨hgo1.trans ?_, hgo2⟩
      rw [hc]; simp


/-- **`expr_ops::inst_lams_at_f_go` refines `Expr.instLamsAtFGo`**
(`ExprOps.lean:1197-1202`); the `λ` twin of `inst_pis_at_f_go_refines`. -/
theorem inst_lams_at_f_go_refines (N : Nat) :
    ∀ (acc args : alloc.vec.Vec expr.Expr) (i : Std.Usize) (e : expr.Expr)
      (out : alloc.vec.Vec expr.Expr)
      (r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)),
      args.val.length - i.val = N → ExprsWF acc → ExprsWF args → ExprWF e →
      ExprsWF out → expr_ops.inst_lams_at_f_go acc args i e out = ok r →
      r.map (fun p => (absExprs p.1, absExpr p.2)) =
          (ConLeche.Expr.instLamsAtFGo (absExprs acc) ((absExprs args).drop i.val) (absExpr e)).map
            (fun p => (absExprs out ++ p.1, p.2)) ∧
        ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro acc args i e out r hN hacc hargs he hout h
    rw [expr_ops.inst_lams_at_f_go.eq_def] at h
    dsimp only at h
    split at h
    · rename_i hge
      have hle : args.val.length ≤ i.val := by scalar_tac
      have hdrop : (absExprs args).drop i.val = [] := by
        rw [absExprs, ← List.map_drop, List.drop_eq_nil_of_le hle, List.map_nil]
      simp only [bind_eq_ok_iff] at h
      obtain ⟨e1, hfast, hr⟩ := h
      obtain ⟨habs, hwf⟩ := instantiate_list_fast_refines he hacc hfast
      rw [← Result.ok_injective hr, hdrop]
      refine ⟨?_, ?_⟩
      · rw [Option.map_some, habs, Expr.val_zero, ConLeche.Expr.instLamsAtFGo]
        simp
      · intro p hp
        rw [← Option.some.inj hp]
        exact ⟨hout, hwf⟩
    · rename_i hge
      have hlt : i.val < args.val.length := by scalar_tac
      rw [absExprs_drop_cons_lt hlt]
      cases he with
      | @bvar j e h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.bvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @fvar idx ty e hty h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.fvar_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @sort u e hu h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.sort_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @mk_const n us e hn hus h1 =>
        obtain ⟨d, b, -, rfl, -, -, -⟩ := Expr.mk_const_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @app f a e hf ha h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.app_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @lam ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lam_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind, bind_eq_ok_iff] at h
        obtain ⟨e1, hdom, out1, hpush, e2, hidx, acc2, hcons, i2, hi2, hrec⟩ := h
        obtain ⟨hlt2, rfl⟩ := vec_index_val hidx
        obtain ⟨habsd, hwfd⟩ := instantiate_list_fast_refines hty hacc hdom
        obtain ⟨habsa, hwfa⟩ :=
          cons_expr_refines (ExprsWF_getElem hargs hlt2) hacc hcons
        have hi2v : i2.val = i.val + 1 := HashMap.uscalar_add_eq hi2
        obtain ⟨hrec1, hrec2⟩ := ih (args.val.length - i2.val) (by omega) acc2 args i2 bo
          out1 r rfl hwfa hargs hbo (ExprsWF_push hout hwfd hpush) hrec
        refine ⟨?_, hrec2⟩
        rw [hrec1, hi2v, habsa, absExprs_push hpush, habsd, Expr.val_zero]
        simp only [absExpr_mk, absExprKind]
        rw [ConLeche.Expr.instLamsAtFGo]
        cases ConLeche.Expr.instLamsAtFGo (absExpr args.val[i.val] :: absExprs acc)
            ((absExprs args).drop (i.val + 1)) (absExpr bo) with
        | none => rfl
        | some q => simp
      | @forall_e ty bo m e hty hbo hm h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.forall_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @let_e ty w bo e hty hw hbo h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.let_e_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @lit l e hl h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.lit_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩
      | @proj s j x e hs hx h1 =>
        obtain ⟨d, rfl, -, -, -⟩ := Expr.proj_inv h1
        simp only [arc_deref_eq, bind_tc_ok, node_kind] at h
        rw [← Result.ok_injective h]
        exact ⟨by simp [ConLeche.Expr.instLamsAtFGo], by simp⟩

/-- **`expr_ops::inst_lams_at_f` refines `Expr.instLamsAtF`**
(`ExprOps.lean:1205-1208`). -/
theorem inst_lams_at_f_refines {args : alloc.vec.Vec expr.Expr} {e : expr.Expr}
    {r : Option ((alloc.vec.Vec expr.Expr) × expr.Expr)}
    (hargs : ExprsWF args) (he : ExprWF e)
    (h : expr_ops.inst_lams_at_f args e = ok r) :
    r.map (fun p => (absExprs p.1, absExpr p.2)) =
        ConLeche.Expr.instLamsAtF (absExprs args) (absExpr e) ∧
      ∀ p, r = some p → ExprsWF p.1 ∧ ExprWF p.2 := by
  rw [expr_ops.inst_lams_at_f] at h
  obtain ⟨o, hgo, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hgo1, hgo2⟩ := inst_lams_at_f_go_refines
    (args.val.length - (0#usize : Std.Usize).val) (alloc.vec.Vec.new expr.Expr) args
    0#usize e (alloc.vec.Vec.new expr.Expr) o rfl (by intro x hx; simp at hx) hargs he
    (by intro x hx; simp at hx) hgo
  rw [show (0#usize : Std.Usize).val = 0 by scalar_tac,
    show absExprs (alloc.vec.Vec.new expr.Expr) = [] from by
      simp [absExprs, alloc.vec.Vec.new]] at hgo1
  simp only [List.drop_zero] at hgo1
  cases o with
  | none =>
    have hnone : ConLeche.Expr.instLamsAtFGo [] (absExprs args) (absExpr e) = none := by
      simpa using hgo1.symm
    rw [ConLeche.Expr.instLamsAtF.eq_def, hnone]
    exact inst_lams_at_refines he hargs h
  | some q =>
    have hr : r = some q := (Result.ok_injective h).symm
    subst hr
    cases hc : ConLeche.Expr.instLamsAtFGo [] (absExprs args) (absExpr e) with
    | none => rw [hc] at hgo1; simp at hgo1
    | some q' =>
      rw [ConLeche.Expr.instLamsAtF.eq_def, hc]
      refine ⟨hgo1.trans ?_, hgo2⟩
      rw [hc]; simp

end ConRon.Refine.ExprOps
