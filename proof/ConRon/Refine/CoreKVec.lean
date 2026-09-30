/-
`CORE_PLAN.md` step 4 (task #49), the *plumbing* slice of
`crates/con-ron-core/src/kernel/core_k.rs`: the `Vec`/list helpers that stand
for Lean's free list operations, the two constant substitutions, the fuel-lift
and the four closed fuel budgets.  Cited Lean: `ConLeche/Kernel/Core.lean`
(`liftFueled` `:108`, `Expr.substConst0` `:686`, `Expr.substConstAll` `:694`,
`piResidual` `:862`, `majorToCtor` `:1274-1456`, `iotaRec` `:1682-1795`,
`ProjEntry.typeAt` `:1797`, `whnfCoreLoopFuel` `:1984`, `whnfLoopFuel` `:1994`,
`defeqLoopFuel` `:2640`, `checkFuel` `:2901`).

Twenty-two `pub fn`, in three shapes.

* **The index recursions** (`drop_exprs`, `append_exprs`, `leaf_contains`,
  `fvar_leaves_subset`, `rev_append_exprs`, `rules_find`, `pi_residual`) are
  all in the task-#5 shape — a `∀`-quantified statement over `len - i = N` and
  strong induction on `N`, `ExprOps.exprs_copy_upto_val` being the model.  The
  seven `*_from` twins carry the accumulator (`out ++ …`, task #13's deviation
  3: a `Vec` has no shared tail), and the wrapper is two lines.
* **The two substitutions** are plain `ExprWF` inductions: `subst_const0`
  recurses only through `app`, `subst_const_all` through every rebuilding kind,
  exactly as the cited `Expr.substConst0`/`Expr.substConstAll` do.
* **The five one-liners** (`lift_fueled` and the four budgets) are `rfl` modulo
  unfolding the cited `@[irreducible] def`s.

Three things cost thought.

1. `leaf_contains`'s `BEq (Nat × Expr)` is `Nat` equality *and* `Expr.beq`, so
   exactness of the `List.contains` needs `ExprWF` on both the probe and every
   stored leaf — hence the `ExprOps.LeavesWF` hypothesis, and `vec_index_leaf`
   below is `ExprOps.vec_index_expr`'s twin for `Vec<(u64, Expr)>`.
2. `rules_find` returns the *position*, so its lemma states both halves of the
   cited `rules.find? (fun r' => r'.ctor == cj)`: the index is `List.findIdx?`
   and reading the list at it is `List.find?`.  The `findIdx?` step needs the
   returned index to be at or past the cursor, which is therefore a third
   conjunct of the induction.
3. `rev_append_exprs` counts *down* (`targs[k-1]`, `targs[k-2]`, …), so its
   invariant is `out ++ (targs.take k).reverse` under `k ≤ targs.length`; the
   call site's `k = targs.len()` is the wrapper, `out ++ targs.reverse`.
-/
import ConRon.Refine.CoreKBase
import ConLeche.Kernel.Core

open Aeneas Aeneas.Std Result
open ConRon.Generated ConRon.Generated.kernel

namespace ConRon.Refine.CoreK

-- `absRecRule` lives in `BasisTables.lean`'s `T22` section, which `CoreKBase`
-- opens only locally (it goes away with task #46's merge).

/-! ## `drop_exprs` — `List.drop` on a `Vec` (`core_k.rs:137`, `:143`) -/

/-! ## `drop_exprs_n` / `take_exprs_n` — `List.drop`/`List.take` at a **`u64`**
count (`core_k.rs:161`, `:166`, `:178`, `:184`)

Task #61.  The counts the ι cone carries (a recursor's parameter count `rP`, a
constructor's `ctorParams`, a major-premise index `mI`) are `u64`s, and `Vec`
indexing is `usize`; the port used to spell the call `take_exprs(xs, n as
usize)`, which Aeneas models as a **truncating** cast (`UScalar.cast .Usize`),
so nothing below 64-bit `usize` was provable and nothing in the cone bounds
`rP`.  DESIGN.md §3.4 rules the cast out, so the count is consumed by the
recursion instead: `i : Usize` walks the `Vec` and `n : U64` counts down, and
no value crosses between the two widths. -/

/-! ## `append_exprs` — `List.append` on a `Vec` (`core_k.rs:155`, `:160`) -/

/-! ## `leaf_contains` and `fvar_leaves_subset` (`core_k.rs:173`-`:199`)

The scope guard's third conjunct of `Core.lean:1274-1456 majorToCtor`,
`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)`.  `absLeaves` and
`LeavesWF` are `Refine/ExprOpsMeta.lean`'s (`fvar_leaves`' abstraction), and
the `BEq (Nat × Expr)` the cited `List.contains` uses is `Nat` equality and
`Expr.beq` — exact only on well-formed nodes, whence the `LeavesWF`/`ExprWF`
hypotheses. -/

/-! ## `expr_singleton` (`core_k.rs:1907`) -/

/-! ## `rev_append_exprs` (`core_k.rs:2351`)

`ConLeche/Kernel/Core.lean:1797-1806 ProjEntry.typeAt`'s `pe :: targs.reverse`,
as the downward index recursion `targs[k-1]`, `targs[k-2]`, …. -/

/-! ## `get_d_expr` (`core_k.rs:2288`)

`Core.lean:1682-1795 iotaRec`'s `args.getD mI (.bvar 0)`; Lean's out-of-range
default is `Inhabited Expr`'s `.bvar 0`, which the port spells
`env::default_expr`. -/

/-! ## `rules_find` (`core_k.rs:2300`)

`Core.lean:1682-1795 iotaRec`'s `rules.find? (fun r' => r'.ctor == cj)`, as an
index recursion returning the position (§3.4 forbids closures).  Both halves
of the cited `find?` are stated: the index is `List.findIdx?`, and the list
read at it is `List.find?`. -/

/-! ## `pi_residual` (`core_k.rs:1881`, `:1887`)

`Core.lean:862-867 piResidual`: peel a `∀`-telescope along an argument list.
Structurally `Expr.instPis`, so the proof is `ExprOps.inst_pis_from_refines`'s. -/

/-! ## The two constant substitutions (`core_k.rs:1705`, `:1723`)

`Core.lean:686-692 Expr.substConst0` and `:694-710 Expr.substConstAll`.  The
cited guard is `c = n ∧ us = []`; the port tests `us.len() == 0 &&
name::beq(c, n)`, which is the same condition (`absLevels us = []` iff the
`Vec` is empty). -/

/-! ## `lift_fueled` (`core_k.rs:328`)

`Core.lean:108-111 liftFueled`, monomorphic at `Option Bool` with `what` baked
in (§3.4).  Stated over the full outcome (task #67): `lift_fueled_refines`
covers both constructors of the returned `core.result.Result`, and
`lift_fueled_err` is its `Err` corollary, which compares the error *kind* only
(DESIGN.md §3.1: messages need not match). -/

/-! ## The four closed fuel budgets

`whnfCoreLoopFuel` (`Core.lean:1984-1992`), `whnfLoopFuel` (`:1994-2001`),
`defeqLoopFuel` (`:2640-2644`) and `checkFuel` (`:2901-2904`) — the first three
`@[irreducible]`, so each lemma unfolds the cited constant by name. -/

end ConRon.Refine.CoreK

/-! ## Axiom census (DESIGN.md §5, the P3 gate)

`subst_const_all_refines` is the file's deepest chain -- the ten-constructor
`ExprWF` induction, `name::beq`'s exactness and five smart constructors -- so it
is the one worth pinning. -/

