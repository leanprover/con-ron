/-
The Rust-side normaliser's two simp sets (task #70's tuned idiom, landed in
the library at task #71).

`Refine/Abs.lean`'s `rust_norm` runs `simp only` on the Rust success hypothesis
several times per goal.  A `simp only [thirty names]` re-elaborates its list at
every call (task #70 measured ~25 ms a call); a registered simp set is
elaborated once, at attribute time.  The attributes live here, in a module of
their own, because a `register_simp_attr` cannot be used in the file that
declares it: `Refine/Abs.lean` imports this one and populates both sets with
the plumbing lemmas it owns, and any later file adds its own (`ExprOps.lean`'s
`binder_meta_eq`, `BasisTables.lean`'s `expr_dup_eq`).

* `rust_reduce`: what makes the generated body's `match` on a known node
  reduce -- the erased pointer operations (`Arc::deref`/`new`/`clone`,
  `ron::ptr::*`, the `dup`s), `lift`, and the node projections of the
  three-type mutual inductives (`Expr._0`, `ExprNode.kind`, ..., which Aeneas
  defines by `match`, so `simp`'s own projection reduction does not see them).
* `rust_invert`: `rust_reduce` plus bind inversion (`bind_eq_ok_iff`) and
  the injectivity/pair/`∃`-cleanup lemmas that turn one inverted bind into
  plain equations.

`Refine/AUTOMATION.md` is the write-up; `Refine/README.md` §"Writing a new
refinement lemma" is the recipe.
-/
import Lean.Meta.Tactic.Simp.RegisterCommand

register_simp_attr rust_reduce
register_simp_attr rust_invert
