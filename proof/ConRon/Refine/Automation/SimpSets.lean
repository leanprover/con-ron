import Lean.Meta.Tactic.Simp.RegisterCommand
/-! # The Rust-side normaliser's simp sets (task #70, Fable)

`Automation/Study.lean`'s normaliser runs `simp only` on the Rust success
hypothesis several times per goal.  A `simp only [thirty names]` re-elaborates
its list at every call (task #70 measured ~25 ms a call); a registered simp
set is elaborated once, at attribute time.  The attributes live here, in a
module of their own, because a `register_simp_attr` cannot be used in the
file that declares it; `Study.lean` populates them.

* `rust_reduce`: what makes the generated body's `match` on a known node
  reduce — the erased pointer operations (`Arc::deref`/`new`/`clone`,
  `ron::ptr::*`, the `dup`s), `lift`, and the node projections of the
  three-type mutual inductives (`Expr._0`, `ExprNode.kind`, …, which Aeneas
  defines by `match`, so `simp`'s own projection reduction does not see them).
* `rust_invert`: `rust_reduce` plus bind inversion (`bind_eq_ok_iff`) and
  the injectivity/pair/`∃`-cleanup lemmas that turn one inverted bind into
  plain equations. -/

register_simp_attr rust_reduce
register_simp_attr rust_invert
