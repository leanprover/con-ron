/-
# `ConRon.Bridge` — Theorem 1: the arena twin (B) against con-leche's pure
checker (A)

DESIGN.md §8.2.  The library root: one module per layer, in dependency
order.

* `Bridge/Peel.lean` — the meta tactic every closer is built on;
* `Bridge/Rel.lean` — the answer relations and the denotation calculus;
* `Bridge/StateOK.lean` — the state invariant and the memo invariants;
* `Bridge/Specs.lean` — the `@[spec]` theorem of every `Monad.lean`
  primitive, and the `bridge_vcs` closer;
* `Bridge/ExprOps.lean` — the `ExprOps` tier (Theorem 1, function by
  function).

It imports `ConRon.Arena` and con-leche's pure tier and **nothing else**: no
`ConRon.Refine`, no `ConRon.Generated`, no Aeneas, no Mathlib.  `mvcgen`
comes from `Std.Tactic.Do`, which is in core.
-/
import ConRon.Bridge.Peel
import ConRon.Bridge.Rel
import ConRon.Bridge.StateOK
import ConRon.Bridge.Specs
import ConRon.Bridge.ExprOps
