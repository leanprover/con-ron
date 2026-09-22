/-
# `ConRon.Bridge` — Theorem 1: the arena twin (B) against con-leche's pure
checker (A)

DESIGN.md §8.2.  The library root: one module per layer, in dependency
order.

* `Bridge/Peel.lean` — the meta tactic every closer is built on;
* `Bridge/Rel.lean` — the answer relations and the denotation calculus;
* `Bridge/StateOK.lean` — the state invariant and the memo invariants;
* `Bridge/StoreNested.lean`, `Bridge/StoreBind.lean`, `Bridge/StoreBM.lean` —
  the three store obligations task #97a's frozen API does not cover
  (`EStore.internName` / `internLevel` / `internLevels`, `internBindI`, and
  the binder-datum store's monotonicity);
* `Bridge/Specs.lean` — the `@[spec]` theorem of every `Monad.lean`
  primitive, and the `bridge_vcs` closer;
* `Bridge/SpecsL.lean` — the four `@[spec]` theorems written after the tier
  had started (they belong in `Specs.lean`);
* `Bridge/Axioms.lean` — the trust census (`#print axioms` on every closed
  result);
* `Bridge/ExprOps.lean` — the `ExprOps` tier (Theorem 1, function by
  function).

It imports `ConRon.Arena` and con-leche's pure tier and **nothing else**: no
`ConRon.Refine`, no `ConRon.Generated`, no Aeneas, no Mathlib.  `mvcgen`
comes from `Std.Tactic.Do`, which is in core.

`ConRonBridge` is deliberately **not** in `lakefile.toml`'s `defaultTargets`
while the tier still carries `sorry`s — the precedent is `ConRonArenaSpike`
(task #97s).  Build it with `lake build ConRonBridge`; promote it to a
default target when the tier is closed.
-/
import ConRon.Bridge.Peel
import ConRon.Bridge.Rel
import ConRon.Bridge.StateOK
import ConRon.Bridge.StoreNested
import ConRon.Bridge.StoreBind
import ConRon.Bridge.StoreBM
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.ExprOps
import ConRon.Bridge.Axioms
