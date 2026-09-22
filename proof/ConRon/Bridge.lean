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
  function);
* `Bridge/Promote.lean` — the promotion tier (task #97-P3-Checker): the
  PERSISTENT extension, the `internPersistent` obligations and the
  promotion's exactness;
* `Bridge/Checker.lean` — **the declaration-checker tier and THEOREM 1**:
  `Arena.checkDecl_bridge`, `Arena.checkDeclsPure_bridge` and the capstone
  `Arena.model_exists`.

It imports `ConRon.Arena` and con-leche and **nothing else**: no
`ConRon.Refine`, no `ConRon.Generated`, no Aeneas, no Mathlib.  `mvcgen`
comes from `Std.Tactic.Do`, which is in core.

Task #97-P3-0's rule was con-leche's `Kernel/*` only; task #97-P3-Checker
widens it by three modules, each in ONE file and each for one declaration:
`ConLeche.Verify.BridgeDecl` (`checkDecl_datF`, in `Bridge/Checker/Mono.lean`),
`ConLeche.Verify.EnvBound` (`mkFEnv_find?_visibleBelow`, in
`Bridge/Checker/Split.lean`) and `ConLeche.Model.Fold`
(`checkDeclsPure_sound_of`, in `Bridge/Checker/Capstone.lean` — the capstone
cannot be stated without it).  All three are prebuilt in con-leche's `.lake`,
so none of them costs elaboration here.

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
import ConRon.Bridge.Promote
import ConRon.Bridge.Checker
import ConRon.Bridge.Axioms
