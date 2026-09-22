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
* `Bridge/Core.lean` — the Core tier: the knot statement, the memo wrappers,
  the per-arm step lemmas and the fuel induction (task #97-P3-Core);
* `Bridge/Promote.lean` — the promotion tier (task #97-P3-Checker): the
  PERSISTENT extension, the `internPersistent` obligations and the
  promotion's exactness;
* `Bridge/Checker.lean` — **the declaration-checker tier and THEOREM 1**:
  `Arena.checkDecl_bridge`, `Arena.checkDeclsPure_bridge` and the capstone
  `Arena.model_exists`;
* `Bridge/Frontend.lean` — **the frontend tier and the BYTE-LEVEL capstone**
  (task #97-P3-Frontend): the parse-state relation, DESIGN §8.2's parser
  statement `denoteDecls (Arena.parse chunks) = parseChunks chunks`, and
  `Arena.no_False_declaration` with its `_prelude` and `_pipeline` letters.
It imports `ConRon.Arena` and con-leche and **nothing else**: no
`ConRon.Refine`, no `ConRon.Generated`, no Aeneas, no Mathlib.  `mvcgen`
comes from `Std.Tactic.Do`, which is in core.

Up to and including the `ExprOps` tier the con-leche half is `Kernel/*`
alone.  **The Core and Checker tiers also import con-leche's `Verify/*`**
(tasks #97-P3-Core and #97-P3-Checker): the memo wrappers need its six
depth-invariance theorems (`Verify/Deep.lean:3066-3120`) and its six
well-scopedness preservations, the batched clauses of DESIGN §8.6's items
9/11/12 are identified against the chain by con-leche's own lemmas
(`Verify/BetaSpine.lean`, `Verify/BinderLoop.lean`, `Verify/InstList.lean`),
and the Checker tier takes four declarations in four files —
`Verify/BridgeDecl.lean`'s `checkDecl_datF` (`Bridge/Checker/Mono.lean`),
`Verify/EnvBound.lean`'s `mkFEnv_find?_visibleBelow`
(`Bridge/Checker/Split.lean`), `Verify/EnvWF.lean`'s `EnvWF`
(`Bridge/Checker/Inv.lean`) and **`Model/Fold.lean`'s
`checkDeclsPure_sound_of`** (`Bridge/Checker/Capstone.lean` — the capstone
cannot be stated without it).  Those modules are already built in the shared
package, so the cost is loading `olean`s, not elaborating.

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
import ConRon.Bridge.Core
import ConRon.Bridge.Promote
import ConRon.Bridge.Checker
import ConRon.Bridge.Frontend
import ConRon.Bridge.Axioms
