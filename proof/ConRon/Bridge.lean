/-
# `ConRon.Bridge` — Theorem 1: the arena twin (B) against con-leche's pure
checker (A)

DESIGN.md §8.2.  The library root: one module per layer, in dependency
order.

* `Bridge/Peel.lean` — the meta tactic every closer is built on;
* `Bridge/Rel.lean` — the answer relations and the denotation calculus;
* `Bridge/StateOK.lean` — the state invariant and the memo invariants;
* `Bridge/StoreNested.lean`, `Bridge/StoreBind.lean` — the store specs the
  arena's store API (DESIGN `### Task #97a`) does not state
  (`EStore.internName` / `internLevel` / `internLevels`, and `internBind`);
* `Bridge/Specs.lean` — the `@[spec]` theorem of every `Monad.lean`
  primitive;
* `Bridge/SpecsL.lean` — four more `@[spec]` theorems, over the
  `Specs.lean` primitives;
* `Bridge/Axioms.lean` — the trust census (`#print axioms` on every closed
  result);
* `Bridge/ExprOps.lean` — the `ExprOps` tier (Theorem 1, function by
  function);
* `Bridge/Core.lean` — the Core tier: the knot statement, the memo wrappers,
  the per-arm step lemmas and the fuel induction;
* `Bridge/Promote.lean` — the promotion tier: the
  PERSISTENT extension, the `internPersistent` obligations and the
  promotion's exactness;
* `Bridge/Checker.lean` — **the declaration-checker tier and THEOREM 1**:
  `Arena.checkDecl_bridge` and the binary's fold `Arena.installThenCheck_bridge`
  / `Arena.pooledAccepts_bridge` (the capstone is `ConRon/Capstone.lean`);
* `Bridge/Inductives.lean` — the inductive tier:
  `Arena/Inductives/**`'s twins and `indSpec_of_bridge`, which discharges
  the `Bridge/Checker/Hyp.lean` hypothesis `IndSpec` (stated over
  `checkIndRoute`, the `.indDecl` arm past the pin recogniser).  It imports
  `Bridge/Checker/Hyp.lean` and `Bridge/Checker/Names.lean` and **not**
  `Bridge/Checker/Base.lean` or `Bridge/Checker/Fold.lean`, so that the
  checker tier can import it back — which is why
  `reservedBasisNames_run` lives in `Names.lean` and not in `Base.lean`;
* `Bridge/Frontend.lean` — **the frontend tier and the BYTE-LEVEL capstone**:
  the parse-state relation, DESIGN §8.2's parser
  statement `denoteDecls (Arena.parse chunks) = parseChunks chunks`, and
  `Arena.no_False_declaration` with its `_prelude` and `_pipeline` letters.
  **Its bottom sits BELOW the checker tier and its top above it**:
  `Bridge/Frontend/Rel.lean` imports `Bridge/Checker/Inv.lean`
  — `FoldOK`, `denoteDecls` and `denoteDecl_pext`, the only three names the
  bottom of the tier uses — and only `Bridge/Frontend/Capstone.lean` imports
  the whole of `Bridge/Checker.lean`.  That is what lets
  `Bridge/Checker/Pins.lean` (and `Basis.lean`, `DeclVal.lean`, `Base.lean`
  after it) import `Bridge/Frontend/Shared.lean` for the intern exactness the
  pin walks read.
It imports `ConRon.Arena` and con-leche and **nothing else**: no
`ConRon.Refine`, no `ConRon.Generated`, no Aeneas, no Mathlib.  `vcgen`
and `Std.WP` are in core.

Up to and including the `ExprOps` tier the con-leche half is `Kernel/*`
alone.  **The Core and Checker tiers also import con-leche's `Verify/*`**:
the memo wrappers need its six
depth-invariance theorems (`Verify/Deep.lean:3066-3120`) and its six
well-scopedness preservations, the batched clauses of DESIGN §8.6's items
9/11/12 are identified against the chain by con-leche's own lemmas
(`Verify/BetaSpine.lean`, `Verify/BinderLoop.lean`, `Verify/InstList.lean`),
and the Checker tier takes three declarations in three files —
`Verify/BridgeDecl.lean`'s `checkDecl_datF` (`Bridge/Checker/Mono.lean`),
`Verify/EnvBound.lean`'s `mkFEnv_find?_visibleBelow`
(`Bridge/Checker/Split.lean`) and `Verify/EnvWF.lean`'s `EnvWF`
(`Bridge/Checker/Inv.lean`).  **`Model/Fold.lean`'s `checkDeclsPure_sound_of`**
comes in with `Bridge/Frontend/Capstone.lean`'s `ConLeche.MainTheorem` import
and is applied in `ConRon/Capstone.lean`.  Those modules are built in the
con-leche package, so the cost is loading `olean`s, not elaborating.

`ConRonBridge` is its own library (`ConRon` reaches only `Generated`/`Refine`/`Dump`;
the capstone is its own library, `ConRonCapstone`), and both are in `lakefile.toml`'s
`defaultTargets`, so a plain `lake build` — `scripts/gates.sh`'s
`lake-build` step — elaborates the whole tier.  The tier is `sorry`-free.
-/
import ConRon.Bridge.Peel
import ConRon.Bridge.Rel
import ConRon.Bridge.StateOK
import ConRon.Bridge.StoreNested
import ConRon.Bridge.StoreBind
import ConRon.Bridge.Specs
import ConRon.Bridge.SpecsL
import ConRon.Bridge.ExprOps
import ConRon.Bridge.Core
import ConRon.Bridge.Promote
import ConRon.Bridge.Checker
import ConRon.Bridge.Inductives
import ConRon.Bridge.Frontend
import ConRon.Bridge.Axioms
