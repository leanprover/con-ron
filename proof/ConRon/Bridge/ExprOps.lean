/-
# `ConRon.Bridge.ExprOps` — Theorem 1 for the `ExprOps` tier

DESIGN §8.2's Theorem 1, one theorem per twin of `Arena/ExprOps.lean`, in
eleven modules grouped by cluster.  **`ExprOps/Inst1.lean` is the exemplar**:
it fixes the statement shape (the `…Spec` record for one level of the
recursion, the fuel induction), the arm step lemmas' shape ("the shape
`mvcgen` actually produces"), the `arm_hyp` tactic and the
`attribute [-grind]` line.  Read it before any of the others.

* `ExprOps/Inst1.lean` — `instantiate1`;
* `ExprOps/Subst.lean` — the bulk substitution,
  the lift, the lower and `instantiate1Lift`;
* `ExprOps/MemoSpecs.lean` — the memo-set specs with the pure function
  INSIDE the relation, which the four rebuilding walks below share;
* `ExprOps/Abs.lean` — `abstract1` and `abstractRange`;
* `ExprOps/Reset.lean` — `resetMeta` and `renameConsts`;
* `ExprOps/InstLP.lean` — the level side: `instantiateLevelParams`, the two
  level memos, and the two `O(1)` derived-bit readers;
* `ExprOps/Walks.lean`, `ExprOps/Ranges.lean`, `ExprOps/Leaves.lean`,
  `ExprOps/Guards.lean` — the `Bool` and `Nat` walks, whose answers are
  representation-free and whose relation is therefore `RelV` with no target
  store at all (which is what makes them the cheapest group);
* `ExprOps/Spine.lean`, `ExprOps/TelescopeF.lean` — the spine and telescope
  operations, most of which take neither fuel nor a memo, and the batched
  telescope peels whose push-order accumulator denotes con-leche's list
  REVERSED.
-/
import ConRon.Bridge.Specs

/-! **This module imports none of them.**  Two modules of the tier cannot sit
in one import closure (see `lakefile.toml`'s `ConRonBridge` entry), so the
library globs `ConRon.Bridge.+` and builds them as siblings; this file is the
index. -/
