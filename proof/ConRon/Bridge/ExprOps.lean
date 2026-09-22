/-
# `ConRon.Bridge.ExprOps` — Theorem 1 for the `ExprOps` tier

DESIGN §8.2's Theorem 1, one theorem per twin of `Arena/ExprOps.lean`, split
into five modules by cluster:

* `ExprOps/Inst1.lean` — `instantiate1`, **the tier's exemplar**: it fixes the
  statement shape, the arm step lemmas' shape, the `arm_hyp` tactic and what
  the tag dispatch costs the proof.  Read it before any of the others.
* `ExprOps/Subst.lean` — the bulk substitution, the lift and the lower.
* `ExprOps/Abs.lean` — abstraction, the metadata reset, the constant rename
  and the level substitution.
* `ExprOps/Walks.lean` — the `Bool` and `Nat` walks, whose answers are
  representation-free and whose relation is therefore `RelV` with no target
  store at all.
* `ExprOps/Spine.lean` — the spine and telescope operations, most of which
  take neither fuel nor a memo (they recurse on a binder count or on an
  argument list) and are the cheapest theorems of the tier.
-/
import ConRon.Bridge.ExprOps.Inst1
