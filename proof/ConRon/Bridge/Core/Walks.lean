/-
# `ConRon.Bridge.Core.Walks` — Theorem 1 for the walks that are not knot slots

Task #97-P3-CoreWalks.  `Bridge/Core/**` does the six slots of
`Arena/Core.lean`'s `coreKnot`; this tier does everything else in that file.

## The census (DESIGN §8's `### Task #97-P3-CoreWalks` §1)

`Arena/Core.lean` is 3 757 lines and **190 definitions**:

| class | count | what a bridge theorem for it is |
|---|---:|---|
| **K** knot slots, bodies, loops, entries | 20 | `Bridge/Core/{Knot,Memo,Arms/*,Induction,EnsureSort}.lean` |
| **C** numeric constants | 6 | nothing |
| **P** pin readers | 25 | `Bridge/StateOK.lean`'s `PinsOK` already says it |
| **F** non-monadic | 6 | a plain equation |
| **W** knot-calling walks | **49** | a `BodySpec`-shaped theorem with `KnotSpec` as a hypothesis |
| **S** state-only walks | **84** | a `BodySpec`-shaped theorem without one |

So the tier is **133 theorems**, not the fifteen task #97-P3-Core's §6
named: those fifteen are the top of the W column and each sits on three to
six more.

## The four modules

* `Walks/Frame.lean` — **the foundation**.  `ReadbackFrame`, the per-call
  memo frame task #97-P3-0's §7 listed as owed, without which no walk that
  reads a name, a level or a universe-argument list back can rebuild
  `CheckOK`; plus the three readback bodies copied (the module note says why)
  and their frame specs.  CLOSED.
* `Walks/Spec.lean` — the five answer relations a non-slot walk's theorem is
  phrased with (`SimEOp`, `SimOOp`, `SimBOp`, `SimLOp`, `SimVOp`), each
  taking the pure call already applied to everything but its fuel, with the
  two `Iff.rfl` bridges to `Bridge/Core/Knot.lean`'s `SimE`/`SimV`.  CLOSED.
* `Walks/Cached.lean` — the five cached verdict walks.  **`lvlEq?_spec` and
  `lvlsEq?_spec` are CLOSED** — the first two non-slot walks of
  `Arena/Core.lean` with a theorem — and are the tier's exemplar; the three
  instantiated-constant caches are stated and wait on
  `ExprOps.instLPFast_spec`.
* `Walks/Owed.lean` — **the seventeen statements the round did not reach**,
  each with what it is waiting on written at the site.  `isBoolTrue_spec`
  waits on nothing at all and `defEqList_spec` waits only on the fuel merge
  (DESIGN §8's `### Task #97-P3-CoreWalks` §6.1).

**This module imports none of them** — the rule `Bridge/Core.lean` and
`Bridge/ExprOps.lean` carry, for the reason `lakefile.toml`'s `ConRonBridge`
entry gives.  The library globs `ConRon.Bridge.+`; this file is the index.

## The one thing the tier is missing that is not a proof

`Arena/Env.lean`'s `IProjEntry` has no denotation, so `IProjEntry.typeAt`,
`projCert` and `IProjEntry.fireOk` cannot even be STATED, and neither can the
`.proj` arms of `whnfCoreBody` and `inferBody` below their guard.
`denoteProjEntry` belongs in `Bridge/Rel.lean` beside the other ten
transports, and it should be the next round's first commit.
-/
