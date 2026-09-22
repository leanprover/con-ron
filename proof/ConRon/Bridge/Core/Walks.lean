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
* `Walks/Guards.lean` — the `defeq` body's cheap scalar tests.
  **`isBoolTrue_spec` is CLOSED**, the tier's third closed walk and the first
  that is not a memo wrapper: five verification conditions, no `ExprOps`
  callee rule, no new denotation, and DESIGN §8.3's "index inequality IS
  structural inequality" cashed twice in one walk.
* `Walks/Mono.lean` — **the fuel merge** (task #97-P3-Core-2, DESIGN §8's
  `### Task #97-P3-CoreWalks` §6.1): one `…_mono` at the record and one
  `…Fueled_mono` at the fuel for every knot-calling walk of con-leche's
  `Kernel/Core.lean` — twenty-two of each, plus `merge2`, the `max`-and-lift
  idiom every caller repeats.  All CLOSED, and the module mentions no arena
  state at all: it is pure con-leche over `Verify/PairM.lean`'s projections
  and `Verify/Mono.lean`'s `pureFns_mono`.
* `Walks/Proj.lean` — **the projection table** (task #97-P3-Core-2), on
  `Bridge/Rel.lean`'s new `denoteProjEntry`: `projTableName_spec`,
  `IFEnv.findProj?_spec` and `IProjEntry.fireOk_spec` CLOSED,
  `IProjEntry.typeAt_spec` and `projCert_spec` stated.  §5's structural gap
  below is closed by it.
* `Walks/Owed.lean` — **the sixteen statements the round did not reach**,
  each with what it is waiting on written at the site.  `defEqList_spec` is
  the nearest and its fuel merge is now IN HAND (`Walks/Mono.lean`'s
  `defEqListFueled_mono`); `reduceNat_spec` and `unfoldDefinition_spec` were
  RESTATED by task #97-P3-Core-2 in the existential-precondition shape
  (§0 of that module) so that `whnfLoop_spec` can call them.

**This module imports none of them** — the rule `Bridge/Core.lean` and
`Bridge/ExprOps.lean` carry, for the reason `lakefile.toml`'s `ConRonBridge`
entry gives.  The library globs `ConRon.Bridge.+`; this file is the index.

## The one thing the tier was missing that is not a proof — CLOSED

`Arena/Env.lean`'s `IProjEntry` had no denotation, so `IProjEntry.typeAt`,
`projCert` and `IProjEntry.fireOk` could not even be STATED, and neither
could the `.proj` arms of `whnfCoreBody` and `inferBody` below their guard.
**Task #97-P3-Core-2 added `denoteProjEntry` to `Bridge/Rel.lean`** beside
the other ten transports, with its `Ext` transport, its field inversion and
the exactness lemma `denoteProjTable_entry` (*taking the per-field view
commutes with the denotation*), and `Walks/Proj.lean` is what it unblocks.

Its one caveat is recorded there and in DESIGN: the exactness lemma holds
**in range**, because both `entry` functions read their two indexed columns
with a DEFAULT and the two defaults are unrelated across the denotation.
That the two columns have `numFields` entries is a clause of OUR
environment invariant (`Bridge/StateOK.lean`'s `IProjTableOK`, a field of
`IFEnvOK`) and not of con-leche's `ConstWF`, which is the wrong side of a
B ⇒ A simulation to take an invariant from; `findProj?_spec` reads it off
`hok.ienv.proj` (task #97-P3-Checker-2).
-/
