/-
# `ConRon.Bridge.Core.Walks` — Theorem 1 for the walks that are not knot slots

`Bridge/Core/**` does the six slots of `Arena/Core.lean`'s `coreKnot`; this
tier does everything else in that file (DESIGN `### Task #97-P3-CoreWalks`).

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

So the tier is **133 theorems**: the fifteen at the top of the W column each
sit on three to six more.

## The modules

* `Walks/Frame.lean` — **the foundation**.  `ReadbackFrame`, the per-call
  memo frame without which no walk that reads a name, a level or a
  universe-argument list back can rebuild `CheckOK`, with one constructor
  per readback.
* `Walks/Spec.lean` — the four answer relations a non-slot walk's theorem is
  phrased with (`SimEOp`, `SimOOp`, `SimBOp`, `SimLOp`), each
  taking the pure call already applied to everything but its fuel, with the
  two `Iff.rfl` bridges to `Bridge/Core/Knot.lean`'s `SimE`/`SimV`.
* `Walks/Cached.lean` — the five cached verdict walks: `lvlEq?_spec` and
  `lvlsEq?_spec`, the tier's exemplar, and the three instantiated-constant
  caches (over `ExprOps.instLPFast_spec`).
* `Walks/Guards.lean` — the `defeq` body's cheap scalar tests.
  `isBoolTrue_spec` is five verification conditions, no `ExprOps` callee
  rule, no new denotation, and DESIGN §8.3's "index inequality IS structural
  inequality" cashed twice in one walk.
* `Walks/Mono.lean` — **the fuel merge** (DESIGN §8's
  `### Task #97-P3-CoreWalks` §6.1): one `…_mono` at the record and one
  `…Fueled_mono` at the fuel for every knot-calling walk of con-leche's
  `Kernel/Core.lean` — twenty-two of each, plus `merge2`, the `max`-and-lift
  idiom every caller repeats.  The module mentions no arena
  state at all: it is pure con-leche over `Verify/PairM.lean`'s projections
  and `Verify/Mono.lean`'s `pureFns_mono`.
* `Walks/Proj.lean` — **the projection table**, on `Bridge/Rel.lean`'s
  `denoteProjEntry`: `projTableName_spec`, `IFEnv.findProj?_spec`,
  `IProjEntry.fireOk_spec`, `IProjEntry.typeAt_spec`, `iotaCertsFull_spec`,
  `projCert_spec` and `projCertAt_spec`.
* `Walks/Nat.lean` — **the literal acceleration**: `reduceNat_spec` and the
  six state-only walks under it, which `Arms/Whnf.lean`'s `whnfBody_spec`
  calls.
* `Walks/PropRead.lean` — **the head-symbol prop-ness readers**: Theorem 1
  for the nine functions of
  `Arena/PropRead.lean`, each an equation with con-leche's reader at
  `find? := env.find?`, in published and answer shape, the binder readers
  of con-leche task #342 (`binderDom`, `lamProj?`, `unwrapIdDefs`, `peelPisW`,
  `substPWAt`), then `propIrrel_spec`.
* `Walks/StrLit.lean` — **the `String`-literal guard**:
  `strLitSupported_spec` and its seven stored-shape tests.
* `Walks/StrCtor.lean` — **a string literal's constructor form**:
  `strLitToConstructor_spec` over the `strLitConsSpine` recursion, and
  `strLitToConstructor_WScoped`.
* `Walks/ProjLit.lean` — `projLitToCtor_spec`.
* `Walks/ProjCore.lean` — **the projection rule on a reduced scrutinee**
  (con-leche's `reduceProjCore`): `reduceProjCore_spec` in
  `SimOOp` form, its five pure exits and `reduceProjCoreFueled_mono`; shared
  by `whnfCoreBody`'s `.proj` clause and `lazyDeltaProjReduction`.
* `Walks/Stuck.lean` — **the stuck fallback**: `stuckIrrel_spec` from
  `structEtaCert_spec` (over `etaCtorShape_spec` and
  `structEtaCertWith_spec`), `structUnitCert_spec` and `proofIrrel_spec`
  (both over `reservedBasisNames_spec`).
* `Walks/Eta.lean` — **the structure-η certificate's sub-walks**:
  `projFnName_spec`, `towerSlotsAll_spec`, `recSlotsAll_spec`,
  `structEtaProjCerts_spec`, `etaProjs_spec` (`projNodesGo`/`projAppsGo`).
* `Walks/Owed.lean` — `etaCert`'s pure side and `defEqList` (over
  `Walks/Mono.lean`'s `defEqListFueled_mono`), with the table of where every
  other walk's statement lives and §0's existential-precondition shape, in
  which `reduceNat_spec` and `unfoldDefinition_spec` are stated so that
  `whnfLoop_spec` can call them.

**This module imports none of them** — the rule `Bridge/Core.lean` and
`Bridge/ExprOps.lean` carry, for the reason `lakefile.toml`'s `ConRonBridge`
entry gives.  The library globs `ConRon.Bridge.+`; this file is the index.

## The projection-entry denotation

`Bridge/Rel.lean`'s `denoteProjEntry` gives `Arena/Env.lean`'s `IProjEntry`
its denotation, so that `IProjEntry.typeAt`, `projCert`, `IProjEntry.fireOk`
and the `.proj` arms of `whnfCoreBody` and `inferBody` below their guard can
be stated.  It sits beside the other ten transports, with its `Ext`
transport, its field inversion and the exactness lemma
`denoteProjTable_entry` (*taking the per-field view commutes with the
denotation*); `Walks/Proj.lean` is its user.

Its one caveat is recorded there and in DESIGN: the exactness lemma holds
**in range**, because both `entry` functions read their two indexed columns
with a DEFAULT and the two defaults are unrelated across the denotation.
That the two columns have `numFields` entries is a clause of OUR
environment invariant (`Bridge/StateOK.lean`'s `IProjTableOK`, a field of
`IFEnvOK`) and not of con-leche's `ConstWF`, which is the wrong side of a
B ⇒ A simulation to take an invariant from; `findProj?_spec` reads it off
`hok.ienv.proj`.
-/
