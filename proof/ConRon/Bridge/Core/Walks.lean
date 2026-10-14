/-
# `ConRon.Bridge.Core.Walks` — Theorem 1 for the walks that are not knot slots

`Bridge/Core/**` does the six slots of
`Arena/Core.lean`'s `coreKnot`; this tier does everything else in that file.

## The census (DESIGN §8's `### Task #97-P3-CoreWalks` §1)

`Arena/Core.lean`'s definitions, by what a bridge theorem for each is:

| class | what a bridge theorem for it is |
|---|---|
| **K** knot slots, bodies, loops, entries | `Bridge/Core/{Knot,Memo,Arms/*,Induction,EnsureSort}.lean` |
| **C** numeric constants | nothing |
| **P** pin readers | `Bridge/StateOK.lean`'s `PinsOK` already says it |
| **F** non-monadic | a plain equation |
| **W** knot-calling walks | a `BodySpec`-shaped theorem with `KnotSpec` as a hypothesis |
| **S** state-only walks | a `BodySpec`-shaped theorem without one |

## The modules

* `Walks/Frame.lean` — **the foundation**.  `ReadbackFrame`, the per-call
  memo frame without which no walk that reads a name, a level or a
  universe-argument list back can rebuild `CheckOK`; plus the three
  readback bodies (the module note says why) and their frame specs.
* `Walks/Spec.lean` — the answer relations a non-slot walk's theorem is
  phrased with (`SimEOp`, `SimOOp`, `SimBOp`), each taking the pure call
  already applied to everything but its fuel.
* `Walks/Cached.lean` — the five cached verdict walks: `lvlEq?_spec`,
  `lvlsEq?_spec` and the three instantiated-constant caches.
* `Walks/Guards.lean` — the `defeq` body's cheap scalar tests
  (`isBoolTrue_spec`): DESIGN §8.3's "index inequality IS structural
  inequality" cashed twice in one walk.
* `Walks/Mono.lean` — **the fuel merge** (DESIGN §8's `### Task
  #97-P3-CoreWalks` §6.1): one `…_mono` at the record and one `…Fueled_mono`
  at the fuel for every knot-calling walk of con-leche's `Kernel/Core.lean`,
  plus `merge2`.  It mentions no arena state: it is pure con-leche over
  `Verify/PairM.lean`'s projections and `Verify/Mono.lean`'s `pureFns_mono`.
* `Walks/Proj.lean` — **the projection table**, on `Bridge/Rel.lean`'s
  `denoteProjEntry`: `projTableName_spec`, `IFEnv.findProj?_spec`,
  `IProjEntry.fireOk_spec`, `IProjEntry.typeAt_spec`, `iotaCertsFull_spec`,
  `projCert_spec` and `projCertAt_spec`.
* `Walks/Nat.lean` — **the literal acceleration**: `reduceNat_spec` and the
  six state-only walks under it.
* `Walks/PropRead.lean` — **the head-symbol prop-ness readers**: Theorem 1
  for the nine functions of `Arena/PropRead.lean`, each an equation with
  con-leche's reader at `find? := env.find?`, in published and answer
  shape, the binder readers of con-leche task #342 (`binderDom`, `lamProj?`,
  `unwrapIdDefs`, `peelPisW`, `substPWAt`), then `propIrrel_spec`.
* `Walks/StrLit.lean` — **the `String`-literal guard**:
  `strLitSupported_spec` and its seven stored-shape tests.
* `Walks/StrCtor.lean` — **a string literal's constructor form**:
  `strLitToConstructor_spec` over the `strLitConsSpine` recursion, and
  `strLitToConstructor_WScoped`.
* `Walks/ProjLit.lean` — `projLitToCtor_spec` (answer `ProjLitAns`), and the
  projection-table vocabulary (`ProjAns`, `EntryFields`).
* `Walks/ProjCore.lean` — **the projection rule on a reduced scrutinee**
  (con-leche's `reduceProjCore`): `reduceProjCore_spec` in `SimOOp` form,
  the function as one equation (`reduceProjCore_eq`) and
  `reduceProjCoreFueled_mono`; shared by `whnfCoreBody`'s `.proj` clause and
  `lazyDeltaProjReduction`.
* `Walks/Stuck.lean` — **the stuck fallback**: `stuckIrrel_spec` from
  `structEtaCert_specA` (over `etaCtorShape_spec` and
  `structEtaCertWith_spec`), `structUnitCert_specA` and `proofIrrel_specA`.
* `Walks/Eta.lean` — **the structure-η certificate's sub-walks**:
  `towerSlotsAll_spec` and `etaProjs_spec` (`towerSlotsAllGo`/`projNodesGo`).
* `Walks/Owed.lean` — `etaCert`'s pure side and `defEqList` (the induction
  `defEqList_specA`), with the table of where every other walk lives.

**This module imports none of them** — the rule `Bridge/Core.lean` and
`Bridge/ExprOps.lean` carry, for the reason `lakefile.toml`'s `ConRonBridge`
entry gives.  The library globs `ConRon.Bridge.+`; this file is the index.

## The projection-table denotation

`Bridge/Rel.lean`'s `denoteProjEntry` is the denotation of an
`IProjEntry`, beside the other ten transports, with its `Ext` transport,
its field inversion and the exactness lemma `denoteProjTable_entry` (*taking
the per-field view commutes with the denotation*); without it
`IProjEntry.typeAt`, `projCert` and `IProjEntry.fireOk` could not be stated.

Its one caveat: the exactness lemma holds **in range**, because both `entry`
functions read their two indexed columns with a DEFAULT and the two defaults
are unrelated across the denotation.  That the two columns have `numFields`
entries is a clause of OUR environment invariant (`Bridge/StateOK.lean`'s
`IProjTableOK`, a field of `IFEnvOK`) and not of con-leche's `ConstWF`,
which is the wrong side of a B ⇒ A simulation to take an invariant from;
`findProj?_spec` reads it off `hok.ienv.proj`.
-/
