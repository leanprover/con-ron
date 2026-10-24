/-
# `ConRon.Bridge.Core` — Theorem 1 for the checker core

DESIGN §8.2's **Theorem 1** at `Arena/Core.lean`'s knot: the slots of the
arena twin's `coreKnot` refine con-leche's fueled entry points (the eager
slot `defeqE` refines the eager tower's `isDefEqCore`).  Nine
modules, in the architecture `_tmp/t97/conleche-arena-history.md` §2.3 names
and con-leche built twice — **one walk per twin body, five memo wrapper
steps, one knot induction**:

* `Core/Knot.lean` — the statement (`KnotSpec`), the two answer relations
  (`SimE`, `SimV`), the body-theorem shape (`BodySpec`, `BodySpecV`) and the
  fuel-zero base case;
* `Core/Memo.lean` — the slots unfolded once, the six cache setters'
  `@[spec]` theorems, the `CacheOK` insert lemmas, the **stuck-tag branch**
  (DESIGN `### Task #97-P6-7`'s lever 2, which con-leche's `memoEI` has no
  counterpart for), **the five memo-wrapper steps** and the eager slot's step
  (`memoDefeqE_step`: the `defeq` wrapper at `mode.toEager` on the eager
  tower's own memos, swapped in and back out);
* `Core/Arms/{WhnfCore,Whnf,Infer,InferIO,Defeq*}.lean` — rule 8's
  step-lemma inventory, one per exit of each PURE clause, plus that body's
  `BodySpec` theorem;
* `Core/Induction.lean` — `knot_spec : ∀ f, KnotSpec mode env fe f`,
  `knot_spec_checkFuel` (what the Checker tier consumes) and the tier's
  `#print axioms` census;
* `Core/EnsureSort.lean` — **the seventh entry point**, which is not a
  `coreKnot` slot and which `Bridge/Checker/Hyp.lean`'s `EnsureSortSpec`
  asks for;
* `Core/Walks/**` — **Theorem 1 for the walks of `Arena/Core.lean` that are
  NOT knot slots**, 133 of them by the census in `Core/Walks.lean`: the
  readback frame (`Walks/Frame.lean`), the three answer relations
  (`Walks/Spec.lean`), the five cached verdict walks (`Walks/Cached.lean`),
  the `defeq` body's cheap tests (`Walks/Guards.lean`), **the fuel merge**
  (`Walks/Mono.lean` — one `…_mono` and one `…Fueled_mono` per knot-calling
  walk of con-leche's `Kernel/Core.lean`), **the projection table**
  (`Walks/Proj.lean` — `findProjAt`, `IFEnv.findProj?_spec` and
  `IProjEntry.fireOk_spec` on `Bridge/Rel.lean`'s `denoteProjEntry`) and the
  sixteen statements (`Walks/Owed.lean`).

**This module imports none of them** — the same rule
`ConRon/Bridge/ExprOps.lean` carries and for the same reason
(`lakefile.toml`'s `ConRonBridge` entry: two modules of a tier cannot sit in
one import closure when `grind` generates the same `match`-auxiliary for an
`Arena` definition in each).  The library globs `ConRon.Bridge.+` and builds
them as siblings; this file is the index.

## Where the tier stands

The tier is sorry-free: the statement layer, the whole memo layer (all six
wrappers), the stuck-tag branch, the per-arm step lemmas over the six pure
bodies, the six `…Body_spec` walks and the batched-clause carries under them,
**the seventh entry point**, **the whole fuel merge** and all 133 non-slot
walks — see DESIGN §8's `### Task #97-P3-Core`, `### Task #97-P3-CoreWalks`
and `### Task #97-P3-Core-2` for the tables.
-/
import ConRon.Bridge.Core.Knot
