/-
# `ConRon.Bridge.Core` — Theorem 1 for the checker core

DESIGN §8.2's **Theorem 1** at `Arena/Core.lean`'s knot: the six slots of the
arena twin's `coreKnot` refine con-leche's six fueled entry points.  Nine
modules, in the architecture `_tmp/t97/conleche-arena-history.md` §2.3 names
and con-leche built twice — **one walk per twin body, five memo wrapper
steps, one knot induction**:

* `Core/Knot.lean` — the statement (`KnotSpec`), the two answer relations
  (`SimE`, `SimV`), the body-theorem shape (`BodySpec`, `BodySpecV`) and the
  fuel-zero base case;
* `Core/Memo.lean` — the six slots unfolded once, the six cache setters'
  `@[spec]` theorems, the `CacheOK` insert lemmas, the **stuck-tag branch**
  (task #97-P6-7's lever 2, which con-leche's `memoEI` has no counterpart
  for) and **the six memo-wrapper steps**;
* `Core/Arms/{WhnfCore,Whnf,Infer,InferIO,Defeq,Annotate}.lean` — rule 8's
  step-lemma inventory, one per exit of each PURE clause, plus that body's
  `BodySpec` theorem;
* `Core/Induction.lean` — `knot_spec : ∀ f, KnotSpec mode env fe f`,
  `knot_spec_checkFuel` (what the Checker tier consumes) and the tier's
  `#print axioms` census;
* `Core/EnsureSort.lean` — **the seventh entry point**, which is not a
  `coreKnot` slot and which `Bridge/Checker/Hyp.lean`'s `EnsureSortSpec`
  asked for (task #97-P3-CoreWalks).  CLOSED;
* `Core/Walks/**` — **Theorem 1 for the walks of `Arena/Core.lean` that are
  NOT knot slots**, 133 of them by the census in `Core/Walks.lean`: the
  readback frame (`Walks/Frame.lean`), the five answer relations
  (`Walks/Spec.lean`), the five cached verdict walks (`Walks/Cached.lean`,
  two of them CLOSED) and the sixteen statements the round did not reach
  (`Walks/Owed.lean`).

**This module imports none of them** — the same rule
`ConRon/Bridge/ExprOps.lean` carries and for the same reason
(`lakefile.toml`'s `ConRonBridge` entry: two modules of a tier cannot sit in
one import closure when `grind` generates the same `match`-auxiliary for an
`Arena` definition in each).  The library globs `ConRon.Bridge.+` and builds
them as siblings; this file is the index.

## Where the tier stands

Closed: the statement layer, the whole memo layer (all six wrappers), the
stuck-tag branch, **fifty-two per-arm step lemmas** over the six pure bodies,
**the seventh entry point** and **the non-slot walk tier's foundation plus
its first two walks** (task #97-P3-CoreWalks).  Open: the six `…Body_spec`
walks, the four batched-clause carries they wait on, and 131 of the 133
non-slot walks — see DESIGN §8's `### Task #97-P3-Core` and
`### Task #97-P3-CoreWalks` for the tables and the reason at each site.
-/
import ConRon.Bridge.Core.Knot
