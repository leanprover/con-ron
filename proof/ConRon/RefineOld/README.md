# `ConRon.RefineOld` — the `Expr`-tree checker's refinement proof

**This directory is not in the build.**  `proof/ConRon.lean` does not import
it, and `lakefile.toml`'s `ConRon` library has `roots = ["ConRon"]`, so `lake
build` never elaborates a file here.  Nothing below is checked, and nothing
below should be trusted to still elaborate.

## What it is

Task #97's arena campaign replaced con-ron's checker: the shipping crate's
`kernel/`+`cached/` `Expr`-tree checker is gone, and `crates/con-ron-core` is
now the arena — `arena/` over four interned handle stores, with the parser
going straight into the store (DESIGN.md §8, task #97-SWAP).  These 76 modules
are the refinement proof of the checker that was replaced.  They are stated
about `ConRon.Generated` declarations — `cached.core_c.*`, `cached.state_c.*`,
`kernel.checker*.*`, `kernel.inductives.*`, the `Expr`-tree
`frontend.export_c.*` — that the model no longer has, so they cannot elaborate
against it and there is no cheap way to make them.

**They are kept for two reasons**, both about the proof that replaces them:

1. **The idiom.**  Nine months of Aeneas-facing proof technique is in here and
   nowhere else: `Refine/Abs.lean`'s abstraction discipline as the arms use
   it, the `⦃ ⦄`/`step` versus forward-refinement choice per tier
   (AENEAS_FINDINGS.md §3.3), the fuel-monotonicity and knot arrangements of
   `Core/Statements.lean` and `Core/Knot.lean`, `CheckerBase.lean`'s
   `F`-mirror pairing, `Frontend/Base.lean`'s WF-by-construction vocabulary
   and the `StateDR`/`ChunksR` parse-refinement shape, and the automation
   study in `Automation/Study.lean`.  `CORE_PLAN.md` and `AUTOMATION.md` are
   the plans those files were written to.
2. **Salvage.**  A module here whose SUBJECT survived the swap unchanged can
   be moved back by fixing its imports — that is how the 47 modules still in
   `ConRon/Refine/` were kept, and the line between the two directories is
   "does it mention a deleted declaration", computed once and then checked by
   building.  Anything here that turns out to be salvageable should be moved
   back to `ConRon/Refine/` rather than copied.

## What replaces it

DESIGN.md §8.6's phases **P3** (the store/denotation refinement) and **P5**
(the capstone over `runPipeline`).  Those are stated about the Lean twin
`ConRon.Arena.*` and about the new `ConRon.Generated`, and they are not done:
the arena's capstones are P3/P5's, and `RefineOld/Main.lean`'s — con-ron's
old `check_decls`/pipeline corollaries — went out of the build with the
checker they were about.  `ConRon/Refine/README.md` says what is still in the
build and why.

## The `_refines` ledger restarts

`scripts/progress.py` counts `*_refines` theorems under the roots it knows;
`RefineOld` is not one, so the standing progress report reads the surviving
tier only.  That is the honest number: the ledger is a measure of how much of
**the shipping checker** is proved, and the shipping checker changed.
