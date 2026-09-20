/-
# The P2s spike (DESIGN.md §8.6, task #97s)

A throw-away library that prices the proof idioms of DESIGN §8's two
theorems before P2b–P2d start at scale.  It is a **separate library root**
(`ConRonArenaSpike`) and is deliberately *not* imported by `ConRon.Arena`:
nothing the checker ships depends on it.

Modules:

* `Spike/Base.lean`   — `AM`, `AState`, the monadic store primitives;
* `Spike/Twins.lean`  — the three subjects and their invariants;
* `Spike/Peel.lean`   — `spike_peel`, twenty lines of meta code;
* `Spike/Specs.lean`  — the `@[spec]`/`@[grind]` layer (experiment A's
  infrastructure, and the template DESIGN §8.6 asks the spike to fix);
* `Spike/ExpA.lean`   — Theorem 1 for subject 1 via `mvcgen`;
* `Spike/ExpA3.lean`  — Theorem 1 for subject 3 (the memo wrapper) via `mvcgen`;
* `Spike/ExpB.lean`   — the same theorem by hand, in con-ron's forward style;
* `Spike/Mini.lean`   — the three-constructor arena for experiments C and D;
* `Spike/Generated/`  — the Aeneas model of `crates/arena-spike`
  (`scripts/extract-spike.sh`);
* `Spike/ExpCD.lean`  — experiments C and D on the mini arena.
-/
import ConRon.Arena.Spike.Base
import ConRon.Arena.Spike.Twins
import ConRon.Arena.Spike.Peel
import ConRon.Arena.Spike.Specs
import ConRon.Arena.Spike.ExpA
import ConRon.Arena.Spike.ExpA3
import ConRon.Arena.Spike.ExpB
import ConRon.Arena.Spike.Mini
import ConRon.Arena.Spike.ExpCD
