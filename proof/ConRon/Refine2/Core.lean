/-
# `ConRon.Refine2.Core` — Theorem 2 for `arena::core`

**Task #97-P5-Core.**  The checker core's refinement: `arena::core`'s six knot
entries against `Arena/Core.lean`'s `coreKnot`, `Arena/CoreGated.lean`'s
`coreKnotGated` and `Arena/CoreIO.lean`'s `coreKnotIO`.

| file | what | closed |
|---|---|---|
| `Core/Probes.lean` | the six `Caches` probes and the six capped writes the knot's slots call, and `relOn_size` — the SIZE agreement the capacity test needs and `RelOn` does not carry | all |
| `Core/KnotRel.lean` | `laneKnot` / `laneKnotAt` (the port's `u32` lane and `bool` io flag as the twin's record), `CoreCtx`, and the two relations `KnotRel f` / `BodyRel f` | — |
| `Core/Induction.lean` | `knotRel_zero`, the six `knotRel_succ_*` fields, `knotRel_succ : BodyRel f → KnotRel (f + 1)` and the fuel induction `knot_rel` | all |
| `Core/Entries.lean` | the six fueled entry points, from `KnotRel` — what the Checker tier consumes | all |
| `Core/Arms.lean` | `bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f`, the ten named arm statements, and the census of the 95 helpers under them | **open** |

**The tier's one idea** is `KnotRel`: §3.4 forbids the port a record of
closures, so `arena::core` dispatches on a `lane : u32` where the twin picks a
`CoreFnsA` field, and the refinement's job is to make those two the same
thing at every fuel.  Written before any `core` lemma, as task #97-P5-1 asked.
-/
import ConRon.Refine2.Core.Probes
import ConRon.Refine2.Core.KnotRel
import ConRon.Refine2.Core.Induction
import ConRon.Refine2.Core.Entries
import ConRon.Refine2.Core.Arms
