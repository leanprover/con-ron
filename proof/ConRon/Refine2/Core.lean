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
| `Core/Eqns.lean` | the 109 `partial_fixpoint` unfolding equations of `arena::core`'s two mutual blocks, derived ONCE and cached into one `.olean` (task #97-P5-Arms) | — |
| `Core/Arms.lean` | the tier index, `bodyRel_of_knot : ∀ f, KnotRel f → BodyRel f` and the census of the ≈ 95 helpers under it | **open** |
| `Core/Arms/Sort.lean` | the `view`/tag agreement — the ten-way `EStore_view_tagOf` and the `sort` projection — and `ensure_sort_refines` | all |
| `Core/Arms/Gated.lean` | `BodyRel`'s one twin-only field, `stuckGatedCore` | all |
| `Core/Arms/Loops.lean` | the two loops' second fuel dimension — `whnf_step`/`whnf_loop`/`whnf_body` closed modulo two leaves; the `defeq` triple stated | 6 of 9 |
| `Core/Arms/Batched.lean` | the five batched clauses of tasks #97-P6-9, -11, -12 and -14 | 0 of 5 |

**The tier's one idea** is `KnotRel`: §3.4 forbids the port a record of
closures, so `arena::core` dispatches on a `lane : u32` where the twin picks a
`CoreFnsA` field, and the refinement's job is to make those two the same
thing at every fuel.  Written before any `core` lemma, as task #97-P5-1 asked.
-/
import ConRon.Refine2.Core.Probes
import ConRon.Refine2.Core.KnotRel
import ConRon.Refine2.Core.Induction
import ConRon.Refine2.Core.Entries
import ConRon.Refine2.Core.Eqns
import ConRon.Refine2.Core.Arms
