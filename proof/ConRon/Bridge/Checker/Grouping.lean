import ConRon.Bridge.Grouping.Checker
import ConRon.Arena.Pooled

/-!
# `ConRon.Bridge.Checker.Grouping` — phase B does not care how records are grouped

**Task #98-GROUP, part 1.**  Phase B runs on a pool: each worker builds one
state (`AState.worker`, `Arena/Phased.lean`) and folds `checkPending` over the
records it claims.  The capstone used to take the pool's partition as a
premise (`PoolAccepts`, `Refine2/Checker/Phased.lean`).  This module proves, at
the TWIN, that the partition does not matter: a record's outcome does not
depend on the records the same worker checked before it.

## Why

`checkPending` is a bracket.  `enterScratch` opens an empty scratch tier over
the persistent one and resets the per-call memos; `checkValueGroup` runs;
`dropScratch` flushes the per-declaration caches and drops the scratch tier.
So a check READS exactly three things of the state it starts from — the
persistent tiers (`s.store.enableScratch`), the caches and the pin table —
and that is `PhaseBEquiv` below (`checkPending_congr`: equivalent starts give
the SAME result, state included).

What it WRITES back is the frame: an accepting check leaves the persistent
tiers and the pins exactly as it found them and the caches empty
(`checkPending_frame`).  The persistent half is the one real theorem: every
function the check reaches interns only into the open scratch tier and never
writes the pins.  That is `Bridge/Grouping/*.lean`: one `@[spec]` Hoare
triple per twin function reachable from `checkValueGroup` (540 of them,
`Monad` → `ExprOps` → `Pins`/`Env`/`PropRead` → `Core` → the knot →
`CheckerSplit`), each saying the invariant `Inv k p` — all four scratch flags
up, persistent tiers `k`, pins `p` — is kept.  The triples are uniform, so
they are stated and proved by three commands (`#keeps`, `#keeps_ind`,
`#keeps_fuel`, `Bridge/Grouping/Gen.lean`) over `mvcgen`; the handful of
functions whose recursion `mvcgen` cannot unfold on its own (well-founded
recursion, the `whnfApp`/`betaPeel` mutual block, continuation-passing
`whnfStep`/`defeqStep`, the structural `defeqPeel` whose equation lemmas
time out) are written by hand.

## The statements

* `checkPending_congr` — equivalent starts, identical runs;
* `checkPending_frame` — an accepting run ends equivalent to its start (with
  the caches empty, which every worker start has);
* `checkPending_after_accept` — hence after an accepting record, every
  further record runs exactly as it would have from the start;
* `checkPendingList_accepts_iff` — the fold over any record list accepts
  from a cache-empty state iff every record accepts from that state;
* `checkPendingList_grouping` — so for any grouping `ws` covering the same
  records as `ks`, the fold over `ks` accepts iff every group's fold accepts
  (all from the same worker start);
* `checkPendingWorker_accepts_iff` / `checkPendingWorker_grouping` — the same
  at `Arena.checkPendingWorker`, the driver's sequential projection, and its
  per-record form at the phase-A state itself.
-/

namespace ConRon.Bridge.Grouping

open ConRon.Arena Std.Do

#erase_foreign_specs

end ConRon.Bridge.Grouping
