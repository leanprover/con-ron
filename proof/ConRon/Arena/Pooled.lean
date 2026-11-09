module

public import ConRon.Arena.Checker

@[expose] public section

/-!
# `ConRon.Arena.Pooled` — the check phase as the binary's pool runs it

**Task #97-P5-POOL.**  A module of its own, beside `Arena/Checker.lean`, so
that it is imported only by the two tiers that state the pool
(`Refine2/Checker/Phased.lean`, `Bridge/Checker/Phased.lean`) and not by the
`ConRon.Arena` aggregator, which half of the proof imports.
-/

namespace ConRon.Arena

open ConLeche

/-! ## The pool, as the twin sees it

The binary's check phase is not one walk but a POOL: the jobs (one per record,
`recordJob` at the record's view of the stream's index) are shared among
workers, and each worker runs the jobs it claimed, in increasing order, on ONE
state it built with `worker_state` and threads through them.  `PooledAccepts` is
that shape on the twin side: the index built, and a family of job lists — one per
worker — covering every position, each accepted by `checkJobList` from the
driver's state's worker.  It says nothing about which worker ran which job.  It does say that a worker's
jobs increase: Theorem 1 inducts in fold order, and a job's start state is reached
through the jobs its worker ran before it, whose specifications need the fold up
to their own, smaller, positions. -/

/-- con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool — **the pooled
-- con-leche: CHANGED since 501589f5 — re-port, re-test, re-prove Pooled.PooledAccepts_bridge, then delete this line
check, accepted**: the index of `ds` built from `s`, ending in `s'`; and `parts`,
one job list per worker, each drawn from the positions of `ds`, together covering
them, each strictly increasing (the pool claims off one monotone counter), each accepted by `checkJobList` from `s'.worker`.  The twin of the Rust's
`PoolAccepts` (`Refine2/Checker/Phased.lean`). -/
def PooledAccepts (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) (s : AState) (I : IStreamIndex) (s' : AState) : Prop :=
  ∃ (parts : List (List Nat)),
    buildIndex ds s = .ok (.ok I, s') ∧
    (∀ t < ds.size, ∃ w ∈ parts, t ∈ w) ∧
    (∀ w ∈ parts, ∀ t ∈ w, t < ds.size) ∧
    (∀ w ∈ parts, w.Pairwise (· < ·)) ∧
    (∀ w ∈ parts, ∃ s'', checkJobList mode pins I ds w s'.worker = .ok (.ok (), s''))

end ConRon.Arena
