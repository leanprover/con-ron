module

public import ConRon.Arena.Checker

@[expose] public section

/-!
# `ConRon.Arena.Pooled` — phase B as the binary's pool runs it

**Task #97-P5-POOL.**  A module of its own, beside `Arena/Checker.lean`, so
that it is imported only by the two tiers that state the pool
(`Refine2/Checker/Phased.lean`, `Bridge/Checker/Phased.lean`) and not by the
`ConRon.Arena` aggregator, which half of the proof imports.
-/

namespace ConRon.Arena

open ConLeche

/-! ## The pool, as the twin sees it

The binary's phase B is not one walk but a POOL: the jobs (the pending records'
value checks and the blocks' checked installs, `jobOrder`) are shared among
workers, and each worker runs the jobs it claimed, in order, on ONE state it built
with `worker_state` and threads through them.  `PooledAccepts` is that shape on
the twin side: phase A accepted, and a family of job lists — one per worker —
covering every job, each accepted by `checkJobList` from the phase-A state's
worker.  It says nothing about which worker ran which job or about any worker's
history, because nothing downstream needs it: Theorem 1 turns each list's accept
into con-leche's per-job accepts, each at its job's own environment, and those
assemble the pure fold whatever the split
(`Bridge/Checker/Phased.lean`'s `Arena.pooledAccepts_bridge`). -/

/-- con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool — **the pooled fold, accepted**:
-- con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove Pooled.PooledAccepts_bridge, then delete this line
phase A (`installFold`) accepted with environment `fe`, pending records `pend` and
block jobs `D`, ending in `s'`; and `parts`, one job list per worker, each drawn
from `jobOrder pend D`, together covering it, each accepted by `checkJobList` from
`s'.worker`.  The twin of the Rust's `PoolAccepts`
(`Refine2/Checker/Phased.lean`). -/
def PooledAccepts (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) (s : AState) (fe : IFEnv) (s' : AState) : Prop :=
  ∃ (n : Nat) (pend : Array PendingCheck) (D : Array BlockCheck) (parts : List (List Job)),
    installFold mode pins (0, mkIFEnv IEnv.empty, #[], #[]) ds.toList s
      = .ok (.ok (n, fe, pend, D), s') ∧
    (∀ j ∈ (jobOrder pend D).toList, ∃ w ∈ parts, j ∈ w) ∧
    (∀ w ∈ parts, ∀ j ∈ w, j ∈ (jobOrder pend D).toList) ∧
    (∀ w ∈ parts, ∃ s'', checkJobList mode pins fe pend D w s'.worker = .ok (.ok (), s''))

end ConRon.Arena
