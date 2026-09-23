import ConRon.Arena.Phased

/-!
# `ConRon.Arena.Pooled` — phase B as the binary's pool runs it

**Task #97-P5-POOL.**  A module of its own, beside `Arena/Phased.lean`, so
that it is imported only by the two tiers that state the pool
(`Refine2/Checker/Phased.lean`, `Bridge/Checker/Phased.lean`) and not by the
`ConRon.Arena` aggregator, which half of the proof imports.
-/

namespace ConRon.Arena

open ConLeche

/-! ## The pool, as the twin sees it

The binary's phase B is not one walk but a POOL: the pending records are
shared among workers, and each worker checks the records it claimed, in
order, on ONE state it built with `worker_state` and threads through them.
`PooledAccepts` is that shape on the twin side: phase A accepted, and a
family of record lists — one per worker — covering every pending record,
each accepted by `checkPendingList` from the phase-A state's worker.  It
says nothing about which worker ran which record or about any worker's
history, because nothing downstream needs it: Theorem 1 turns each list's
accept into con-leche's per-record pure accepts, each at its record's own
prefix environment, and those assemble the pure fold whatever the split
(`Bridge/Checker/Phased.lean`'s `Arena.pooledAccepts_bridge`). -/

/-- con-leche: Main.lean:289-316 checkPool — **the pooled fold, accepted**:
phase A (`annotFold`) accepted with environment `fe` and pending records
`pend`, ending in `s'`; and `parts`, one record list per worker, each drawn
from `pend`, together covering it, each accepted by `checkPendingList` from
`s'.worker`.  The twin of the Rust's `PoolAccepts`
(`Refine2/Checker/Phased.lean`). -/
def PooledAccepts (mode : CheckMode) (pins : List INatOpPinSet)
    (ds : Array IDeclaration) (s : AState) (fe : IFEnv) (s' : AState) : Prop :=
  ∃ (n : Nat) (pend : Array PendingCheck) (parts : List (List PendingCheck)),
    annotFold mode pins (0, mkIFEnv IEnv.empty, #[]) ds.toList s
      = .ok (.ok (n, fe, pend), s') ∧
    (∀ pc ∈ pend.toList, ∃ w ∈ parts, pc ∈ w) ∧
    (∀ w ∈ parts, ∀ pc ∈ w, pc ∈ pend.toList) ∧
    (∀ w ∈ parts, ∃ s'', checkPendingList mode fe w s'.worker = .ok (.ok (), s''))

end ConRon.Arena
