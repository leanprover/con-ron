/-
# `ConRon.Refine2.Checker.OleanPool` — Theorem 2 at the check phase of an `--olean` run

An `--olean` read leaves each theorem's value in its file (the record holds a reference,
`.ThmDecl cv v` with `v` a `bvar` whose index is the reference's code), and the binary's
check phase reads it in the theorem's job: `driver::olean_job` (`crates/con-ron/src/
driver.rs`, unverified), con-leche's `oleanJobRun`.  That function is a straight line of
calls into the verified crate, written here as `oleanJobStep`: the reference read off the
record (a `bvar` handle's `view_bvar`), the job's bracket opened (`enter_record`), the value read into the
worker's scratch tier (`records::read_value`, from the worker's `ValueCache`), the record
checked with it in place (`stream_index::record_check`), the bracket closed
(`leave_record`); any other record is `run_job`'s.  Its twin is `Arena/OleanJobs.lean`'s
`oleanJob`, and the pool's accept over it is `PooledOleanAccepts`.
-/
import ConRon.Refine2.Checker.Phased

open Aeneas Aeneas.Std Result
open ConRon.Generated

namespace ConRon.Refine2

open ConRon.Arena

/-- **The driver's `--olean` step closure**, `|tier, w, c, k| driver::olean_job(tier, w,
c, &mode, &ipins, ds, rd, sp, k as u64)`, as the Aeneas model of each call reads it, over
the worker's state and cache.  The file system is the reader's (`fs` at instance `inst`). -/
def oleanJobStep {F : Type} (inst : frontend.olean.files.OleanFs F) (fs : F)
    (tier : arena.store.PersTier) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (rd : frontend.olean.records.OleanRead)
    (sp : alloc.vec.Vec (alloc.vec.Vec Std.U32))
    (w : arena.monad.AState × frontend.olean.records.ValueCache) (k : Nat) :
    Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
      (arena.monad.AState × frontend.olean.records.ValueCache)) :=
  if h : k < 2 ^ UScalarTy.Usize.numBits then
    let ku : Std.U64 := UScalar.cast .U64 (UScalar.ofNatCore (ty := .Usize) k h)
    let plain : Result ((core.result.Result Unit (kernel.core_types.CheckError × Std.U64)) ×
        (arena.monad.AState × frontend.olean.records.ValueCache)) := do
      let (r, st') ← arena.checker.run_job tier w.1 mode pins ds ku
      ok (r, (st', w.2))
    match ds.val[k]? with
    | some (.ThmDecl cv v) => do
      let t ← arena.handle.EIdx.tag v
      let code ← if t = arena.handle.ETAG_BVAR then arena.store.EStore.view_bvar w.1.store tier v
        else ok none
      match code with
      | some code =>
        let st1 ← arena.core.enter_record w.1
        let (r, ar, c) ← frontend.olean.records.read_value inst fs rd.pins tier st1.store sp
          rd.values w.2 code
        match r with
        | .Err e =>
          let st3 ← arena.core.leave_record { st1 with store := ar }
          ok (.Err (e, ku), (st3, c))
        | .Ok e =>
          let cv' ← arena.env.i_constant_val_dup cv
          let (r', st3) ← arena.stream_index.record_check tier { st1 with store := ar } mode
            pins ku (.ThmDecl cv' e)
          let st4 ← arena.core.leave_record st3
          match r' with
          | .Ok () => ok (.Ok (), (st4, c))
          | .Err e => ok (.Err (e, ku), (st4, c))
      | none => plain
    | _ => plain
  else fail .panic

/-- **The driver's `--olean` init closure**, `|| (checker::worker_state(&st.pins),
value_cache_empty())`. -/
def oleanWorkerInit (pins : arena.pins.Pins) :
    Result (arena.monad.AState × frontend.olean.records.ValueCache) := do
  let w ← arena.checker.worker_state pins
  let c ← frontend.olean.records.value_cache_empty
  ok (w, c)

/-- con-leche: ConLeche/Driver/CheckMain.lean:152-170 checkOleansG — **the driver's check
phase on an `--olean` run, accepted**: the index built from the empty one, the tier
frozen, and `parallel_all` over the record positions with the `--olean` closures. -/
def OleanPoolAccepts {F : Type} (inst : frontend.olean.files.OleanFs F) (fs : F)
    (pers : arena.store.PersTier) (st : arena.monad.AState) (mode : kernel.env.CheckMode)
    (pins : alloc.vec.Vec arena.nat_op_pin_set.INatOpPinSet)
    (ds : alloc.vec.Vec arena.env.IDeclaration) (rd : frontend.olean.records.OleanRead)
    (sp : alloc.vec.Vec (alloc.vec.Vec Std.U32))
    (ix : arena.stream_index.IStreamIndex) (st' : arena.monad.AState) : Prop :=
  ∃ (tier : arena.store.PersTier) (est : arena.store.EStore),
    arena.stream_index.build_index pers st ixEmpty ds 0#usize = ok (.Ok ix, st') ∧
    arena.checker.freeze_tier st'.store ix = ok (tier, est) ∧
    ParallelAll ds.length (oleanWorkerInit st'.pins) (oleanJobStep inst fs tier mode pins ds rd sp)

end ConRon.Refine2
