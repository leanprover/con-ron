//! `pool` — con-leche's worker map (`CheckerIO.parMapWorkersIO`) and
//! `Driver/CheckPool.lean` over the ARENA: **the check phase on a pool of worker
//! threads** (DESIGN.md §8.3, §8.6's P6 item 6, tasks #97-P6-6b and #98-POOL).
//!
//! Since task #98-POOL the whole module is ONE generic combinator,
//! [`parallel_all`], plus the index-merge and the walk it rests on.  It knows
//! nothing about checking: it is handed a count `n`, a worker count, a state
//! constructor `init` and a per-index `step`, and it answers whether `step`
//! succeeded at every index.  What the check phase plugs into it is the
//! driver's business (`driver::check_decls_driver`):
//!
//! ```text
//! parallel_all(ds.len(), workers,
//!              || checker::worker_state(&st.pins),
//!              |w, k| checker::run_job(&tier, w, mode, pins, ds, k),
//!              <the heartbeat line>)
//! ```
//!
//! — both closures calls into the VERIFIED crate.  The functions are the cited
//! ones: `worker` is `parWorker`, `parallel_all` is `parMapWorkersIO` (and the
//! thread handling of `checkPool`), `merge_results` is `parMapWorkersIO`'s
//! table merge, and `first_failure` is the walk that turns the merged table
//! into a verdict (`collect`).  The observable contract is con-leche's worker
//! map's: one element per claim off one shared counter, a worker's state going
//! through its own elements in claim order, a failure lowering the shared limit,
//! the results merged by index, and the first failure in the list's order the
//! answer.  Two deviations: `init` takes no worker index (no state here needs
//! it), and a worker that panics is `Panicked` where con-leche's `IO` error
//! restarts the worker's state at `init` — both outside an accepting run.
//!
//! **Threads live here and never in `con-ron-core`** (DESIGN.md §8.5): the
//! verified crate is a pure state-threading computation and knows nothing of
//! this module.
//!
//! ## What a worker is, in the check phase
//!
//! §8.3 has said since P1 what the check phase is: "the persistent tier is
//! immutable, each worker owns a scratch tier — **no atomics anywhere**"
//! (`record_job` is the bracket; nothing writes the persistent tier after the
//! index is built and frozen, and a worker never holds it `&mut`).  So the
//! driver's `init`
//! builds `checker::worker_state(pins)` — an EMPTY store, FROZEN
//! (`EStore::empty_frozen`: every append a scratch append), its own `Memos`
//! and `Caches`, and a COPY of
//! the driver's `Pins` — and its `step` borrows the frozen `&PersTier`, which
//! holds the stream's index.  A job reads it through an empty layer of its own
//! at its record's view and pushes into that layer.  So a worker costs no
//! environment copy at all.
//!
//! ## THE TRUSTED CLAIM, and the whole of it
//!
//! **If `parallel_all(n, workers, init, step, after)` returns `Ok(())`, then
//! every index in `0..n` was claimed by some worker; each worker built its
//! state with `init()` exactly once and folded `step` over the indices it
//! claimed, in claim order, which is increasing; and every one of those
//! `step` calls returned `Ok(())`** — at every worker count.  That is
//! `ParallelAll` in `proof/ConRon/Refine2/Checker/Phased.lean` (task
//! #98-POOL; the increasing order added at task #143), and it is a statement
//! about this module's control flow only — nothing about what `init` and
//! `step` compute.  With the driver's closures it is the capstone's pool
//! premise: index lists covering `0..ds.len`, each increasing, and for each
//! list a fold of `run_job` over it from `worker_state pins`, accepting,
//! which the proof relates, worker by worker, to the twin
//! (`pool_accepts_refines`).
//!
//! The claim is weaker than what the code does: the counter below hands each
//! index to exactly ONE worker, but the contract does not promise that — the
//! proof needs coverage and each worker's increasing order, nothing about
//! repetition across workers.  The argument:
//!
//! * **A claim is a `fetch_add` on one counter.**  Each value `0, 1, 2, …` is
//!   handed to exactly one caller, so every index in `0..n` is claimed (by
//!   exactly one worker, in fact).  A worker stops at its first claim `≥ n`.
//! * **A worker's claims increase.**  The counter only grows, so each
//!   `fetch_add` a worker makes returns more than the one before it: the
//!   order a worker steps its indices in is increasing.
//! * **A worker is one fold.**  `worker` calls `init()` once, then for each
//!   claimed index `k` calls `step(&mut st, k)` on that one state — the fold,
//!   in claim order.  `after(&st, k)` sees the state by `&` only.  A claimed
//!   index at or above `limit` is skipped without a call, and on an accepting
//!   run the limit never moves (only a failing step lowers it), so no claimed
//!   index is skipped.
//! * **Merge by index — master's argument.**  A worker hands back each index
//!   it stepped with the step's result; the workers' arrays are merged *by
//!   index* into one table and `first_failure` walks it in index order,
//!   answering `Ok` only if every slot holds `Ok`.  So an accept means every
//!   index was stepped, successfully, by the worker that claimed it, whatever
//!   the timing.  An empty slot is `ParallelError::Missing`, never `Ok`.
//!
//! The failure side is not part of the claim the capstone uses, but the pool
//! keeps master's behaviour there: the walk stops at the first failing index,
//! and the table is complete below it.  con-leche's argument: a worker whose
//! step fails at `f` lowers the shared `limit` to `f`, and a worker skips a
//! claimed index at or above the limit.  Every value the limit ever holds is
//! `n` or a *failing* index, hence at least the first failing index `f`; so an
//! index below `f` is never skipped, and — the counter being monotone — it was
//! claimed before `f` was and is finished by the worker that claimed it.
//! `pool_reports_the_first_failure_at_every_jobs` is the test, at 1, 2, 3, 4
//! and 8 workers on a list whose records 2 and 4 both fail;
//! `pool_is_the_one_worker_walk_at_every_jobs` checks that the check phase's verdict
//! is the one-worker walk's; `parallel_all_partitions_the_indices` checks the
//! claim itself on a state that records its claims.
//!
//! Every access is `Relaxed`: a stale read of `limit` can only be *larger*
//! than the current value, i.e. can only make a worker do work it could have
//! skipped, and the results themselves travel through the `join` at the end
//! of the scope, which is the release/acquire pair.
//!
//! **A worker keeps one state across its indices** (task #97-P6-6b), where
//! master's pool checked each record from a fresh state: the bracket
//! (`enter_record`, `leave_record`) resets everything but capacity, and a
//! fresh state per record measured **+16.4 % instructions on `Init`** (task
//! #97-P5-Driver).  The claim above does not ask what a worker stepped
//! before: the capstone relates every worker's fold to the twin on its own.
//!
//! ## Threads, stacks and the address-space arithmetic
//!
//! The workers are `std::thread::scope`d threads with `STACK_BYTES` (1 GiB)
//! reserved each — which is what lets the closures borrow `&PersTier`,
//! and `&[IDeclaration]` with no `Arc` and no `'static` bound — so a
//! run needs `3x` the checker's resident set **plus 1 GiB of address space per
//! worker** under `ulimit -v`.
//!
//! **A worker the OS refuses is not a failure** (task #98-POOL).  If spawning
//! a worker fails — out of threads, or out of address space for another
//! 1 GiB stack — the pool runs with the workers that did spawn, and if none
//! did, the calling thread is the one worker.  The claim above holds at every
//! worker count, so the verdict does not depend on how many spawned; only the
//! wall time does.  (Found: `--jobs=8` under an 8 GB `ulimit -v` exited 3,
//! and so did the `--jobs=1` baseline lane under its 2.6 GB cap.)  A worker
//! that PANICS is `ParallelError::Panicked`, an internal error, exit 3, never
//! a verdict on the input.

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

use crate::driver::STACK_BYTES;

/// con-leche: none — `checkPool`'s failure cases, with the checker erased
/// Why [`parallel_all`] did not return `Ok(())`.
pub enum ParallelError<E> {
    /// `step(_, k)` returned `Err(e)`, and `k` is the LEAST index whose step
    /// failed — the walk's first failure in index order.
    Step(usize, E),
    /// Index `k` has no result: the pool did not do its job.  An internal
    /// error, never a verdict on the input.
    Missing(usize),
    /// A worker thread panicked.  An internal error, never a verdict.
    Panicked,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:396-419 parWorker
/// **One worker**: build ONE state with `init()`, then claim ONE index off the
/// shared counter, step it on that state, repeat until the counter is past
/// `n`.  An index at or above the shared `limit` is skipped — it is above a
/// known failure and the walk will never ask for it — and a failing step
/// lowers the limit to its index.  One index per claim is con-leche's choice
/// and its reason is the port's: the work is millions of mostly tiny checks
/// with a skewed tail, and the heavy ones sit *close together* in the stream,
/// so claiming singly spreads a cluster of heavy records over the whole pool
/// instead of serialising it inside one claimed range.
///
/// Deviation: the cited `fuel` (`xs.size + 1` claims, Lean's termination
/// device) is a `loop` that returns when its claim is past the end, which is
/// the same bound — every claim advances the counter by exactly one.
fn worker<S, E>(
    n: usize,
    next: &AtomicUsize,
    limit: &AtomicUsize,
    init: &(impl Fn() -> S + Sync),
    step: &(impl Fn(&mut S, usize) -> Result<(), E> + Sync),
    after: &(impl Fn(&S, usize) + Sync),
) -> Vec<(usize, Result<(), E>)> {
    let mut acc: Vec<(usize, Result<(), E>)> = Vec::new();
    let mut st: S = init();
    loop {
        let k = next.fetch_add(1, Ordering::Relaxed);
        if k >= n {
            return acc;
        }
        if k >= limit.load(Ordering::Relaxed) {
            continue;
        }
        let r = step(&mut st, k);
        if r.is_err() {
            limit.fetch_min(k, Ordering::Relaxed);
        }
        acc.push((k, r));
        after(&st, k);
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:421-447 parMapWorkersIO
/// The workers' arrays merged **by index** into one table.  The table is the
/// pool's whole interface to the verdict: which worker produced a result, and
/// when, is recorded nowhere.
pub fn merge_results<E>(
    n: usize,
    results: Vec<Vec<(usize, Result<(), E>)>>,
) -> Vec<Option<Result<(), E>>> {
    let mut tab: Vec<Option<Result<(), E>>> = Vec::with_capacity(n);
    for _ in 0..n {
        tab.push(None);
    }
    for rs in results {
        for (k, r) in rs {
            if k < n {
                tab[k] = Some(r);
            }
        }
    }
    tab
}

/// con-leche: ConLeche/Driver/CheckPool.lean:125-141 collectFrom
/// con-leche: ConLeche/Driver/CheckPool.lean:143-146 collect
/// **The results, walked in index order.**  Slot `k` holds index `k`'s
/// result; the walk stops at the first failure, so its answer is the
/// sequential fold's whatever order the results were produced in.  An empty
/// slot is `ParallelError::Missing` (a pool that did not do its job), never
/// an accept.
pub fn first_failure<E>(tab: Vec<Option<Result<(), E>>>) -> Result<(), ParallelError<E>> {
    for (k, slot) in tab.into_iter().enumerate() {
        match slot {
            Some(Ok(())) => {}
            Some(Err(e)) => return Err(ParallelError::Step(k, e)),
            None => return Err(ParallelError::Missing(k)),
        }
    }
    Ok(())
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:421-447 parMapWorkersIO
/// con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool
/// **`step` at every index of `0..n`, on a pool of `workers` threads** — the
/// module note's trusted claim is this function's contract:
///
/// > If it returns `Ok(())`, every index in `0..n` was claimed by some worker,
/// > each worker built its state with `init()` once and folded `step` over its
/// > claimed indices in claim order, which is increasing, and every step
/// > returned `Ok(())`.
///
/// On a failure it returns the LEAST failing index with its error
/// (`ParallelError::Step`), whatever the timing.  `after(&st, k)` runs on the
/// worker's thread after each step it made, with the worker's state by `&`
/// (the driver's heartbeat); it cannot change an outcome.
///
/// The workers are `std::thread::scope`d, with `STACK_BYTES` of stack each.
/// `workers` is the count the caller has already clamped
/// (`driver::workers_for`: `max(1, min(jobs, n))`); if the OS refuses to
/// spawn one, the pool runs on those it has, and on the calling thread if it
/// has none — the contract holds at every worker count, so the answer does
/// not depend on it.
pub fn parallel_all<S, E: Send>(
    n: usize,
    workers: usize,
    init: impl Fn() -> S + Sync,
    step: impl Fn(&mut S, usize) -> Result<(), E> + Sync,
    after: impl Fn(&S, usize) + Sync,
) -> Result<(), ParallelError<E>> {
    let next = AtomicUsize::new(0);
    let limit = AtomicUsize::new(n);
    let run = || worker(n, &next, &limit, &init, &step, &after);
    let mut results: Vec<Vec<(usize, Result<(), E>)>> = Vec::with_capacity(workers);
    let mut panicked = false;
    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for w in 0..workers {
            let spawned = std::thread::Builder::new()
                .stack_size(STACK_BYTES)
                .name(format!("check-{}", w))
                .spawn_scoped(scope, &run);
            match spawned {
                Ok(h) => handles.push(h),
                // Out of threads, or out of address space for another stack:
                // run on the workers already spawned (the module note).
                Err(_) => break,
            }
        }
        if handles.is_empty() {
            results.push(run());
        }
        for h in handles {
            match h.join() {
                Ok(rs) => results.push(rs),
                Err(_) => panicked = true,
            }
        }
    });
    if panicked {
        return Err(ParallelError::Panicked);
    }
    first_failure(merge_results(n, results))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    use con_ron_core::arena::checker;
    use con_ron_core::arena::env::{IConstantVal, IDeclaration};
    use con_ron_core::arena::monad;
    use con_ron_core::arena::monad::AState;
    use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
    use con_ron_core::arena::pins::Pins;
    use con_ron_core::arena::store::EStore;
    use con_ron_core::arena::store::ENodeView;
    use con_ron_core::arena::store::LNodeView;
    use con_ron_core::arena::store::NNodeView;
    use con_ron_core::arena::store::PersTier;
    use con_ron_core::arena::stream_index;
    use con_ron_core::kernel::core_types::CheckError;
    use con_ron_core::kernel::env::{CheckMode, ReducibilityHint};
    use con_ron_core::ron::hashmap::Dup;
    use crate::driver::PhaseObserver;

    type RecordResult = Result<(), (CheckError, u64)>;

    /// **The check phase as the driver runs it** (`driver::check_decls_driver`'s
    /// `parallel_all` call, with the heartbeat hook the observer asks for).
    fn check_pool<O: PhaseObserver + Send>(
        pers: &PersTier,
        mode: &CheckMode,
        ds: &Vec<IDeclaration>,
        pins: &Pins,
        workers: usize,
        obs: &Mutex<&mut O>,
    ) -> RecordResult {
        let np: Vec<INatOpPinSet> = Vec::new();
        let heartbeat = match obs.lock() {
            Ok(g) => g.wants_check_lines(),
            Err(_) => false,
        };
        let done = AtomicUsize::new(0);
        let r = parallel_all(
            ds.len(),
            workers,
            || checker::worker_state(pins),
            |w: &mut AState, k| checker::run_job(pers, w, mode, &np, ds, k as u64),
            |w: &AState, k| {
                if heartbeat {
                    let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                    if let Ok(mut g) = obs.lock() {
                        g.check_after(pers, &w.store, n, ds.len(), ds, k);
                    }
                }
            },
        );
        crate::driver::pool_verdict(r)
    }

    /// **The contract, generically**: a state that records the indices it
    /// was stepped at.  At every worker count, on accept, the workers' claim
    /// lists partition `0..n`, each is increasing (claim order), each worker
    /// called `init` exactly once, and `after` saw every step.
    #[test]
    fn parallel_all_partitions_the_indices() {
        for n in [0usize, 1, 2, 7, 100, 1000] {
            for workers in [1usize, 2, 3, 4, 8, 16] {
                let inits = AtomicUsize::new(0);
                let afters = AtomicUsize::new(0);
                let finished: Mutex<Vec<Vec<usize>>> = Mutex::new(Vec::new());
                // The state hands its claim list to `finished` when dropped,
                // i.e. when its worker is done.
                struct Rec<'a>(Vec<usize>, &'a Mutex<Vec<Vec<usize>>>);
                impl Drop for Rec<'_> {
                    fn drop(&mut self) {
                        if let Ok(mut g) = self.1.lock() {
                            g.push(std::mem::take(&mut self.0));
                        }
                    }
                }
                let r: Result<(), ParallelError<()>> = parallel_all(
                    n,
                    workers,
                    || {
                        inits.fetch_add(1, Ordering::Relaxed);
                        Rec(Vec::new(), &finished)
                    },
                    |s: &mut Rec, k| {
                        s.0.push(k);
                        Ok(())
                    },
                    |s: &Rec, k| {
                        assert_eq!(s.0.last(), Some(&k));
                        afters.fetch_add(1, Ordering::Relaxed);
                    },
                );
                assert!(r.is_ok(), "n={} workers={}", n, workers);
                let parts = finished.into_inner().unwrap_or_default();
                assert_eq!(parts.len(), inits.load(Ordering::Relaxed));
                assert!(parts.len() >= 1 && parts.len() <= workers);
                let mut all: Vec<usize> = Vec::new();
                for w in &parts {
                    assert!(w.windows(2).all(|p| p[0] < p[1]), "claim order");
                    all.extend(w.iter().copied());
                }
                all.sort();
                assert_eq!(all, (0..n).collect::<Vec<usize>>(), "a partition of 0..n");
                assert_eq!(afters.load(Ordering::Relaxed), n);
            }
        }
    }

    /// A failure is the LEAST failing index, at every worker count.
    #[test]
    fn parallel_all_reports_the_least_failing_index() {
        for workers in [1usize, 2, 3, 4, 8] {
            let r = parallel_all(
                50,
                workers,
                || (),
                |_: &mut (), k| if k % 7 == 3 { Err(k) } else { Ok(()) },
                |_: &(), _| {},
            );
            match r {
                Err(ParallelError::Step(k, e)) => {
                    assert_eq!((k, e), (3, 3), "at {} workers", workers)
                }
                _ => panic!("expected the step failure at 3 ({} workers)", workers),
            }
        }
    }

    /// An observer that prints nothing and wants no check lines — the plain
    /// pooled lane.
    struct Silent;
    impl PhaseObserver for Silent {}

    /// `Result::unwrap` needs `E: Debug`, and `CheckError` deliberately has
    /// none (DESIGN.md §3.4: no `derive(Debug)` on the core types).  This is
    /// the tests' `unwrap`.
    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture's store declined a node"),
        }
    }

    /// The fixture: one store, the records built into it, their index built
    /// and the tier frozen out of it.  A definition whose declared type is
    /// `Sort 1` and whose value is `Sort u` checks iff `u + 1 = 1`, i.e. iff
    /// `u` is `Sort 0` — no other constant is needed for either outcome, which
    /// is the point: the walk is what is under test, not the checker.
    fn fixture(oks: &[bool]) -> (PersTier, Pins, Vec<IDeclaration>) {
        let pers0: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        ok(con_ron_core::arena::pins::intern_reserved_pins(pers0, &mut st));
        let anon = ok(monad::intern_n_node(pers0, &mut st, NNodeView::Anonymous));
        let zero = ok(monad::intern_l_node(pers0, &mut st, LNodeView::Zero));
        let one = ok(monad::intern_l_node(pers0, &mut st, LNodeView::Succ(zero.dup2())));
        let sort0 = ok(monad::intern_e(pers0, &mut st, ENodeView::Sort(zero.dup2())));
        let sort1 = ok(monad::intern_e(pers0, &mut st, ENodeView::Sort(one.dup2())));
        let mut ds: Vec<IDeclaration> = Vec::new();
        for (k, good) in oks.iter().enumerate() {
            let nm = ok(monad::intern_n_node(
                pers0,
                &mut st,
                NNodeView::Num(anon.dup2(), k as u64),
            ));
            ds.push(IDeclaration::DefnDecl(
                IConstantVal {
                    name: nm,
                    level_params: Vec::new(),
                    ty: sort1.dup2(),
                },
                if *good { sort0.dup2() } else { sort1.dup2() },
                ReducibilityHint::Abbrev,
            ));
        }
        let ix = match stream_index::build_index(pers0, &mut st, stream_index::stream_index_empty(), &ds, 0) {
            Ok(ix) => ix,
            Err(_) => panic!("the fixture's index must build"),
        };
        let pins = checker::pins_dup(&st.pins);
        let tier = checker::freeze_tier(&mut st.store, ix);
        (tier, pins, ds)
    }

    /// **The pool's guarantee** (the module note): a list whose records 2 and
    /// 4 both fail reports record 2 — the first failure in FOLD order — at
    /// every worker count, because the results are walked in record order.
    #[test]
    fn pool_reports_the_first_failure_at_every_jobs() {
        let (tier, pins, ds) = fixture(&[true, true, false, true, false, true]);
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8] {
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            match check_pool(&tier, &mode, &ds, &pins, workers, &lock) {
                Ok(()) => panic!(
                    "a list with two failing records must fail ({} workers)",
                    workers
                ),
                Err((_, pos)) => assert_eq!(pos, 2, "at {} workers", workers),
            }
        }
    }

    /// The check phase as a pure walk (a test's own oracle): every record's job
    /// by the verified `checker::run_job`, in fold order, from one worker state.
    fn run_job_list(
        pers: &PersTier,
        st: &mut AState,
        mode: &CheckMode,
        ds: &Vec<IDeclaration>,
        i: usize,
    ) -> Result<(), (CheckError, u64)> {
        let np: Vec<INatOpPinSet> = Vec::new();
        if i >= ds.len() {
            Ok(())
        } else {
            match checker::run_job(pers, st, mode, &np, ds, i as u64) {
                Err(e) => Err(e),
                Ok(()) => run_job_list(pers, st, mode, ds, i + 1),
            }
        }
    }

    /// **The trusted claim, as a test**: at every worker count the pool
    /// returns what the one-worker walk returns — the same verdict, and on a
    /// failure the same fold position.
    #[test]
    fn pool_is_the_one_worker_walk_at_every_jobs() {
        let lists: Vec<Vec<bool>> = vec![
            vec![true, true, false, true, false, true],
            vec![true; 9],
            vec![],
            vec![false, true],
            vec![true, true, true, true, true, false],
        ];
        let mode = CheckMode::Verified;
        for oks in lists {
            let (tier, pins, ds) = fixture(&oks);
            let mut st = checker::worker_state(&pins);
            let seq = run_job_list(&tier, &mut st, &mode, &ds, 0);
            for workers in [1usize, 2, 3, 4, 8] {
                let mut obs = Silent;
                let lock = Mutex::new(&mut obs);
                let pooled = check_pool(&tier, &mode, &ds, &pins, workers, &lock);
                match (&seq, &pooled) {
                    (Ok(()), Ok(())) => {}
                    (Err((_, a)), Err((_, b))) => {
                        assert_eq!(a, b, "{:?} at {} workers", oks, workers)
                    }
                    _ => panic!("{:?} at {} workers: the pool and the walk disagree", oks, workers),
                }
            }
        }
    }

    /// A list every record of which checks is accepted at every worker count,
    /// and every slot of the table is filled (an unfilled one is the internal
    /// error `pool_verdict` reports, so `Ok` IS the completeness assertion).
    #[test]
    fn pool_accepts_a_clean_list_at_every_jobs() {
        let (tier, pins, ds) = fixture(&[true; 9]);
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8, 16] {
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            assert!(
                check_pool(&tier, &mode, &ds, &pins, workers, &lock).is_ok(),
                "at {} workers",
                workers
            );
        }
    }

    /// A record whose name an earlier record took fails as a duplicate at its
    /// own position: the index keeps the first entry, and the later record's
    /// view sees it.
    #[test]
    fn a_repeated_name_fails_at_the_repeat() {
        let (tier, pins, mut ds) = fixture(&[true, true]);
        let d0 = con_ron_core::arena::env::i_declaration_dup(&ds[0]);
        ds.push(d0);
        // the index was built without the repeat, so rebuild it with it
        let mut st = AState::init(EStore::empty());
        let _ = checker::thaw_tier(&mut st.store, tier);
        let ix = match stream_index::build_index(&PersTier::empty(), &mut st, stream_index::stream_index_empty(), &ds, 0) {
            Ok(ix) => ix,
            Err(_) => panic!("the index must build"),
        };
        let tier = checker::freeze_tier(&mut st.store, ix);
        let mut obs = Silent;
        let lock = Mutex::new(&mut obs);
        match check_pool(&tier, &CheckMode::Verified, &ds, &pins, 2, &lock) {
            Ok(()) => panic!("a repeated name is never an accept"),
            Err((e, pos)) => {
                assert_eq!(crate::driver::exit_code(&e), 1);
                assert_eq!(pos, 2);
            }
        }
    }

    /// The empty list: no worker has anything to claim, and the walk accepts.
    #[test]
    fn pool_on_no_records_accepts() {
        let (tier, pins, ds) = fixture(&[]);
        let mut obs = Silent;
        let lock = Mutex::new(&mut obs);
        assert!(check_pool(&tier, &CheckMode::Verified, &ds, &pins, 4, &lock).is_ok());
    }

    /// The merge is by index whatever order the arrays arrive in, and a gap in
    /// the table is the internal error.
    #[test]
    fn merge_is_by_index_and_a_gap_is_internal() {
        let tab = merge_results(3, vec![vec![(2, Ok(())), (0, Ok(()))], vec![(1, Ok(()))]]);
        assert!(crate::driver::pool_verdict(first_failure(tab)).is_ok());
        let gap: Vec<Option<Result<(), (CheckError, u64)>>> =
            merge_results(3, vec![vec![(0, Ok(())), (2, Ok(()))]]);
        match crate::driver::pool_verdict(first_failure(gap)) {
            Ok(()) => panic!("a gap in the table is never an accept"),
            Err((e, pos)) => {
                assert_eq!(crate::driver::exit_code(&e), 3);
                assert_eq!(pos, 1);
            }
        }
    }
}
