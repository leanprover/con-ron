//! `pool` — con-leche's `Main.lean:193-316` over the ARENA: **phase B on a
//! pool of worker threads** (DESIGN.md §8.3, §8.6's P6 item 6, tasks
//! #97-P6-6b and #98-POOL).
//!
//! Since task #98-POOL the whole module is ONE generic combinator,
//! [`parallel_all`], plus the index-merge and the walk it rests on.  It knows
//! nothing about checking: it is handed a count `n`, a worker count, a state
//! constructor `init` and a per-index `step`, and it answers whether `step`
//! succeeded at every index.  What phase B plugs into it is the driver's
//! business (`driver::check_decls_driver`):
//!
//! ```text
//! parallel_all(pend.len(), workers,
//!              || checker::worker_state(&st.pins),
//!              |w, k| checker::check_pending(&tier, w, mode, &fe, &pend[k]),
//!              <the heartbeat line>)
//! ```
//!
//! — both closures calls into the VERIFIED crate.  The functions are the cited
//! ones: `worker` is `checkWorker` with `checkOne` inlined
//! (`Main.lean:240-278`), `parallel_all` is `checkPool` (`:289-316`),
//! `merge_results` is `mergeResults` (`:280-287`) and `first_failure` is the
//! walk that turns the merged table into a verdict (`collectChecks`,
//! `ConLeche/Cached/Installed.lean:392-416`).
//!
//! **Threads live here and never in `con-ron-core`** (DESIGN.md §8.5): the
//! verified crate is a pure state-threading computation and knows nothing of
//! this module.
//!
//! ## What a worker is, in phase B
//!
//! §8.3 has said since P1 what phase B is: "the persistent tier is immutable
//! in phase B, each worker owns a scratch tier — **no atomics anywhere**",
//! and task #97-P6-6 verified it in the code (`check_pending` is the bracket;
//! the persistent interns' only caller is phase A's `arena::promote`, which
//! writes a `&mut PersTier` a worker never holds).  So the driver's `init`
//! builds `checker::worker_state(pins)` — an EMPTY store, FROZEN
//! (`EStore::empty_frozen`: every append a scratch append), its own `Memos`
//! and `Caches`, and a COPY of
//! the driver's `Pins` — and its `step` borrows the frozen `&PersTier` and
//! the installed `&IFEnv` (by reference: `check_pending` takes the record's
//! prefix bound as a scalar, `pc.vis`, so a worker costs no environment copy
//! at all — task #97-P6-6b).
//!
//! ## THE TRUSTED CLAIM, and the whole of it
//!
//! **If `parallel_all(n, workers, init, step, after)` returns `Ok(())`, then
//! every index in `0..n` was claimed by some worker; each worker built its
//! state with `init()` exactly once and folded `step` over the indices it
//! claimed, in claim order; and every one of those `step` calls returned
//! `Ok(())`** — at every worker count.  That is `ParallelAll` in
//! `proof/ConRon/Refine2/Checker/Phased.lean` (task #98-POOL), and it is a
//! statement about this module's control flow only — nothing about what
//! `init` and `step` compute.  With the driver's closures it is the
//! capstone's pool premise `h8` (task #98-H8 states it inline: index lists
//! `ws` covering `0..pend.len`, and for each `w` in `ws` a `foldlM` of
//! `check_pending` over `w` from `worker_state pins`, accepting), which the
//! proof relates, worker by worker, to the twin (`PoolAccepts.toParts`,
//! `pool_accepts_refines`).
//!
//! The claim is deliberately weaker than what the code does (task #98-H8):
//! the counter below hands each index to exactly ONE worker and a worker's
//! claims INCREASE, but the contract promises neither — the proof needs only
//! coverage, since each record is checked against its own prefix environment
//! and the twin's grouping theorem (`checkPendingList_grouping`) holds for any
//! order, any split and any repetition.  The argument:
//!
//! * **A claim is a `fetch_add` on one counter.**  Each value `0, 1, 2, …` is
//!   handed to exactly one caller, so every index in `0..n` is claimed (by
//!   exactly one worker, in fact).  A worker stops at its first claim `≥ n`.
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
//! `pool_is_check_pending_worker_at_every_jobs` checks that phase B's verdict
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
//! (`enter_scratch`, `drop_scratch`) resets everything but capacity, and a
//! fresh state per record measured **+16.4 % instructions on `Init`** (task
//! #97-P5-Driver).  The claim above does not ask what a worker stepped
//! before: the capstone relates every worker's fold to the twin on its own.
//!
//! ## Threads, stacks and the address-space arithmetic
//!
//! The workers are `std::thread::scope`d threads with `STACK_BYTES` (1 GiB)
//! reserved each — which is what lets the closures borrow `&PersTier`,
//! `&IFEnv` and `&[PendingCheck]` with no `Arc` and no `'static` bound — so a
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

/// con-leche: Main.lean:262-278 checkWorker
/// con-leche: Main.lean:240-260 checkOne
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
/// Deviation: the cited `fuel` (`pend.size + 1` claims, Lean's termination
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

/// con-leche: Main.lean:280-287 mergeResults
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

/// con-leche: ConLeche/Cached/Installed.lean:392-416 collectChecks
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

/// con-leche: Main.lean:289-316 checkPool
/// **`step` at every index of `0..n`, on a pool of `workers` threads** — the
/// module note's trusted claim is this function's contract:
///
/// > If it returns `Ok(())`, every index in `0..n` was claimed by exactly one
/// > worker, each worker built its state with `init()` once and folded `step`
/// > over its claimed indices in claim order (increasing), and every step
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
    use con_ron_core::arena::checker::PendingCheck;
    use con_ron_core::arena::env::IFEnv;
    use con_ron_core::arena::monad::AState;
    use con_ron_core::arena::pins::Pins;
    use con_ron_core::arena::store::PersTier;
    use con_ron_core::kernel::core_types::CheckError;
    use con_ron_core::kernel::env::CheckMode;
    use crate::driver::PhaseObserver;
    use con_ron_core::arena::checker_split::ValueGroup;
    use con_ron_core::arena::checker_split::ValueKind;
    use con_ron_core::arena::env as ienv;
    use con_ron_core::arena::env::IConstantVal;
    use con_ron_core::arena::monad;
    use con_ron_core::arena::store::EStore;
    use con_ron_core::ron::hashmap::Dup;
    use con_ron_core::arena::store::ENodeView;
    use con_ron_core::arena::store::LNodeView;
    use con_ron_core::arena::store::NNodeView;

    type RecordResult = Result<(), (CheckError, u64)>;

    /// **Phase B as the driver runs it** (`driver::check_decls_driver`'s
    /// `parallel_all` call, with the heartbeat hook the observer asks for):
    /// the tests below are about this call.
    fn check_pool<O: PhaseObserver + Send>(
        pers: &PersTier,
        mode: &CheckMode,
        fe: &IFEnv,
        pend: &[PendingCheck],
        pins: &Pins,
        workers: usize,
        obs: &Mutex<&mut O>,
    ) -> RecordResult {
        let heartbeat = match obs.lock() {
            Ok(g) => g.wants_check_lines(),
            Err(_) => false,
        };
        let done = AtomicUsize::new(0);
        let r = parallel_all(
            pend.len(),
            workers,
            || checker::worker_state(pins),
            |w: &mut AState, k| checker::check_pending(pers, w, mode, fe, &pend[k]),
            |w: &AState, k| {
                if heartbeat {
                    let n = done.fetch_add(1, Ordering::Relaxed) + 1;
                    if let Ok(mut g) = obs.lock() {
                        g.check_after(pers, &w.store, n, pend.len(), &pend[k]);
                    }
                }
            },
        );
        crate::driver::phase_b_verdict(pend, r)
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

    /// The fixture: one store, the tier frozen out of it, and the six or nine
    /// records built into that tier.  A record whose declared type is `Sort 1`
    /// and whose value is `Sort u` checks iff `u + 1 = 1`, i.e. iff `u` is
    /// `Sort 0` — no environment is needed for either outcome, which is the
    /// point: the walk is what is under test, not the checker.
    fn fixture(oks: &[bool]) -> (PersTier, Pins, Vec<PendingCheck>) {
        let pers0: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        ok(con_ron_core::arena::pins::intern_reserved_pins(pers0, &mut st));
        let anon = ok(monad::intern_n_node(pers0, &mut st, NNodeView::Anonymous));
        let zero = ok(monad::intern_l_node(pers0, &mut st, LNodeView::Zero));
        let one = ok(monad::intern_l_node(pers0, &mut st, LNodeView::Succ(zero.dup2())));
        let sort0 = ok(monad::intern_e(pers0, &mut st, ENodeView::Sort(zero.dup2())));
        let sort1 = ok(monad::intern_e(pers0, &mut st, ENodeView::Sort(one.dup2())));
        let mut pend: Vec<PendingCheck> = Vec::new();
        for (k, good) in oks.iter().enumerate() {
            let nm = ok(monad::intern_n_node(
                pers0,
                &mut st,
                NNodeView::Num(anon.dup2(), k as u64),
            ));
            pend.push(PendingCheck {
                vg: ValueGroup {
                    kind: ValueKind::Defn,
                    cv_a: IConstantVal {
                        name: nm,
                        level_params: Vec::new(),
                        ty: sort1.dup2(),
                    },
                    jv: if *good { sort0.dup2() } else { sort1.dup2() },
                },
                pos: k as u64,
                vis: 0,
            });
        }
        let pins = checker::pins_dup(&st.pins);
        let tier = checker::freeze_tier(&mut st.store);
        (tier, pins, pend)
    }

    /// **The pool's guarantee** (the module note): a list whose records 2 and
    /// 4 both fail reports record 2 — the first failure in FOLD order — at
    /// every worker count, because the results are walked in record order.
    #[test]
    fn pool_reports_the_first_failure_at_every_jobs() {
        let (tier, pins, pend) = fixture(&[true, true, false, true, false, true]);
        let fe: IFEnv = ienv::mk_ifenv(ienv::i_env_empty());
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8] {
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            match check_pool(&tier, &mode, &fe, &pend, &pins, workers, &lock) {
                Ok(()) => panic!(
                    "a list with two failing records must fail ({} workers)",
                    workers
                ),
                Err((_, pos)) => assert_eq!(pos, 2, "at {} workers", workers),
            }
        }
    }

    /// **The trusted claim, as a test**: at every worker count the pool
    /// returns what the verified one-worker walk
    /// `checker::check_pending_worker` returns — the same verdict, and on a
    /// failure the same fold position.
    #[test]
    fn pool_is_check_pending_worker_at_every_jobs() {
        let lists: Vec<Vec<bool>> = vec![
            vec![true, true, false, true, false, true],
            vec![true; 9],
            vec![],
            vec![false, true],
            vec![true, true, true, true, true, false],
        ];
        let fe: IFEnv = ienv::mk_ifenv(ienv::i_env_empty());
        let mode = CheckMode::Verified;
        for oks in lists {
            let (tier, pins, pend) = fixture(&oks);
            let seq = checker::check_pending_worker(&tier, &mode, &fe, &pins, &pend);
            for workers in [1usize, 2, 3, 4, 8] {
                let mut obs = Silent;
                let lock = Mutex::new(&mut obs);
                let pooled = check_pool(&tier, &mode, &fe, &pend, &pins, workers, &lock);
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
    /// error `collect_checks` reports, so `Ok` IS the completeness assertion).
    #[test]
    fn pool_accepts_a_clean_list_at_every_jobs() {
        let (tier, pins, pend) = fixture(&[true; 9]);
        let fe: IFEnv = ienv::mk_ifenv(ienv::i_env_empty());
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8, 16] {
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            assert!(
                check_pool(&tier, &mode, &fe, &pend, &pins, workers, &lock).is_ok(),
                "at {} workers",
                workers
            );
        }
    }

    /// The empty list: no worker has anything to claim, and the walk accepts.
    #[test]
    fn pool_on_no_records_accepts() {
        let (tier, pins, _) = fixture(&[]);
        let fe: IFEnv = ienv::mk_ifenv(ienv::i_env_empty());
        let mut obs = Silent;
        let lock = Mutex::new(&mut obs);
        assert!(check_pool(&tier, &CheckMode::Verified, &fe, &[], &pins, 4, &lock).is_ok());
    }

    /// `mergeResults` merges by index whatever order the arrays arrive in, and
    /// a gap in the table is the internal error, tagged with the missing
    /// record's fold position.
    #[test]
    fn merge_is_by_index_and_a_gap_is_internal() {
        let (_, _, pend) = fixture(&[true, true, true]);
        let tab = merge_results(3, vec![vec![(2, Ok(())), (0, Ok(()))], vec![(1, Ok(()))]]);
        assert!(crate::driver::phase_b_verdict(&pend, first_failure(tab)).is_ok());
        let gap = merge_results(3, vec![vec![(0, Ok(())), (2, Ok(()))]]);
        match crate::driver::phase_b_verdict(&pend, first_failure(gap)) {
            Ok(()) => panic!("a gap in the table is never an accept"),
            Err((e, pos)) => {
                assert_eq!(crate::driver::exit_code(&e), 3);
                assert_eq!(pos, 1);
            }
        }
    }
}
