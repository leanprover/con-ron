//! `pool` — con-leche's `Main.lean:193-316` over the ARENA: **phase B on a
//! pool of worker threads** (DESIGN.md §8.3, §8.6's P6 item 6, task
//! #97-P6-6b).
//!
//! The four functions are the cited ones one to one: `check_one`
//! (`Main.lean:240-260`), `check_worker` (`:262-278`), `merge_results`
//! (`:280-287`) and `check_pool` (`:289-316`), plus the walk that turns the
//! merged table into a verdict (`collect_checks`,
//! `ConLeche/Cached/Installed.lean:392-416 collectChecks`).  Task #97-SWAP put
//! it here, replacing the `Expr`-tree pool of task #48 that it was written
//! beside.
//!
//! **Threads live here and never in `con-ron-core`** (DESIGN.md §8.5): the
//! verified crate is a pure state-threading computation and knows nothing of
//! this module.  What it had to grow for the pool is one shared parameter —
//! `pers: &PersTier` — and one scalar, and both are task #97-P6-6b's.
//!
//! ## What a worker is
//!
//! §8.3 has said since P1 what phase B is: "the persistent tier is immutable
//! in phase B, each worker owns a scratch tier — **no atomics anywhere**",
//! and task #97-P6-6 verified it in the code (`check_pending` is the bracket;
//! `intern_persistent`'s only caller is phase A's `arena::promote`).  So a
//! worker is
//!
//!   * its own `AState`, `checker::worker_state(pins)` — an EMPTY store whose
//!     four `shared_on` flags are set, its own `Memos`, its own `Caches`, and
//!     a COPY of the driver's `Pins` (sixty-eight handles into the persistent
//!     tier, so a copy is two `Vec<NIdx>` and three words);
//!   * `&PersTier`, the persistent tier the driver froze at the phase
//!     boundary (`checker::freeze_tier`) and every worker reads;
//!   * `&IFEnv`, the installed index — **by reference, and this is what task
//!     #97-P6-6b's second half bought**.  `check_pending` used to take the
//!     index BY VALUE so that it could restrict it to the record's prefix
//!     bound; a worker would have needed `ifenv_dup`, which DESIGN.md (task
//!     #97-P6-6b) prices at ≈1.4 GB a worker on Mathlib.  The bound is a scalar
//!     parameter now (`pc.vis`), so the environment is shared and **a worker
//!     costs no environment copy at all**.
//!
//! Every sequential piece of that — the freeze, the worker's state, the
//! per-record check — is the VERIFIED crate's since task #97-P5-Driver, and
//! so is what one worker runs: `checker::check_pending_worker(pers, mode, fe,
//! pins, w)`, which is ONE worker's state and `check_pending_list` from it
//! over the records `w` that worker checked.
//!
//! ## THE TRUSTED CLAIM, and the whole of it
//!
//! **If `check_pool(pers, mode, fe, pend, pins, n, _)` accepts, then the
//! records of `pend` are covered by lists `w_1 … w_n`, one per worker (the
//! records that worker checked, in the order it checked them), and
//! `checker::check_pending_worker(pers, mode, fe, pins, w_j)` accepts every
//! one of them** — at every worker count `n`.  That is the capstone's stage
//! 6 (`Refine2/Checker/Phased.lean`'s `PoolAccepts`, task #97-P5-POOL), and it
//! is a statement about this module's control flow only: which worker
//! checked which record, and what a worker checked before, is not asked,
//! because the capstone relates every worker's walk to the twin on its own
//! and assembles con-leche's pure fold from the per-record accepts, each at
//! its record's own prefix environment.  The argument:
//!
//! * **A worker is the verified walk.**  `check_worker` builds ONE
//!   `checker::worker_state(pins)` and calls `checker::check_pending` on the
//!   records it claims, in claim order, threading that state: exactly
//!   `check_pending_list` over its records — `check_pending_worker` on them.
//!   The observer line between two records holds `&st.store` only.  A record
//!   at or above `limit` is skipped without a call, and on an accepting run
//!   the limit never moves, so no claimed record is skipped.
//! * **Merge by record index — master's argument.**  A worker's result is
//!   the record's index with its outcome; the workers' arrays are merged *by
//!   record index* into one table and `collect_checks` walks it in record
//!   order, answering `Ok` only if every slot holds `Ok`.  So an accept means
//!   every record was checked and accepted by the worker that claimed it,
//!   whatever the timing.
//!
//! The failure side is not part of the claim the capstone uses, but the pool
//! keeps master's behaviour there: the walk stops at the first failing record
//! in fold order, and the table is complete below it.  con-leche's argument:
//! a worker that fails record `f` lowers the shared `limit` to `f`, and a
//! worker skips a claimed record at or above the limit.  Every value the limit
//! ever holds is `m` or a *failing* index, hence at least the first failing
//! index `f`; so a record below `f` is never skipped, and — the counter being
//! monotone — it was claimed before `f` was and is finished by the worker that
//! claimed it.  `pool_reports_the_first_failure_at_every_jobs` is the test, at
//! 1, 2, 3, 4 and 8 workers on a list whose records 2 and 4 both fail;
//! `pool_is_check_pending_worker_at_every_jobs` checks that the pool's result
//! is the one-worker walk's.
//!
//! Every access is `Relaxed`: a stale read of `limit` can only be *larger*
//! than the current value, i.e. can only make a worker do work it could have
//! skipped, and the results themselves travel through the `join` at the end
//! of the scope, which is the release/acquire pair.
//!
//! **A worker keeps one `AState` across its records** (task #97-P6-6b), where
//! master's pool checked each record from a fresh state: the bracket
//! (`enter_scratch`, `drop_scratch`) resets everything but capacity, and a
//! fresh state per record measured **+16.4 % instructions on `Init`** (task
//! #97-P5-Driver).  Until task #97-P5-POOL the claim was that the pool returns
//! what one worker walking every record returns, which needed a second,
//! untrusted-by-proof argument — that a record's outcome does not depend on
//! what its worker checked before.  The claim above does not need it.
//!
//! ## Threads, stacks and the address-space arithmetic
//!
//! The workers are `std::thread::scope`d threads with `STACK_BYTES` (1 GiB)
//! reserved each — which is what lets them hold `&PersTier`, `&IFEnv` and
//! `&[PendingCheck]` with no `Arc` and no `'static` bound — so a run needs
//! `3x` the checker's resident set **plus 1 GiB of address space per worker**
//! under `ulimit -v`.  A worker that fails as a *thread* (a panic, or a spawn
//! the address space refused) is an internal error, exit 3, never a verdict
//! on the input.

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Mutex;

use con_ron_core::arena::checker;
use con_ron_core::arena::checker::PendingCheck;
use con_ron_core::arena::env::IFEnv;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::pins::Pins;
use con_ron_core::arena::store::PersTier;

use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;

use crate::driver::PhaseObserver;
use crate::driver::STACK_BYTES;

/// con-leche: none — `RecordResult` with the `GroupChecked` proof erased
/// One record's outcome as a worker hands it back: `Ok(())` for a checked
/// record, or the error tagged with the record's **fold position** (not its
/// record index — the position is what a verdict line names).
pub type RecordResult = Result<(), (CheckError, u64)>;

/// con-leche: none — a driver-side `CheckError::Internal` from a Rust `&str`
/// The core carries messages as `Vec<u32>` code points (DESIGN.md §3.4), and
/// the pool's two internal errors are formatted here, above it.
fn internal(msg: &str) -> CheckError {
    core_types::internal(msg.chars().map(|c| c as u32).collect())
}

/// con-leche: Main.lean:240-260 checkOne
/// **One claimed record of one worker.**  Below the shared `limit` it is
/// checked inside its own scratch tier and its result appended; a failure
/// lowers the limit to its index; on the heartbeat lane the completed-count
/// is bumped and the observer prints under the lock.  A record at or above
/// the limit is skipped — it is above a known failure and the walk will never
/// ask for it.
#[allow(clippy::too_many_arguments)]
fn check_one<O: PhaseObserver + Send>(
    pers: &PersTier,
    mode: &CheckMode,
    fe: &IFEnv,
    pend: &[PendingCheck],
    limit: &AtomicUsize,
    done: &AtomicUsize,
    heartbeat: bool,
    obs: &Mutex<&mut O>,
    k: usize,
    st: &mut AState,
    acc: &mut Vec<(usize, RecordResult)>,
) {
    if k >= limit.load(Ordering::Relaxed) {
        return;
    }
    let r: RecordResult = match checker::check_pending(pers, st, mode, fe, &pend[k]) {
        Ok(()) => Ok(()),
        Err(e) => {
            limit.fetch_min(k, Ordering::Relaxed);
            Err((e, pend[k].pos))
        }
    };
    acc.push((k, r));
    if heartbeat {
        let n = done.fetch_add(1, Ordering::Relaxed) + 1;
        // A poisoned lock means another worker panicked while printing; the
        // panic is the report and this line is dropped.
        if let Ok(mut g) = obs.lock() {
            g.check_after(pers, &st.store, n, pend.len(), &pend[k]);
        }
    }
}

/// con-leche: Main.lean:262-278 checkWorker
/// **One worker**: claim ONE record off the shared counter, check it, repeat
/// until the counter is past the records.  One record per claim is
/// con-leche's choice and its reason is the port's: the work is millions of
/// mostly tiny checks with a skewed tail, and the heavy ones sit *close
/// together* in the stream, so claiming singly spreads a cluster of heavy
/// declarations over the whole pool instead of serialising it inside one
/// claimed range.
///
/// Deviation: the cited `fuel` (`pend.size + 1` claims, Lean's termination
/// device) is a `loop` that returns when its claim is past the end, which is
/// the same bound — every claim advances the counter by exactly one.
#[allow(clippy::too_many_arguments)]
fn check_worker<O: PhaseObserver + Send>(
    pers: &PersTier,
    mode: &CheckMode,
    fe: &IFEnv,
    pend: &[PendingCheck],
    pins: &Pins,
    next: &AtomicUsize,
    limit: &AtomicUsize,
    done: &AtomicUsize,
    heartbeat: bool,
    obs: &Mutex<&mut O>,
) -> Vec<(usize, RecordResult)> {
    let m = pend.len();
    let mut acc: Vec<(usize, RecordResult)> = Vec::new();
    let mut st: AState = checker::worker_state(pins);
    loop {
        let k = next.fetch_add(1, Ordering::Relaxed);
        if k >= m {
            return acc;
        }
        check_one(
            pers, mode, fe, pend, limit, done, heartbeat, obs, k, &mut st, &mut acc,
        );
    }
}

/// con-leche: Main.lean:280-287 mergeResults
/// The workers' arrays merged **by record index** into one table.  The table
/// is the pool's whole interface to the verdict: which worker produced a
/// result, and when, is recorded nowhere.
pub fn merge_results(
    m: usize,
    results: Vec<Vec<(usize, RecordResult)>>,
) -> Vec<Option<RecordResult>> {
    let mut tab: Vec<Option<RecordResult>> = Vec::with_capacity(m);
    for _ in 0..m {
        tab.push(None);
    }
    for rs in results {
        for (k, r) in rs {
            if k < m {
                tab[k] = Some(r);
            }
        }
    }
    tab
}

/// con-leche: ConLeche/Cached/Installed.lean:392-416 collectChecks
/// **The results, assembled in record order.**  Slot `j` holds record `j`'s
/// result; the walk stops at the first failure, so its verdict is
/// `check_pending_list`'s whatever order the results were produced in.  An
/// empty slot is an internal error (a pool that did not do its job), never a
/// verdict on the input.
pub fn collect_checks(pend: &[PendingCheck], tab: Vec<Option<RecordResult>>) -> RecordResult {
    for (j, slot) in tab.into_iter().enumerate() {
        match slot {
            Some(Ok(())) => {}
            Some(Err(e)) => return Err(e),
            None => {
                return Err((
                    internal(&format!("check phase: record {} was never checked", j)),
                    pend[j].pos,
                ))
            }
        }
    }
    Ok(())
}

/// con-leche: Main.lean:289-316 checkPool
/// **Phase B on a pool of `workers` worker threads** — each worker the
/// verified `checker::check_pending_worker` over the records it claims (the
/// module note's trusted claim).  Spawns them inside a
/// `std::thread::scope` — which is what lets them hold `&PersTier`, `&IFEnv`
/// and `&[PendingCheck]` with no `Arc<Mutex<…>>` and no `'static` bound —
/// waits for all of them, merges their results by record index and walks the
/// table in record order.
///
/// `workers` is the count the caller has already clamped
/// (`driver::workers_for`: `max(1, min(jobs, m))`), and `heartbeat` is the
/// port's spelling of the cited `stride > 0` guard inside `checkOne`: off, no
/// worker touches the `done` counter or the observer at all.
pub fn check_pool<O: PhaseObserver + Send>(
    pers: &PersTier,
    mode: &CheckMode,
    fe: &IFEnv,
    pend: &[PendingCheck],
    pins: &Pins,
    workers: usize,
    obs: &Mutex<&mut O>,
) -> RecordResult {
    let m = pend.len();
    let heartbeat = match obs.lock() {
        Ok(g) => g.wants_check_lines(),
        Err(_) => false,
    };
    let next = AtomicUsize::new(0);
    let limit = AtomicUsize::new(m);
    let done = AtomicUsize::new(0);
    let mut results: Vec<Vec<(usize, RecordResult)>> = Vec::with_capacity(workers);
    let mut failure: Option<String> = None;
    std::thread::scope(|scope| {
        let mut handles = Vec::with_capacity(workers);
        for w in 0..workers {
            let spawned = std::thread::Builder::new()
                .stack_size(STACK_BYTES)
                .name(format!("check-{}", w))
                .spawn_scoped(scope, || {
                    check_worker(
                        pers, mode, fe, pend, pins, &next, &limit, &done, heartbeat, obs,
                    )
                });
            match spawned {
                // Out of threads, or out of address space for another 1 GiB
                // stack: the pool cannot be built as asked.  The workers
                // already spawned are joined below all the same.
                Ok(h) => handles.push(h),
                Err(e) => failure = Some(format!("cannot spawn a check worker: {}", e)),
            }
        }
        for h in handles {
            match h.join() {
                Ok(rs) => results.push(rs),
                Err(_) => failure = Some("a worker panicked".to_string()),
            }
        }
    });
    match failure {
        Some(msg) => Err((internal(&format!("check phase: {}", msg)), 0)),
        None => collect_checks(pend, merge_results(m, results)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
        let tier = match checker::freeze_tier(&mut st.store) {
            Ok(t) => t,
            Err(_) => panic!("the fixture's store has its flags down"),
        };
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
        assert!(collect_checks(&pend, tab).is_ok());
        let gap = merge_results(3, vec![vec![(0, Ok(())), (2, Ok(()))]]);
        match collect_checks(&pend, gap) {
            Ok(()) => panic!("a gap in the table is never an accept"),
            Err((e, pos)) => {
                assert_eq!(crate::driver::exit_code(&e), 3);
                assert_eq!(pos, 1);
            }
        }
    }
}
