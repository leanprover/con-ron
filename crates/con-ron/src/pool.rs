//! `pool` — con-leche's `Main.lean:213-328`: **phase B on a pool of worker
//! threads** (task #48).
//!
//! The recorded checks are independent by construction — each reads the
//! installed index at its own prefix view, its own record, and a *fresh* memo
//! state — so phase B is `n` workers over one shared claim counter.  This
//! module is that pool, `checkPool` with its three helpers ported one to one:
//! `check_one` (`Main.lean:255-274`), `check_worker` (`:276-291`),
//! `merge_results` (`:293-300`) and `check_pool` (`:302-328`), plus the walk
//! that turns the merged table into a verdict (`collect_checks`,
//! `ConLeche/Cached/Installed.lean:360-383 collectChecks`).
//!
//! ## The guarantee, and why it is the sequential walk's
//!
//! **The verdict, and the record a rejection names, are the same at every
//! `--jobs`.**  A worker's result is the record's index with its outcome; the
//! workers' arrays are merged *by record index* into one table and the table is
//! walked in **record order**, stopping at the first failing record in fold
//! order.  That walk is `check_pending_list`'s, whatever the workers' timing,
//! so the pool cannot report the second failure of a stream that has two —
//! `pool_reports_the_first_failure_at_every_jobs` is the test, at 1, 2, 3, 4
//! and 8 workers on a list whose records 2 and 4 both fail.
//!
//! **The table is complete below the first failure**, which is what makes the
//! walk total.  con-leche's argument, and the port's: a worker that fails
//! record `f` lowers the shared `limit` to `f`, and a worker skips a claimed
//! record at or above the limit.  Every value the limit ever holds is `m` or a
//! *failing* index, hence at least the first failing index `f`; so a record
//! below `f` is never skipped, and — the counter being monotone — it was
//! claimed before `f` was and is finished by the worker that claimed it.
//! Records above `f` may be missing from the table, and the walk never reaches
//! them.  A worker cannot be cancelled mid-check (a check is a pure
//! computation), so the pool always drains.
//!
//! That argument needs no memory ordering beyond atomicity, which is why every
//! access here is `Relaxed`: a stale read of `limit` can only be *larger* than
//! the current value, i.e. can only make a worker do work it could have
//! skipped, and the results themselves travel through the `join` at the end of
//! the scope, which is the release/acquire pair.
//!
//! ## The one deviation: a view per worker, not one shared view
//!
//! con-leche's workers share the installed `FEnv` and take
//! `fe.restrictTo pc.vis` per record, which is `O(1)` because the Lean runtime
//! shares the `Std.HashMap` field.  The port's `fenv::restrict_to` is the same
//! record update but **takes the record by value and returns it** (task #6's
//! linear threading; `kernel/fenv.rs`'s module note says in so many words that
//! this "forecloses the parallel phase B where several workers hold different
//! views of one index at once").
//!
//! So each worker takes **one `fenv::dup` of the installed index**, on its own
//! thread, and threads that one view through every record it claims:
//! `check_pending` lowers the bound to `pc.vis` and restores it, exactly as in
//! the sequential lane, so a worker's view is the installed one again between
//! records.  What is *shared* is what the memory is in — the term DAG and the
//! constant records, reached through `P = std::sync::Arc` (§3.2, task #45),
//! which is what made the pool possible at all.  What is *copied* is one
//! `Name`-keyed table of handles and one handle vector per worker: `O(|env|)`
//! **once per worker**, not per record, and the handles are bumped, not the
//! records (task #34).  The resident set grows by tens of MB per worker, which
//! is the shape of con-leche's own note ("about 25 MB per worker").
//!
//! A failed record consumes the worker's view (`check_pending` takes it by
//! value and the error comes back in its place), so a worker re-`dup`s lazily
//! — at most once, because after a failure at `k` every later claim of that
//! worker is above the limit it just lowered and is skipped.
//!
//! ## Threads, stacks and the address-space arithmetic
//!
//! The workers are `std::thread::scope`d threads with `STACK_BYTES` (1 GiB)
//! reserved each, which is con-leche's figure and the port's own requirement:
//! the fold's recursion depth is the term DAG's, and `fenv::mk_fenv_go` — the
//! `dup` every worker takes — recurses once per constant.  A run therefore
//! needs `3x` the checker's resident set **plus 1 GiB of address space per
//! worker** under `ulimit -v`; `driver::default_jobs` caps the default for
//! exactly that reason and its note has the arithmetic.
//!
//! A worker that fails as a *thread* — a panic, or a spawn that the address
//! space refused — is an internal error, exit 3, never a verdict on the input.
//! That is con-leche's rule for a worker whose `IO` action failed, and a
//! failing check cannot take that path: it is a `RecordResult`.

use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Mutex;

use con_ron_core::cached::installed;
use con_ron_core::cached::parsed_c::PendingCheck;
use con_ron_core::cached::state_c;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::fenv::FEnv;

use crate::driver::PhaseObserver;
use crate::driver::STACK_BYTES;

/// con-leche: none — `RecordResult` with the `GroupChecked` proof erased
/// One record's outcome as a worker hands it back: `Ok(())` for a checked
/// record, or the error tagged with the record's **fold position** (not its
/// record index — the position is what a verdict line names).
///
/// The Lean's `RecordResult` carries the record's `GroupChecked` *proof* on the
/// `ok` side and `checkRecordResult` builds it; both stay on DESIGN.md §3.7's
/// skip list as evidence plumbing (`installed.rs`'s module note), and what is
/// left of them once the proof is erased is this `Result` — hence `none`.
pub type RecordResult = Result<(), (CheckError, u64)>;

/// con-leche: none — a driver-side `CheckError::Internal` from a Rust `&str`
/// The core carries messages as `Vec<u32>` code points (DESIGN.md §3.4), and
/// the pool's two internal errors are formatted here, above it.
fn internal(msg: &str) -> CheckError {
    core_types::internal(msg.chars().map(|c| c as u32).collect())
}

/// con-leche: Main.lean:240-260 checkOne
/// **One claimed record of one worker.**  Below the shared `limit` it is
/// checked from a fresh memo state and its result appended; a failure lowers
/// the limit to its index; on the heartbeat lane the completed-count is bumped
/// and the observer prints under the lock.  A record at or above the limit is
/// skipped — it is above a known failure and the walk will never ask for it.
///
/// `view` is the worker's own `FEnv` (the module note): `None` until its first
/// record, and `None` again after a failure, since `check_pending` takes the
/// view by value.
#[allow(clippy::too_many_arguments)]
fn check_one<O: PhaseObserver + Send>(
    mode: &CheckMode,
    fe: &FEnv,
    pend: &[PendingCheck],
    limit: &AtomicUsize,
    done: &AtomicUsize,
    heartbeat: bool,
    obs: &Mutex<&mut O>,
    k: usize,
    view: &mut Option<FEnv>,
    acc: &mut Vec<(usize, RecordResult)>,
) {
    if k >= limit.load(Ordering::Relaxed) {
        return;
    }
    let mut st: CState = state_c::cstate_new();
    let fe_w: FEnv = match view.take() {
        Some(v) => v,
        None => fenv::dup(fe),
    };
    let r: RecordResult = match installed::check_pending(mode, &mut st, fe_w, &pend[k]) {
        Ok(fe2) => {
            *view = Some(fe2);
            Ok(())
        }
        Err(e) => {
            limit.fetch_min(k, Ordering::Relaxed);
            Err((e, pend[k].pos))
        }
    };
    acc.push((k, r));
    if heartbeat {
        let n = done.fetch_add(1, Ordering::Relaxed) + 1;
        let fe_line: &FEnv = match view {
            Some(v) => v,
            None => fe,
        };
        // A poisoned lock means another worker panicked while printing; the
        // panic is the report and this line is dropped.
        if let Ok(mut g) = obs.lock() {
            g.check_after(n, pend.len(), &pend[k], &st, fe_line);
        }
    }
}

/// con-leche: Main.lean:262-278 checkWorker
/// **One worker**: claim ONE record off the shared counter, check it, repeat
/// until the counter is past the records.  One record per claim is con-leche's
/// choice and its reason is the port's: the work is millions of mostly tiny
/// checks with a skewed tail, and the heavy ones sit *close together* in the
/// stream, so claiming singly spreads a cluster of heavy declarations over the
/// whole pool instead of serialising it inside one claimed range — the only
/// item that can then strand the pool is the single largest check.
///
/// Deviation: the cited `fuel` (`pend.size + 1` claims, Lean's termination
/// device) is a `loop` that returns when its claim is past the end, which is
/// the same bound — every claim advances the counter by exactly one.
fn check_worker<O: PhaseObserver + Send>(
    mode: &CheckMode,
    fe: &FEnv,
    pend: &[PendingCheck],
    next: &AtomicUsize,
    limit: &AtomicUsize,
    done: &AtomicUsize,
    heartbeat: bool,
    obs: &Mutex<&mut O>,
) -> Vec<(usize, RecordResult)> {
    let m = pend.len();
    let mut acc: Vec<(usize, RecordResult)> = Vec::new();
    let mut view: Option<FEnv> = None;
    loop {
        let k = next.fetch_add(1, Ordering::Relaxed);
        if k >= m {
            return acc;
        }
        check_one(
            mode, fe, pend, limit, done, heartbeat, obs, k, &mut view, &mut acc,
        );
    }
}

/// con-leche: Main.lean:280-287 mergeResults
/// The workers' arrays merged **by record index** into one table.  The table is
/// the pool's whole interface to the verdict: which worker produced a result,
/// and when, is recorded nowhere.
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
///
/// Deviation: the cited walk carries the `GroupChecked` facts of the records
/// below `j` — erased here (§3.7's skip list, `RecordResult`'s note) — and
/// checks that slot `j` holds record `j`, which the port's table answers by
/// construction: the index is the slot, not data beside the result, so that arm
/// has no port.
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
/// **Phase B on a pool of `workers` worker threads.**  Spawns them inside a
/// `std::thread::scope` — which is what lets them hold `&FEnv` and
/// `&[PendingCheck]` into the installed environment with no `Arc<Mutex<…>>` and
/// no `'static` bound — waits for all of them, merges their results by record
/// index and walks the table in record order.
///
/// `workers` is the count the caller has already clamped
/// (`driver::workers_for`: `max(1, min(jobs, m))`), and `heartbeat` is the
/// port's spelling of the cited `stride > 0` guard inside `checkOne`: off, no
/// worker touches the `done` counter or the observer at all, which is the
/// difference between a plain pooled run and the `--progress` lane (one extra
/// atomic increment per completed record, for an exact completed-count).
pub fn check_pool<O: PhaseObserver + Send>(
    mode: &CheckMode,
    fe: &FEnv,
    pend: &[PendingCheck],
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
                    check_worker(mode, fe, pend, &next, &limit, &done, heartbeat, obs)
                });
            match spawned {
                Ok(h) => handles.push(h),
                // Out of threads, or out of address space for another 1 GiB
                // stack: the pool cannot be built as asked.  The workers
                // already spawned are joined below all the same.
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
    use con_ron_core::cached::parsed_c::ValueGroup;
    use con_ron_core::cached::parsed_c::ValueKind;
    use con_ron_core::kernel::env;
    use con_ron_core::kernel::env::ConstantVal;
    use con_ron_core::kernel::expr;
    use con_ron_core::kernel::level;
    use con_ron_core::kernel::name;

    /// An observer that prints nothing and wants no check lines — the plain
    /// pooled lane.
    struct Silent;
    impl PhaseObserver for Silent {}

    /// A record whose declared type is `Sort 1` and whose value is
    /// `Sort level`: it checks iff `level + 1 = 1`, i.e. iff `level` is `Sort
    /// 0`.  No environment is needed for either outcome, which is the point —
    /// the walk is what is under test, not the checker.
    fn record(pos: u64, ok: bool) -> PendingCheck {
        let ty = expr::sort(level::succ(level::zero()));
        let jv = if ok {
            expr::sort(level::zero())
        } else {
            expr::sort(level::succ(level::zero()))
        };
        PendingCheck {
            vg: ValueGroup {
                kind: ValueKind::Defn,
                cv_a: ConstantVal {
                    name: name::mk_str(name::anonymous(), vec![0x64, 0x30 + pos as u32]),
                    level_params: Vec::new(),
                    ty,
                },
                jv,
            },
            pos,
            vis: 0,
        }
    }

    /// **The pool's guarantee** (the module note): a list whose records 2 and 4
    /// both fail reports record 2 — the first failure in FOLD order — at every
    /// worker count, because the results are walked in record order.  Record 2
    /// is `pos = 2`, which is what a verdict line names.
    #[test]
    fn pool_reports_the_first_failure_at_every_jobs() {
        let fe: FEnv = fenv::mk_fenv(env::empty());
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8] {
            let pend: Vec<PendingCheck> = (0..6)
                .map(|k| record(k, k != 2 && k != 4))
                .collect();
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            match check_pool(&mode, &fe, &pend, workers, &lock) {
                Ok(()) => panic!("a list with two failing records must fail ({} workers)", workers),
                Err((_, pos)) => assert_eq!(pos, 2, "at {} workers", workers),
            }
        }
    }

    /// A list every record of which checks is accepted at every worker count,
    /// and every slot of the table is filled (an unfilled one is the internal
    /// error `collect_checks` reports, so `Ok` IS the completeness assertion).
    #[test]
    fn pool_accepts_a_clean_list_at_every_jobs() {
        let fe: FEnv = fenv::mk_fenv(env::empty());
        let mode = CheckMode::Verified;
        for workers in [1usize, 2, 3, 4, 8, 16] {
            let pend: Vec<PendingCheck> = (0..9).map(|k| record(k, true)).collect();
            let mut obs = Silent;
            let lock = Mutex::new(&mut obs);
            assert!(
                check_pool(&mode, &fe, &pend, workers, &lock).is_ok(),
                "at {} workers",
                workers
            );
        }
    }

    /// The empty list: no worker has anything to claim, and the walk accepts.
    #[test]
    fn pool_on_no_records_accepts() {
        let fe: FEnv = fenv::mk_fenv(env::empty());
        let mut obs = Silent;
        let lock = Mutex::new(&mut obs);
        assert!(check_pool(&CheckMode::Verified, &fe, &[], 4, &lock).is_ok());
    }

    /// `mergeResults` merges by index whatever order the arrays arrive in, and
    /// a gap in the table is the internal error, tagged with the missing
    /// record's fold position.
    #[test]
    fn merge_is_by_index_and_a_gap_is_internal() {
        let pend: Vec<PendingCheck> = (0..3).map(|k| record(10 + k, true)).collect();
        let tab = merge_results(3, vec![vec![(2, Ok(())), (0, Ok(()))], vec![(1, Ok(()))]]);
        assert!(collect_checks(&pend, tab).is_ok());
        let gap = merge_results(3, vec![vec![(0, Ok(())), (2, Ok(()))]]);
        match collect_checks(&pend, gap) {
            Ok(()) => panic!("a gap in the table is never an accept"),
            Err((e, pos)) => {
                assert_eq!(crate::driver::exit_code(&e), 3);
                assert_eq!(pos, 11);
            }
        }
    }
}
