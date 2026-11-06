//! `driver` — con-leche's `Driver/{Cli,CheckMain,Run}.lean`, over the ARENA (tasks #37, #48 and
//! #97-P4f), and the Rust side of the Lean twin's
//! `proof/ConRon/Arena/Main.lean`.
//!
//! The module is that driver in its order: the reads,
//! the two phases with the boundary visible, the `--progress` heartbeat behind
//! one observer trait, the verdict lines, the exit-code mapping, and the flag
//! parsers.  Task #97-SWAP put it here, under the name the shipping driver
//! always had: it was `crates/con-ron-arena/src/driver.rs` through the arena
//! campaign, beside the `Expr`-tree driver it has now replaced, and the
//! eleven representation-free items it used to import across the crate line
//! ([`exit_code`], `verdict_word`, `message`, `ms_secs`, `progress_pace`,
//! `jobs_count`, `default_jobs`, [`workers_for`],
//! `read_up_to`, `STACK_BYTES`) are back in it, unchanged.
//!
//! ## THE EXIT CODES
//!
//! | exit | verdict | meaning |
//! |---|---|---|
//! | 0 | `accepted N declarations` | every declaration checked; `N` counts the file's declaration records |
//! | 1 | `rejected` | a declaration is invalid |
//! | 2 | `declined` | the checker positively detected a feature it does not support, and says which |
//! | 3 | error | bad usage, malformed input, or an internal failure of unclear cause |
//!
//! ## What the arena changed about the driver
//!
//! 1. **The state is one `AState`** (`con_ron_core::arena::monad::AState`: the
//!    store, the per-call memos, the per-declaration caches), threaded as a
//!    `&mut` through the parse, the preparation, the pin walk and both phases.
//!    The `Expr`-tree driver threaded a `CState` and the declarations carried
//!    their own terms; here the terms are in the state and the records are
//!    handles into it, so nothing may be run against a state that is not the
//!    one they were interned into.
//! 2. **`intern_all_pins` runs once, before the fold, with the scratch tier
//!    off** (DESIGN.md §8.6 P2d, task #97-P4d's "for P4f"): every pinned datum
//!    is in the PERSISTENT cons table before any declaration's check can
//!    intern one into a tier that is about to vanish.  Its result — the
//!    interned pin list — is the fold's parameter.
//! 3. **Phase B's bracket is `run_job`'s** (`check_pending`'s and
//!    `block_check`'s), which empties the scratch tier around each job.  A
//!    driver that checked records itself without it would grow the scratch tier
//!    without bound; the pool calls it once per job and nothing else opens a
//!    tier.
//! 4. **Phase B runs on [`crate::pool`] at every `--jobs=<n>`**, which is
//!    DESIGN.md §8.3's arrangement and needs no atomics: the persistent tier
//!    and the installed index are immutable in phase B, so they are shared by
//!    reference, and each worker owns a scratch tier, its own caches and a copy
//!    of the pin handles.  `--jobs=1` is the same install and the same jobs on
//!    one worker.
//!
//! ## The read loop
//!
//! [`parse_export_handle_d`] is `ConLeche/Frontend/CheckerIO.lean`'s
//! `foldChunks` over forward reads (its positional reads and its parallel
//! rounds parse are not ported): the VERIFIED loop `export_c::parse_source` (task
//! #97-P5-Driver moved it into the core) over [`HandleSource`], the handle
//! read strictly forward 4 MiB at a time, each buffer fed to `chunk_step` and
//! dropped, the first empty read its end of file and `chunk_finish` the
//! close.  Never seeked, never re-opened, and no scratch file
//! exists; the input is a regular file, checked before it is opened.
//! `parse_source` is `export_c::parse_chunks` over the chunks read — a
//! theorem (`Refine2/Frontend/Source.lean`), under the one hypothesis about
//! the input the binary trusts: that the reads are the file's bytes, in
//! order.

use std::io::Read;
use std::sync::Mutex;
use std::time::Instant;

use con_ron_core::arena::checker;
use con_ron_core::arena::env as ienv;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::arena::stream_index;
use con_ron_core::arena::stream_index::IStreamIndex;
use con_ron_core::frontend::pace::{pace_due_count, pace_on, pace_trace, Pace};
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
use con_ron_core::arena::store::EStore;
use con_ron_core::frontend::export_c;
use con_ron_core::frontend::export_c::ChunkSource;
use con_ron_core::frontend::export_c::ParseResultD;

use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::pins_decode;
use con_ron_core::kernel::env::CheckMode;

use con_ron_core::arena::store::PersTier;

use crate::pool::parallel_all;
use crate::pool::ParallelError;

// ---------------------------------------------------------------------------
// The flags, the messages and the reads (task #97-SWAP)
//
// These eleven items are the driver's own and say nothing about the term
// representation: the flag parsers and their caps, the exit-code mapping, the
// verdict word, the `CheckError` rendering and the read loop.  They were
// `crates/con-ron`'s before the swap and `con-ron` imported them across
// the crate line so that the two binaries of the differential sweep could not
// disagree about a command line; the swap deleted the other binary, so they
// live here, unchanged.
// ---------------------------------------------------------------------------

/// con-leche: none — the Lean runtime's per-thread stack reservation, which
/// `Driver/Cli.lean`'s `--jobs` note measures at 1 GiB per worker.  The fold's
/// recursion depth is the term DAG's, and so is the frontend's
/// (`canon_expr_eq_fast`, `occurs_const_go`), so the whole run is on one.
pub const STACK_BYTES: usize = 1 << 30;

/// con-leche: none — rendering a `CheckError`'s payload, which `core_types`
/// carries as a `Vec<u32>` of code points (DESIGN.md §3.4) where Lean carries
/// a `String`.
pub fn message(e: &CheckError) -> String {
    let cps: &Vec<u32> = match e {
        CheckError::NotImplemented(m) => m,
        CheckError::Invalid(m) => m,
        CheckError::Internal(m) => m,
        CheckError::Native(m) => m,
    };
    cps.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{fffd}'))
        .collect()
}

/// con-leche: ConLeche/Cached/ParsedC.lean:251-253 msSecs
/// Milliseconds as seconds.  Also a deliberate skip in the core, for
/// `declCLabel`'s reason.  Deviation: three decimals rather than con-leche's
/// one.
pub fn ms_secs(ms: u128) -> String {
    format!("{}.{:03}", ms / 1000, ms % 1000)
}

/// con-leche: none — `IO.FS.Handle.read`, which returns *up to* `n` bytes and
/// an empty buffer at end of file; `Read::read` may also stop short of a full
/// buffer mid-file, so the port loops until the buffer is full or the reader
/// is done.
pub fn read_up_to<R: Read>(h: &mut R, buf: &mut [u8]) -> std::io::Result<usize> {
    let mut got = 0usize;
    while got < buf.len() {
        match h.read(&mut buf[got..]) {
            Ok(0) => break,
            Ok(n) => got += n,
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(got)
}

/// con-leche: ConLeche/Driver/CheckMain.lean:32-39 ConLeche.CheckError.exitCode
/// The cited three codes, plus the port's own fourth constructor
/// (`core_types::CheckError::Native`, DESIGN.md §3's ruling of 2026-09-13):
/// a failure with no con-leche counterpart — a machine-word limit, a width
/// check — is a **decline**, exit 2, the same code as "not implemented",
/// because that is what it is: the port cannot carry this input, and says so
/// rather than rejecting the stream (1) or claiming a checker bug (3).
pub fn exit_code(e: &CheckError) -> u8 {
    match e {
        CheckError::NotImplemented(_) => 2,
        CheckError::Invalid(_) => 1,
        CheckError::Internal(_) => 3,
        CheckError::Native(_) => 2,
    }
}

/// con-leche: none — the verdict word `OVERVIEW.md` §2.2 tabulates against each
/// exit code.  con-leche prints the word only for the accept (`accepted N
/// declarations`); a rejection's line is the error message itself, so this is
/// the port's own handle for a log to grep.
pub fn verdict_word(code: u8) -> &'static str {
    match code {
        0 => "accepted",
        1 => "rejected",
        2 => "declined",
        _ => "error",
    }
}

/// con-leche: none — the port's cap on the `--jobs` default
/// **The cap on the default worker count, and the memory arithmetic behind
/// it.**  con-leche's default is one worker per hardware thread, and on a big
/// machine that default *aborts*: every worker reserves ~1 GiB of address space
/// for its stack, so 96 workers ask for 96 GiB of it and
/// `_tmp/corpus/baseline.md`'s last row is con-leche at its own default —
/// exit 134, "failed to create thread", under `ulimit -v 22000000`.
///
/// The port keeps con-leche's default *rule* and caps it: the default is
/// `min(hardware threads, JOBS_DEFAULT_CAP)`, and an explicit `--jobs=<n>` is
/// obeyed to the letter (a measurement must be able to ask for 96).  The
/// arithmetic a caller under `ulimit -v` needs is
///
/// ```text
/// address space >= 3 x (the checker's resident set) + 1 GiB per worker
/// ```
///
/// — the `3x` is CLAUDE.md's rule for the checker itself, and the per-worker
/// gigabyte is the stack reservation `STACK_BYTES` asks for, which counts
/// against `ulimit -v` whether or not it is ever touched.  The *resident* cost
/// of a worker is much smaller: one `fenv::dup` of the installed index
/// (`pool`'s module note), tens of MB.
pub const JOBS_DEFAULT_CAP: u64 = 16;

/// con-leche: ConLeche/Driver/Cli.lean:219-304 runArgs
/// The `--jobs` default, which con-leche reads in `run` off
/// `System.Platform.Internal.getHardwareConcurrency` — "one worker per
/// hardware thread", and one worker on a machine that reports none — capped
/// here at `JOBS_DEFAULT_CAP` for the reason that constant's note gives.
pub fn default_jobs() -> u64 {
    let hw: u64 = match std::thread::available_parallelism() {
        Ok(n) => n.get() as u64,
        Err(_) => 1,
    };
    if hw < JOBS_DEFAULT_CAP {
        hw
    } else {
        JOBS_DEFAULT_CAP
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:79-101 jobsCount
/// The worker count: a decimal numeral of at least 1, `1` being the sequential
/// lane (one worker, no shared counter and no result table).  `0` and a
/// non-numeral are usage errors (exit 3), as in con-leche, so a script that
/// lowers the count for an address-space limit behaves the same against both
/// binaries.  Since task #48 the value is **acted on**: `crate::pool` is phase
/// B at every count above 1.
pub fn jobs_count(v: &str) -> Result<u64, String> {
    match v.parse::<u64>() {
        Ok(0) => Err("--jobs takes a worker count of at least 1 \
                      (a decimal numeral); omit the flag for one worker per \
                      hardware thread"
            .to_string()),
        Ok(n) => Ok(n),
        Err(_) => Err(format!(
            "--jobs takes a worker count \
             (a decimal numeral of at least 1), got {}",
            crate::render::display_str(v)
        )),
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:56-77 progressPace
/// The progress heartbeat's pace, read off the `--progress[=N|P%|Ss]` flag:
/// every `N` declarations, per `P` percent of a phase, or at the first one done
/// after `S` seconds (`Pace`).  No flag is off; bare `--progress` is every one.
/// A value of another form, and a zero — the flag asking for no heartbeat — are
/// usage errors (exit 3): a run's output must be readable off its invocation,
/// never silently degraded.
pub fn progress_pace(v: &str) -> Result<Pace, String> {
    let bad = || {
        Err(format!(
            "--progress takes a number of declarations of at least 1, a percentage \
             from 1% to 100%, or seconds of at least 1s, got {}; omit the flag for no \
             heartbeat",
            crate::render::display_str(v)
        ))
    };
    if let Some(p) = v.strip_suffix('%') {
        match p.parse::<u64>() {
            Ok(p) if (1..=100).contains(&p) => Ok(Pace::Percent(p)),
            _ => bad(),
        }
    } else if let Some(n) = v.strip_suffix('s') {
        match n.parse::<u64>() {
            Ok(0) | Err(_) => bad(),
            Ok(n) => Ok(Pace::Seconds(n)),
        }
    } else {
        match v.parse::<u64>() {
            Ok(0) | Err(_) => bad(),
            Ok(n) => Ok(Pace::Every(n)),
        }
    }
}

/// con-leche: none — how a run *chooses* `checkDecls`' pin argument, which
/// con-leche does not have to: its driver passes `ConLeche.natOpPinSets`.
///
/// **The pin list a run checks with** (task #43).  Since con-leche task #304
/// `pins` is an explicit parameter of the fold with **no default** — asked for
/// on con-ron's behalf, so that the large constant leaves the statement and
/// the theorem can say outright that consistency does not depend on it — and
/// the binary is what supplies `natOpPinSets`.  The port supplies the same
/// value: it carries it as an *embedded text constant inside the verified
/// core* (`kernel::pins_text::PINS_TEXT`) and decodes it with a verified
/// decoder (`kernel::pins_decode::decode_embedded`), so a run checks with
/// con-leche's own pins and nothing is read from outside.  That is the
/// default, and the headline theorems take the decoder's output as their
/// `hpins` premise (`proof/ConRon/Capstone.lean`; the `_embedded` forms fix
/// the text to `PINS_TEXT`).
///
/// The two overrides are **for testing only** and neither is a con-leche
/// spelling: `--pins FILE` reads a `con-ron-pins/2` dump through the
/// *unverified* reader (task #31's arrangement, kept so that a differential
/// sweep can hand the checker a pin list the embedded one is not, e.g. after a
/// con-leche bump and before `scripts/gen-pins.sh` runs), and `--no-pins` is
/// the empty list, which is what exercises the pin loop's `[]` arm
/// (`scripts/diff-e2e.sh --no-pins`).
pub fn pins_for_run(
    over: &Option<String>,
    no_pins: bool,
) -> Result<Vec<NatOpPinSet>, String> {
    if no_pins {
        return Ok(Vec::new());
    }
    match over {
        Some(p) => {
            let shown = crate::render::display_path(p);
            let text = std::fs::read_to_string(p).map_err(|e| format!("{}: {}", shown, e))?;
            con_ron_dump::parse_pins(&text).map_err(|e| format!("{}: {}", shown, e))
        }
        None => match pins_decode::decode_embedded() {
            Ok(ps) => Ok(ps),
            // Unreachable unless the crate was built with a text
            // `scripts/gen-pins.sh` did not write: exit 3, an internal
            // failure, never a verdict on the input.
            Err(e) => Err(format!("embedded pin text: {}", message(&e))),
        },
    }
}

// ---------------------------------------------------------------------------
// Rendering: the labels the arena has to read back
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ParsedC.lean:255-264 declCLabel
/// con-leche: ConLeche/Driver/CheckMain.lean:47-51 declCName
/// A record's display label, the cited six arms with the names READ BACK out
/// of the store: a handle is not a name until the store is asked, which is the
/// one thing every rendering in this crate has to do that con-leche's does not.
/// A dangling handle renders as `?` rather than failing — this is a log line,
/// never a verdict.
pub fn decl_label(pers: &PersTier, ar: &EStore, d: &IDeclaration) -> String {
    let (kind, n) = match d {
        IDeclaration::AxiomDecl(cv) => ("axiom", name_of(pers, ar, &cv.name)),
        IDeclaration::DefnDecl(cv, _, _) => ("def", name_of(pers, ar, &cv.name)),
        IDeclaration::ThmDecl(cv, _) => ("theorem", name_of(pers, ar, &cv.name)),
        IDeclaration::OpaqueDecl(cv, _) => ("opaque", name_of(pers, ar, &cv.name)),
        IDeclaration::IndDecl(block, _) => (
            "inductive",
            match block.first() {
                Some(ci) => name_of(pers, ar, &ienv::i_constant_info_name(ci)),
                None => "[anonymous]".to_string(),
            },
        ),
        IDeclaration::QuotDecl(_, cv) => ("quot", name_of(pers, ar, &cv.name)),
    };
    format!("{} {}", kind, n)
}

/// con-leche: none — `Name.toString` of a handle, for a log line
/// A name handle, rendered.  `con_ron_core::arena::env::read_name` is the
/// readback and `crate::render::name_str` the rendering; a handle the store
/// does not know renders as `?`.
pub fn name_of(pers: &PersTier, ar: &EStore, h: &con_ron_core::arena::handle::NIdx) -> String {
    match ienv::read_name(pers, ar, h) {
        Ok(n) => crate::render::name_str(&n),
        Err(_) => "?".to_string(),
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool
/// The worker count a run reports and the pool spawns: the cited
/// `max 1 (min jobs m)`.
pub fn workers_for(jobs: u64, m: usize) -> usize {
    let w = if (jobs as usize) < m { jobs as usize } else { m };
    if w < 1 {
        1
    } else {
        w
    }
}

// ---------------------------------------------------------------------------
// The check phase (`Driver/CheckPool.lean`, `Driver/Run.lean`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Run.lean:74-97 checkDeclsIO
/// What a caller wants to know between the steps of the run — the heartbeat's
/// lines, with the store passed to every method because a handle is not a
/// label until the store is asked.  Every method defaults to nothing, so a
/// caller implements the lines it prints and no more.  An observer only ever
/// holds `&` the state, so it cannot change an outcome.
pub trait PhaseObserver {
    /// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
    /// The index build is about to start (`tIndex`).
    fn index_starts(&mut self) {}

    /// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
    /// The parse is done, the index built: `con-ron: parse done: …`.
    fn parse_done(&mut self, _pers: &PersTier, _ar: &EStore, _fold_records: usize) {}

    /// con-leche: ConLeche/Driver/Run.lean:48-52 checkStarts
    /// The check phase starts: `m` jobs on `workers` workers.
    fn check_starts(&mut self, _m: usize, _workers: usize) {}

    /// con-leche: ConLeche/Driver/CheckPool.lean:165-170 jobBegin
    /// Does this observer print a line per check?  The driver asks ONCE, before
    /// the pool spawns: off, no worker touches the completed-count or the
    /// observer lock at all, which is the difference between a plain run and
    /// the `--progress` lane.
    fn wants_check_lines(&self) -> bool {
        false
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:96-114 checkHeartbeat
    /// After the `done`-th of `m` jobs completed, job `k` the one just done.
    fn check_after(&mut self, _pers: &PersTier, _ar: &EStore, _done: usize, _m: usize, _ds: &Vec<IDeclaration>, _k: usize) {}

    /// con-leche: ConLeche/Driver/Run.lean:54-72 checkDone
    /// The check phase ended: at the first failure in fold order, or with every
    /// job passed (`None`).
    fn check_done(&mut self, _m: usize, _failure: Option<u64>) {}
}

/// con-leche: ConLeche/Driver/Run.lean:74-97 checkDeclsIO
/// The observer a plain run (no `--progress`) hands the driver: it prints
/// nothing and wants no check lines, so no worker touches the completed-count
/// or the observer lock at all.  ONE lane serves both runs.
pub struct Silent;

/// con-leche: ConLeche/Driver/Run.lean:74-97 checkDeclsIO
impl PhaseObserver for Silent {}

/// con-leche: ConLeche/Driver/CheckPool.lean:172-183 jobEnd
/// The heartbeat's line after job `k`, on the worker that ran it:
/// `parallel_all`'s `after` hook.  `heartbeat` is the cited `pace.on` guard:
/// off, no worker touches the counter or the observer lock at all.
///
/// **The bump and its line are ONE critical section** (the cited `jobEnd`):
/// the completed-count and the observer share one `Mutex`, so a worker cannot
/// be descheduled between incrementing the count and printing it, which used
/// to let a later count's line overtake its own (`check 1, 3, 2`, measured
/// under load).  Under the one lock the lines leave in count order, whatever
/// the scheduling.
#[allow(clippy::too_many_arguments)]
fn check_line<O: PhaseObserver>(
    heartbeat: bool,
    lock: &Mutex<(usize, &mut O)>,
    tier: &PersTier,
    w: &AState,
    m: usize,
    ds: &Vec<IDeclaration>,
    k: usize,
) {
    if heartbeat {
        // A poisoned lock means another worker panicked while printing; the
        // panic is the report and this line is dropped.
        if let Ok(mut g) = lock.lock() {
            g.0 += 1;
            let n = g.0;
            g.1.check_after(tier, &w.store, n, m, ds, k);
        }
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:143-146 collect
/// The check phase's answer as a verdict: `parallel_all`'s first failing job,
/// whose error carries its fold position, and the pool's own failures (a
/// missing result, a panicked worker) as internal errors — exit 3, never a
/// verdict on the input.
pub fn pool_verdict(r: Result<(), ParallelError<(CheckError, u64)>>) -> Result<(), (CheckError, u64)> {
    let internal = |msg: String| con_ron_core::kernel::core_types::internal(msg.chars().map(|c| c as u32).collect());
    match r {
        Ok(()) => Ok(()),
        Err(ParallelError::Step(_, e)) => Err(e),
        Err(ParallelError::Missing(k)) => Err((internal(format!("check phase: no result for job {}", k)), k as u64)),
        Err(ParallelError::Panicked) => Err((internal("check phase: a worker failed".to_string()), 0)),
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
/// con-leche: ConLeche/Driver/Run.lean:74-97 checkDeclsIO
/// con-leche: ConLeche/Driver/CheckPool.lean:199-227 checkPool
/// **The driver after the parse**: the stream's index, built once from the
/// records alone, frozen, and every record's job on the pool — a straight line
/// of calls with the observer's lines between them, at every job count.  Each
/// step is one premise of the capstone:
///
/// | step | here | con-leche |
/// |---|---|---|
/// | index | `stream_index::build_index(pers, st, stream_index_empty(), ds, 0)` | `Jobs.build` (`buildIndex`) |
/// | boundary | `checker::freeze_tier(&mut st.store, ix)` | `Runtime.markPersistent` |
/// | check | `pool::parallel_all(m, workers, ‖ worker_state(pins), ‖w, k‖ run_job(&tier, w, mode, pins, ds, k), …)` | `checkPool` over `runAt` |
/// | after | `checker::thaw_tier(&mut st.store, tier)` | — |
///
/// `init` and `step` are calls into the verified crate; `parallel_all` is the
/// one trusted piece, and its contract (`pool.rs`'s note) is that on `Ok` every
/// job was run by some worker, each worker folding `run_job` over the jobs it
/// claimed, in increasing order, on ONE `worker_state`.  The pool reports the
/// least failing index, so the first failure in fold order is the verdict at
/// every job count.  There is no install phase: a record's guards run in its
/// own job, so a failing guard at record 9 no longer overtakes a failing value
/// at record 5.
///
/// **The boundary is where the tier is FROZEN.**  The index is built on the
/// driver's own store, with no scratch tier open, so every handle it holds is
/// persistent; `checker::freeze_tier` moves the four stores' persistent tables
/// and the index into one `PersTier`, handed back `frozen`, and a worker's own
/// store is frozen too (`checker::worker_state`), so every append there is a
/// scratch append.  So `n` workers share one index and one term DAG and own
/// nothing but a scratch tier, their caches and a copy of the pin handles.
pub fn check_decls_driver<O: PhaseObserver + Send>(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    jobs: u64,
    obs: &mut O,
) -> Result<(), (CheckError, u64)> {
    check_decls_driver_with(pers, st, ds, jobs, obs, || (), |tier, w, _x, k| {
        checker::run_job(tier, w, mode, pins, ds, k)
    })
}

/// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
/// con-leche: ConLeche/Driver/CheckMain.lean:152-169 checkOleansG
/// `check_decls_driver` with a worker state of the caller's beside each
/// worker's `AState` (`init_x`, one per worker) and the caller's job: an
/// `--olean` run's workers keep the module region they read a theorem's value
/// from (`olean_job`, con-leche's `OleanWorker`), every other run's job is
/// `checker::run_job` with nothing beside it.
pub fn check_decls_driver_with<O, X, I, J>(
    pers: &PersTier,
    st: &mut AState,
    ds: &Vec<IDeclaration>,
    jobs: u64,
    obs: &mut O,
    init_x: I,
    job: J,
) -> Result<(), (CheckError, u64)>
where
    O: PhaseObserver + Send,
    I: Fn() -> X + Sync,
    J: Fn(&PersTier, &mut AState, &mut X, u64) -> Result<(), (CheckError, u64)> + Sync,
{
    // THE INDEX (the last step of the parse phase): every record's constants and
    // tables, a name's first entry winning, read off the records alone.
    obs.index_starts();
    let ix: IStreamIndex = stream_index::build_index(pers, st, stream_index::stream_index_empty(), ds, 0)?;
    obs.parse_done(pers, &st.store, ds.len());
    let m = ds.len();
    let workers = workers_for(jobs, m);
    obs.check_starts(m, workers);
    // THE BOUNDARY: the persistent tier and the index leave the state and become
    // a value every worker reads.  `st` keeps its (empty) store, its tables
    // moved out, so the observer can still read a label back through the tier.
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    // THE CHECK PHASE: the job at every record, on `workers` threads, each
    // folding it over the jobs it claims on ONE `worker_state` — the verdict and
    // the record a rejection names are the one-worker walk's at every `--jobs`.
    let heartbeat = obs.wants_check_lines();
    let lock: Mutex<(usize, &mut O)> = Mutex::new((0, obs));
    let r = parallel_all(
        m,
        workers,
        || (checker::worker_state(&st.pins), init_x()),
        |w: &mut (AState, X), k| job(&tier, &mut w.0, &mut w.1, k as u64),
        |w: &(AState, X), k| check_line(heartbeat, &lock, &tier, &w.0, m, ds, k),
    );
    let obs: &mut O = match lock.into_inner() {
        Ok((_, o)) => o,
        Err(e) => e.into_inner().1,
    };
    // AND THE TIER GOES BACK.  Everything after the check — the verdict line's
    // declaration label, the failing record's name — reads a handle back out of
    // `st`, and a state left frozen over a tier that has gone out of scope
    // answers `None` to every one of them.
    let _ix: IStreamIndex = checker::thaw_tier(&mut st.store, tier);
    let v = pool_verdict(r);
    obs.check_done(m, match &v {
        Err((_, pos)) => Some(*pos),
        Ok(()) => None,
    });
    v
}

/// con-leche: ConLeche/Driver/CheckMain.lean:120-133 oleanJobRun
/// **One job of an `--olean` run**, from the module region the worker kept: a
/// theorem whose value is still in its file (`.thmDecl cv (.bvar code)`, a
/// reference) reads it into the worker's scratch tier and is checked with it in
/// place, any other record as it stands.  The value goes with the tier when the
/// job ends.  The read is inside the job's bracket (`enter_record` …
/// `leave_record`, `stream_index::record_job`'s), so that what it interns is
/// the job's.
#[allow(clippy::too_many_arguments)]
pub fn olean_job(
    tier: &PersTier,
    w: &mut AState,
    cache: &mut con_ron_core::frontend::olean::records::ValueCache,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    rd: &con_ron_core::frontend::olean::records::OleanRead,
    sp: &Vec<Vec<u32>>,
    k: u64,
) -> Result<(), (CheckError, u64)> {
    let d = match ds.get(k as usize) {
        Some(d) => d,
        None => return checker::run_job(tier, w, mode, pins, ds, k),
    };
    let code: Option<u64> = match d {
        IDeclaration::ThmDecl(_, v) => w.store.view_bvar(tier, v),
        _ => None,
    };
    match (code, d) {
        (Some(code), IDeclaration::ThmDecl(cv, _)) => {
            con_ron_core::arena::core::enter_record(w);
            let r = match con_ron_core::frontend::olean::records::read_value(
                &crate::olean_fs::StdFs,
                &rd.pins,
                tier,
                &mut w.store,
                sp,
                &rd.values,
                cache,
                code,
            ) {
                Err(e) => Err((e, k)),
                Ok(v) => {
                    let pd = IDeclaration::ThmDecl(ienv::i_constant_val_dup(cv), v);
                    match stream_index::record_check(tier, w, mode, pins, k, &pd) {
                        Err(e) => Err((e, k)),
                        Ok(()) => Ok(()),
                    }
                }
            };
            con_ron_core::arena::core::leave_record(w);
            r
        }
        _ => checker::run_job(tier, w, mode, pins, ds, k),
    }
}

// ---------------------------------------------------------------------------
// The progress heartbeat (`--progress[=N|P%|Ss]`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Run.lean:26-30 beat
/// con-leche: ConLeche/Driver/CheckPool.lean:96-114 checkHeartbeat
/// **The heartbeat**, con-leche's line shapes with `con-ron: ` for the prefix:
///
/// ```text
/// con-ron: reading <label>
/// con-ron: parse done: <N> fold records — … t=<s>s (parse <s>s)
/// con-ron: checking: <N> declarations on <W> workers t=<s>s
/// con-ron: check <n> (<p>%)[ <decl>] t=<s>s
/// con-ron: check done: <N> declarations t=<s>s (check <s>s)
/// con-ron: done: parse <p>s, check <c>s, <W> worker[s] t=<s>s
/// ```
///
/// A check line is printed AFTER the check, so "a check that is running is not
/// on any line, the gap between two lines is where it sits"; it names its
/// declaration only at a pace that gives every check a line (`pace_trace`).
/// Deviation: con-leche's ` busy=…, oldest …` suffix and its `stats:` lines are
/// not ported (performance reports the port's driver has never printed); the
/// parse line also gives the store's node counts.
pub struct Heartbeat {
    /// How often it speaks; `Pace::Off` is no flag and no heartbeat.
    pub pace: Pace,
    /// The start of the run, which every `t=` is measured from.
    pub t0: Instant,
    /// When the clock pace last spoke, in ms since `t0` (`Pace.clock`).
    pub last: u128,
    /// The file's records and the prelude records synthesised, for the parse
    /// line.
    pub file_records: usize,
    pub synthesised: u64,
    /// When the index build started and the parse ended (index included), in ms
    /// since `t0`: `checkMainG`'s `tIndex` and `tParse`.
    pub t_index: u128,
    pub t_parse: u128,
    /// The worker count the check ran on, for the summary.
    pub workers: usize,
}

/// con-leche: ConLeche/Driver/Run.lean:26-30 beat
/// The heartbeat's own lines.
impl Heartbeat {
    /// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
    /// A heartbeat at `pace`, starting now.
    pub fn new(pace: Pace, t0: Instant) -> Heartbeat {
        Heartbeat {
            pace,
            t0,
            last: 0,
            file_records: 0,
            synthesised: 0,
            t_index: 0,
            t_parse: 0,
            workers: 1,
        }
    }

    /// con-leche: none — `IO.monoMsNow`, in milliseconds since `t0`.
    fn now(&self) -> u128 {
        self.t0.elapsed().as_millis()
    }

    /// con-leche: ConLeche/Driver/Run.lean:26-30 beat
    /// A line, when the heartbeat is on.
    pub fn beat(&self, line: &str) {
        if pace_on(&self.pace) {
            eprintln!("con-ron: {}", line);
        }
    }

    /// con-leche: ConLeche/Driver/Run.lean:32-34 readStarts
    /// The first line of a run: what it is reading.
    pub fn read_starts(&self, label: &str) {
        self.beat(&format!("reading {}", label));
    }

    /// con-leche: ConLeche/Frontend/Pace.lean:38-48 Pace.due
    /// Is a line due at item `k` of `total`, counted from 1?  The count arms are
    /// the core's (`pace_due_count`); the clock arm is here.
    fn due(&mut self, k: u64, total: u64) -> bool {
        match &self.pace {
            Pace::Seconds(s) => {
                let now = self.now();
                if self.last + (*s as u128) * 1000 <= now {
                    self.last = now;
                    true
                } else {
                    false
                }
            }
            p => pace_due_count(p, k, total),
        }
    }
}

/// con-leche: ConLeche/Driver/CheckPool.lean:96-114 checkHeartbeat
/// con-leche: ConLeche/Driver/Run.lean:48-52 checkStarts
/// The heartbeat as an observer of the run.
impl PhaseObserver for Heartbeat {
    /// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
    /// `tIndex`.
    fn index_starts(&mut self) {
        self.t_index = self.now();
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:224-376 checkMainG
    /// `con-ron: parse done: …`: the parse and the index are done.  Records
    /// `t_parse`, so the summary can price the parse whatever happens next.
    fn parse_done(&mut self, pers: &PersTier, ar: &EStore, fold_records: usize) {
        self.t_parse = self.now();
        self.beat(&format!(
            "parse done: {} fold records — the file's {}, {} built-in \
             prelude records synthesised; store {} expression, {} level, {} name \
             nodes t={}s (parse {}s)",
            fold_records,
            self.file_records,
            self.synthesised,
            ar.node_count(pers),
            ar.ls().node_count(pers),
            ar.ns().node_count(pers),
            ms_secs(self.t_parse),
            ms_secs(self.t_parse)
        ));
    }

    /// con-leche: ConLeche/Driver/Run.lean:48-52 checkStarts
    /// `con-ron: checking: <N> declarations on <W> workers t=<s>s`.
    fn check_starts(&mut self, m: usize, workers: usize) {
        self.workers = workers;
        self.last = self.now();
        self.beat(&format!(
            "checking: {} declarations on {} workers t={}s",
            m,
            workers,
            ms_secs(self.now())
        ));
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:165-170 jobBegin
    /// The heartbeat prints check lines exactly when it is on.
    fn wants_check_lines(&self) -> bool {
        pace_on(&self.pace)
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:96-114 checkHeartbeat
    /// `con-ron: check <n> (<p>%)[ <decl>] t=<s>s`, after the check, when the
    /// pace says a line is due.
    fn check_after(&mut self, pers: &PersTier, ar: &EStore, done: usize, m: usize, ds: &Vec<IDeclaration>, k: usize) {
        if self.due(done as u64, m as u64) {
            let label = if !pace_trace(&self.pace) {
                String::new()
            } else {
                match ds.get(k) {
                    Some(d) => format!(" {}", decl_label(pers, ar, d)),
                    None => format!(" record {}", k),
                }
            };
            let pct = done * 100 / if m == 0 { 1 } else { m };
            self.beat(&format!(
                "check {} ({}%){} t={}s",
                done,
                pct,
                label,
                ms_secs(self.now())
            ));
        }
    }

    /// con-leche: ConLeche/Driver/Run.lean:54-72 checkDone
    /// The end of the check phase, whatever its result, and the summary.
    fn check_done(&mut self, m: usize, failure: Option<u64>) {
        let now = self.now();
        match failure {
            Some(pos) => self.beat(&format!(
                "check failed at fold position {} t={}s (check {}s)",
                pos,
                ms_secs(now),
                ms_secs(now - self.t_parse)
            )),
            None => self.beat(&format!(
                "check done: {} declarations t={}s (check {}s)",
                m,
                ms_secs(now),
                ms_secs(now - self.t_parse)
            )),
        }
        self.beat(&format!(
            "done: parse {}s, check {}s, {} worker{} t={}s",
            ms_secs(self.t_parse),
            ms_secs(now - self.t_parse),
            self.workers,
            if self.workers == 1 { "" } else { "s" },
            ms_secs(now)
        ));
    }
}
// ---------------------------------------------------------------------------
// The verdict lines
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/CheckMain.lean:171-222 verdictG
/// **The accept line**, `crate::driver::verdict_accept`'s with this
/// binary's name: `records` is the FILE's declaration-record count — what the
/// parse produced — and nothing the preparation does moves it.  It is not the
/// environment's constant count, which is a property of the representation
/// and not of the input.  Printed on STDOUT, where a caller greps for a
/// verdict.
pub fn verdict_accept(records: u64, mode_tag: &str) -> u8 {
    println!(
        "con-ron: accepted {} declarations ({})",
        records, mode_tag
    );
    0
}

/// con-leche: ConLeche/Driver/CheckMain.lean:171-222 verdictG
/// The failure line: the error, the declaration it names and its FOLD
/// position, the mode, the elapsed time.  There is no second pass — the fold's
/// error carries the position, so the label is read off the record array the
/// driver already holds.
///
/// `i` is the fold position and is NOT the file's record index (the prepared
/// list starts with the prelude's records); the declaration NAME on the line
/// is the portable handle.  con-leche's own generated-`_model`-record owner
/// naming is gone with the modeller (task #105).
pub fn verdict_failure(
    pers: &PersTier,
    ar: &EStore,
    ds: &Vec<IDeclaration>,
    e: &CheckError,
    i: u64,
    mode_tag: &str,
    t0: Instant,
) -> u8 {
    let code = exit_code(e);
    let loc = match ds.get(i as usize) {
        None => format!(" [at fold position {}]", i),
        Some(d) => format!(" [at {}, fold position {}]", decl_label(pers, ar, d), i),
    };
    eprintln!(
        "con-ron: {}: {}{} ({}) t={}s",
        verdict_word(code),
        message(e),
        loc,
        mode_tag,
        ms_secs(t0.elapsed().as_millis())
    );
    code
}

// ---------------------------------------------------------------------------
// The streaming reader
//
// `ConLeche/Frontend/CheckerIO.lean`'s `foldChunks`, the serial parse's fold
// over a file's reads: the core's `export_c::parse_source` over the file
// handle.  Only the READS are here, for `crate::driver`'s reason:
// `IO.FS.Handle.read` has no model, and a theorem about the file is a
// theorem about its bytes.  Deviation: con-leche's reads are positional, through
// its `CheckerIO` class; these are sequential and forward, and there is no class.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/CheckerIO.lean:179-187 foldChunks
/// **The file handle as the parse's `ChunkSource`**: each `next_chunk` is one
/// `read_up_to` of `chunk` bytes, strictly forward, handed over whole; the
/// first empty read is the end of the input.  A failed read ends the input
/// the same way and is KEPT here, and `parse_export_handle_d` reports it in
/// place of whatever the parse of the truncated input said — so a read error
/// is exit 3, never a verdict, as before the loop moved.
pub struct HandleSource<'a, R: Read> {
    /// The open reader.
    pub h: &'a mut R,
    /// The buffer size, `export_c::CHUNK_SIZE` in the binary.
    pub chunk: usize,
    /// The nonempty buffers handed out so far, for the heartbeat.
    pub chunks: u64,
    /// The first read failure, if any.
    pub err: Option<std::io::Error>,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:179-187 foldChunks
impl<'a, R: Read> ChunkSource for HandleSource<'a, R> {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:179-187 foldChunks
    /// One read of up to `chunk` bytes; empty at the end or on a failure.
    fn next_chunk(&mut self) -> Vec<u8> {
        if self.err.is_some() {
            return Vec::new();
        }
        let mut buf: Vec<u8> = vec![0u8; self.chunk];
        match read_up_to(self.h, &mut buf) {
            Ok(n) => {
                buf.truncate(n);
                if n > 0 {
                    self.chunks += 1;
                }
                buf
            }
            Err(e) => {
                self.err = Some(e);
                Vec::new()
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:179-187 foldChunks
/// Streaming direct parse off an open reader, into the persistent tier of
/// `ar`: the VERIFIED reader loop `export_c::parse_source` over the handle
/// (task #97-P5-Driver moved the loop into the core; what is left here is
/// the reads).  The chunk count comes back for the heartbeat, as the Lean
/// twin's `readFold` returns it.
pub fn parse_export_handle_d<R: Read>(
    pers: &PersTier,
    ar: &mut AState,
    h: &mut R,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    let mut src = HandleSource { h, chunk, chunks: 0, err: None };
    let r = export_c::parse_source(pers, ar, &mut src);
    match src.err {
        Some(e) => Err(e),
        None => Ok((r, src.chunks)),
    }
}

/// con-leche: ConLeche/Driver/StreamParse.lean:114-125 parseStreamG
/// con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
/// Streaming direct parse of a file.  The input must be a regular file, and
/// that is decided before it is opened, as the class's `fileSize` decides it:
/// opening a FIFO with no writer would block.  con-leche goes on with positional
/// reads and its rounds parse; this one reads forward, one chunk at a time.
pub fn parse_export_stream_d(
    pers: &PersTier,
    ar: &mut AState,
    path: &str,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    if !std::fs::metadata(path)?.is_file() {
        return Err(std::io::Error::other("not a regular file"));
    }
    let mut f = std::fs::File::open(path)?;
    parse_export_handle_d(pers, ar, &mut f, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **The reader loop is `parse_chunks` with the reads interleaved.**  The
    /// core proves nothing about the reader — it cannot, `IO.FS.Handle.read`
    /// has no model — so the agreement is a test: at every chunk size,
    /// including sizes that cut inside a line and one byte at a time, the
    /// streaming parse and the pure fold over the same chunks produce the same
    /// records.  `crate::driver`'s own test, over the arena's parser.
    #[test]
    fn the_reader_is_parse_chunks_with_the_reads() {
        let pers: &PersTier = &PersTier::empty();
        let s = concat!(
            "{\"meta\":{\"exporter\":{\"name\":\"lean4export\"}}}\n",
            "{\"in\":1,\"str\":{\"pre\":0,\"str\":\"A\"}}\n",
            "{\"ie\":0,\"sort\":0}\n",
            "{\"axiom\":{\"isUnsafe\":false,\"levelParams\":[],\"name\":1,\"type\":0}}\n"
        );
        let b = s.as_bytes();
        for chunk in [1usize, 2, 7, 8, 13, 64, 4096] {
            let mut ar = AState::init(EStore::empty());
            let mut r = std::io::Cursor::new(b.to_vec());
            let (streamed, _) =
                parse_export_handle_d(pers, &mut ar, &mut r, chunk)
                    .expect("no io error");
            let streamed = streamed
                .unwrap_or_else(|(e, l)| panic!("chunk {} line {}: {}", chunk, l, message(&e)));
            let mut ar2 = AState::init(EStore::empty());
            let cs: Vec<Vec<u8>> = b.chunks(chunk).map(|c| c.to_vec()).collect();
            let pure = export_c::parse_chunks(pers, &mut ar2, &cs)
                .unwrap_or_else(|(e, l)| {
                    panic!("pure chunk {} line {}: {}", chunk, l, message(&e))
                });
            assert_eq!(streamed.decls.len(), pure.decls.len(), "chunk {}", chunk);
            assert_eq!(streamed.decls.len(), 1, "chunk {}", chunk);
            assert_eq!(ar.store.node_count(pers), ar2.store.node_count(pers), "chunk {}", chunk);
        }
    }

    /// The flag values.
    #[test]
    fn rendering_and_flag_values() {
        assert!(matches!(progress_pace("1"), Ok(Pace::Every(1))));
        assert!(matches!(progress_pace("5%"), Ok(Pace::Percent(5))));
        assert!(matches!(progress_pace("10s"), Ok(Pace::Seconds(10))));
        assert!(progress_pace("0").is_err());
        assert!(progress_pace("0s").is_err());
        assert!(progress_pace("101%").is_err());
        assert!(progress_pace("x").is_err());
        assert_eq!(jobs_count("8"), Ok(8));
        assert!(jobs_count("0").is_err());
        // the worker count is `workers_for` and nothing else
        // (task #97-P6-6b): the two binaries cannot drift on `--jobs`
        assert_eq!(workers_for(8, 100), 8);
        assert_eq!(workers_for(8, 3), 3);
        assert_eq!(workers_for(1, 0), 1);
        assert_eq!(workers_for(8, 100), workers_for(8, 100));
    }

    /// **The phase boundary is invisible to every reader outside phase B**
    /// (task #97-P6-6b; the two functions are the verified crate's since task
    /// #97-P5-Driver).  `freeze_tier` takes the persistent tier out of the
    /// store and `thaw_tier` puts it back; between them a worker reads the
    /// tier it was handed, and after them the store answers exactly as it did
    /// before — which is what the verdict line needs, because it renders the
    /// failing record's NAME out of the store after the fold has returned.
    /// The first version of the pool dropped the tier at the end of the
    /// driver and printed `at theorem ?`; this is the regression.
    #[test]
    fn freezing_and_thawing_leave_every_handle_readable() {
        let empty: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        let anon = match con_ron_core::arena::monad::intern_n_node(
            empty,
            &mut st,
            con_ron_core::arena::store::NNodeView::Anonymous,
        ) {
            Ok(h) => h,
            Err(_) => panic!("the anonymous name interns"),
        };
        let n = match con_ron_core::arena::monad::intern_n_node(
            empty,
            &mut st,
            con_ron_core::arena::store::NNodeView::Str(anon, vec![0x61, 0x64, 0x64]),
        ) {
            Ok(h) => h,
            Err(_) => panic!("`add` interns"),
        };
        assert_eq!(name_of(empty, &st.store, &n), "add");
        // frozen: the store's own tables are out and the tier answers
        let tier = checker::freeze_tier(&mut st.store, con_ron_core::arena::stream_index::stream_index_empty());
        assert!(tier.frozen);
        assert_eq!(name_of(&tier, &st.store, &n), "add");
        // and a worker, whose store is its own, reads it too
        let w = checker::worker_state(&st.pins);
        assert_eq!(name_of(&tier, &w.store, &n), "add");
        // thawed: the store is what it was
        let _ = checker::thaw_tier(&mut st.store, tier);
        assert!(!st.store.scratch_on);
        assert_eq!(name_of(empty, &st.store, &n), "add");
    }
}
