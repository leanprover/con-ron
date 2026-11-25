//! `driver` — what the binary's instance (`std_io::StdIo`) renders and runs
//! with, from con-leche's `Driver/{Cli,CheckMain,Run,CheckPool}.lean`: the
//! checking threads' stack, the flag values' messages (the verified parser's
//! `Bad` values are rendered with these functions, so the two cannot drift),
//! the exit-code mapping, the hardware worker count, the `--progress`
//! heartbeat, the worker map's verdict, the verdict lines and the labels the
//! arena has to read back.  The driver itself is the verified
//! `con_ron_core::driver`; everything here is outside the theorems.
//!
//! ## THE EXIT CODES
//!
//! | exit | verdict | meaning |
//! |---|---|---|
//! | 0 | `accepted N declarations` | every declaration checked; `N` counts the file's declaration records |
//! | 1 | `rejected` | a declaration is invalid |
//! | 2 | `declined` | the checker positively detected a feature it does not support, and says which |
//! | 3 | error | bad usage, malformed input, or an internal failure of unclear cause |

use std::time::Instant;

use con_ron_core::arena::env as ienv;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::frontend::pace::{pace_due_count, pace_on, pace_trace, Pace};
use con_ron_core::arena::store::EStore;

use con_ron_core::kernel::core_types::CheckError;

use con_ron_core::arena::store::PersTier;
use con_ron_core::ron::nat::{self, Nat};

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

/// con-leche: none — the Lean runtime's `LEAN_STACK_SIZE_KB`, read at the start
/// for every thread's stack
/// **The checking threads' stack**: `LEAN_STACK_SIZE_KB` KiB where it is set to
/// a positive number (as a Lean binary reads it: the scheduler's
/// `--worker-stack-size` sets it for its workers), else `STACK_BYTES`.
pub fn stack_bytes() -> usize {
    match std::env::var("LEAN_STACK_SIZE_KB").ok().and_then(|v| v.parse::<usize>().ok()) {
        Some(k) if k > 0 => k.saturating_mul(1024),
        _ => STACK_BYTES,
    }
}

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

/// con-leche: ConLeche/Cached/ParsedC.lean:332-334 msSecs
/// Milliseconds as seconds.  Also a deliberate skip in the core, for
/// `declCLabel`'s reason.  Deviation: three decimals rather than con-leche's
/// one.
pub fn ms_secs(ms: u128) -> String {
    format!("{}.{:03}", ms / 1000, ms % 1000)
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

/// con-leche: ConLeche/Driver/Cli.lean:302-521 runArgs
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

/// con-leche: ConLeche/Driver/Cli.lean:104-114 maxNatSizeArg
/// The maximum `Nat` size, read off the `--max-nat-size=<bytes>` flag: a
/// decimal byte count, the official kernel's `LEAN_NAT_MAX_SIZE` (the largest
/// `Nat` numeral the checker takes in or computes; a larger one rejects the
/// declaration).  Any size, read as con-leche's `String.toNat?` reads it
/// (`is_nat`: digits, `_` allowed between two of them); a non-numeral is a
/// usage error (exit 3).  Without the flag the maximum size is the official
/// default, 128 MiB (`arena::pins::max_nat_size_default`).
pub fn max_nat_size_arg(v: &str) -> Result<Nat, String> {
    if !is_nat(v) {
        Err(format!(
            "--max-nat-size takes a byte count (a decimal numeral), got {}",
            crate::render::display_str(v)
        ))
    } else {
        let ten = nat::from_u64(10);
        Ok(v.bytes().filter(|&c| c != b'_').fold(nat::zero(), |acc, c| {
            nat::add(&nat::mul(&acc, &ten), &nat::from_u64((c - b'0') as u64))
        }))
    }
}

/// con-leche: none — Lean core's `String.Slice.isNat`, which `String.toNat?` tests first
/// Whether `v` is a decimal numeral as Lean's `String.toNat?` takes one: not
/// empty, ASCII digits, each `_` right after a digit, ending in a digit.
pub fn is_nat(v: &str) -> bool {
    let mut last_was_digit = false;
    for c in v.chars() {
        if c == '_' {
            if !last_was_digit {
                return false;
            }
            last_was_digit = false;
        } else if c.is_ascii_digit() {
            last_was_digit = true;
        } else {
            return false;
        }
    }
    last_was_digit
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

// ---------------------------------------------------------------------------
// Rendering: the labels the arena has to read back
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ParsedC.lean:336-345 declCLabel
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

// ---------------------------------------------------------------------------
// The check phase (`Driver/CheckPool.lean`, `Driver/Run.lean`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Run.lean:74-99 checkDeclsIO
/// What a caller wants to know between the steps of the run — the heartbeat's
/// lines, with the store passed to every method because a handle is not a
/// label until the store is asked.  Every method defaults to nothing, so a
/// caller implements the lines it prints and no more.  An observer only ever
/// holds `&` the state, so it cannot change an outcome.  The cited
/// `checkDeclsIO` is at `justify = none` on this path (`hds` is `rfl`): no
/// solution is checked against.
pub trait PhaseObserver {
    /// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
    /// The index build is about to start (`tIndex`).
    fn index_starts(&mut self) {}

    /// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
    /// The parse is done, the index built: `con-ron: parse done: …`.
    fn parse_done(&mut self, _pers: &PersTier, _ar: &EStore, _fold_records: usize) {}

    /// con-leche: ConLeche/Driver/Run.lean:48-52 checkStarts
    /// The check phase starts: `m` jobs on `workers` workers.
    fn check_starts(&mut self, _m: usize, _workers: usize) {}

    /// con-leche: ConLeche/Driver/CheckPool.lean:177-182 jobBegin
    /// Does this observer print a line per check?  The driver asks ONCE, before
    /// the pool spawns: off, no worker touches the completed-count or the
    /// observer lock at all, which is the difference between a plain run and
    /// the `--progress` lane.
    fn wants_check_lines(&self) -> bool {
        false
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:106-125 checkHeartbeat
    /// After the `done`-th of `m` jobs completed, job `k` the one just done;
    /// `m` is the cited `total`, the phase's job count.
    fn check_after(&mut self, _pers: &PersTier, _ar: &EStore, _done: usize, _m: usize, _ds: &Vec<IDeclaration>, _k: usize) {}

    /// con-leche: ConLeche/Driver/Run.lean:54-72 checkDone
    /// The check phase ended: at the first failure in fold order, or with every
    /// job passed (`None`); `m` is the cited `n`, the phase's job count.
    fn check_done(&mut self, _m: usize, _failure: Option<u64>) {}
}

/// con-leche: ConLeche/Driver/CheckPool.lean:154-157 collect
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

// ---------------------------------------------------------------------------
// The progress heartbeat (`--progress[=N|P%|Ss]`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Run.lean:26-30 beat
/// con-leche: ConLeche/Driver/CheckPool.lean:106-125 checkHeartbeat
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
    /// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
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

/// con-leche: ConLeche/Driver/CheckPool.lean:106-125 checkHeartbeat
/// con-leche: ConLeche/Driver/Run.lean:48-52 checkStarts
/// The heartbeat as an observer of the run.
impl PhaseObserver for Heartbeat {
    /// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
    /// `tIndex`.
    fn index_starts(&mut self) {
        self.t_index = self.now();
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
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

    /// con-leche: ConLeche/Driver/CheckPool.lean:177-182 jobBegin
    /// The heartbeat prints check lines exactly when it is on.
    fn wants_check_lines(&self) -> bool {
        pace_on(&self.pace)
    }

    /// con-leche: ConLeche/Driver/CheckPool.lean:106-125 checkHeartbeat
    /// `con-ron: check <n> (<p>%)[ <decl>] t=<s>s`, after the check, when the
    /// pace says a line is due; `m` is the cited `total` (every record here).
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
    /// The end of the check phase, whatever its result, and the summary; `m`
    /// is the cited `n` (every record here).
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

/// con-leche: ConLeche/Driver/CheckMain.lean:179-231 verdictG
/// **The accept line**, `crate::driver::verdict_accept`'s with this
/// binary's name: `records` is the FILE's declaration-record count — what the
/// parse produced — and nothing the preparation does moves it.  It is not the
/// environment's constant count, which is a property of the representation
/// and not of the input.  Printed on STDOUT, where a caller greps for a
/// verdict.  The cited `who` (a module's worker's prefix) is `""` on this path.
pub fn verdict_accept(records: u64, mode_tag: &str) -> u8 {
    println!(
        "con-ron: accepted {} declarations ({})",
        records, mode_tag
    );
    0
}

/// con-leche: ConLeche/Driver/CheckMain.lean:179-231 verdictG
/// The failure line: the error, the declaration it names and its FOLD
/// position, the mode, the elapsed time.  There is no second pass — the fold's
/// error carries the position, so the label is read off the record array the
/// driver already holds.
///
/// `i` is the fold position and is NOT the file's record index (the prepared
/// list starts with the prelude's records); the declaration NAME on the line
/// is the portable handle.  con-leche's own generated-`_model`-record owner
/// naming is gone with the modeller (task #105).  The cited `who` is a compared
/// run's prefix for its solution's failure (`the solution S: `), `""` elsewhere;
/// after a `who` the error reads as con-leche renders it (`error_text`), so the
/// line says the solution's verdict in con-leche's words.
#[allow(clippy::too_many_arguments)]
pub fn verdict_failure(
    pers: &PersTier,
    ar: &EStore,
    ds: &Vec<IDeclaration>,
    e: &CheckError,
    i: u64,
    mode_tag: &str,
    t0: Instant,
    who: &str,
) -> u8 {
    let code = exit_code(e);
    let loc = match ds.get(i as usize) {
        None => format!(" [at fold position {}]", i),
        Some(d) => format!(" [at {}, fold position {}]", decl_label(pers, ar, d), i),
    };
    let what = if who.is_empty() {
        message(e)
    } else {
        format!("{}{}", who, error_text(e))
    };
    eprintln!(
        "con-ron: {}: {}{} ({}) t={}s",
        verdict_word(code),
        what,
        loc,
        mode_tag,
        ms_secs(t0.elapsed().as_millis())
    );
    code
}

/// con-leche: ConLeche/Kernel/Error.lean:36-40 _
/// A `CheckError` as con-leche prints it: its kind's words, then the payload.  The
/// port's fourth constructor reads `native: …`.
pub fn error_text(e: &CheckError) -> String {
    match e {
        CheckError::NotImplemented(_) => format!("not implemented yet: {}", message(e)),
        CheckError::Invalid(_) => format!("invalid: {}", message(e)),
        CheckError::Internal(_) => format!("internal error: {}", message(e)),
        CheckError::Native(_) => format!("native: {}", message(e)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::arena::checker;
    use con_ron_core::arena::monad::AState;

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
        // `--max-nat-size` reads as Lean's `String.toNat?`
        let size = |v: &str| max_nat_size_arg(v).map(|n| nat::to_u64(&n));
        assert_eq!(size("16"), Ok(Some(16)));
        assert_eq!(size("0"), Ok(Some(0)));
        assert_eq!(size("134_217_728"), Ok(Some(134217728)));
        assert_eq!(size("0016"), Ok(Some(16)));
        for bad in ["", "_1", "1_", "1__2", "-1", "+1", "0x10", "1e3", " 1"] {
            assert!(max_nat_size_arg(bad).is_err(), "{bad:?}");
        }
        assert_eq!(
            max_nat_size_arg("18446744073709551616").map(|n| nat::to_u64(&n)),
            Ok(None)
        );
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
