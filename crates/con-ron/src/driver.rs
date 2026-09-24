//! `driver` — con-leche's `Main.lean`, over the ARENA (tasks #37, #48 and
//! #97-P4f), and the Rust side of the Lean twin's
//! `proof/ConRon/Arena/Main.lean`.
//!
//! The module is con-leche's `Main.lean` in `Main.lean`'s order: the reads,
//! the two phases with the boundary visible, the `--progress` heartbeat behind
//! one observer trait, the verdict lines, the exit-code mapping, and the flag
//! parsers.  Task #97-SWAP put it here, under the name the shipping driver
//! always had: it was `crates/con-ron-arena/src/driver.rs` through the arena
//! campaign, beside the `Expr`-tree driver it has now replaced, and the
//! eleven representation-free items it used to import across the crate line
//! ([`exit_code`], `verdict_word`, `message`, `ms_secs`, `progress_stride`,
//! `jobs_count`, `default_jobs`, [`workers_for`], `mark_persistent_note`,
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
//! 3. **Phase B's bracket is `check_pending`'s**, which turns the scratch tier
//!    on and drops it.  A driver that checked records itself without it would
//!    grow the scratch tier without bound; the loop below calls it once per
//!    record and nothing else opens a tier.
//! 4. **`--jobs=<n>` runs [`crate::pool`]** (task #97-P6-6b), which is
//!    DESIGN.md §8.3's arrangement and needs no atomics: the persistent tier
//!    is immutable in phase B, so it is shared by reference, and each worker
//!    owns a scratch tier, its own caches and a copy of the pin handles.
//!    Phase B reads `fe` and the pending list and writes only the per-record
//!    state, which is what lets the pool slot in where the `while` is.
//! 5. **`--no-mark-persistent` has a stronger reason to be a no-op here.**
//!    The mark it turns off is a Lean-runtime reference-counting device, and
//!    the checking path has no reference counts at all — a term is a `u32`
//!    handle into a `Vec` (DESIGN.md §8.5) — so [`mark_persistent_note`] says
//!    so rather than letting a log read as an A/B lane that was never run.
//!
//! ## The read loop
//!
//! [`parse_export_handle_d`] is `ConLeche/Frontend/ExportC.lean:903-931`'s
//! `parseExportHandleD`: the VERIFIED loop `export_c::parse_source` (task
//! #97-P5-Driver moved it into the core) over [`HandleSource`], the handle
//! read strictly forward 4 MiB at a time, each buffer fed to `chunk_step` and
//! dropped, the first empty read its end of file and `chunk_finish` the
//! close.  Never seeked, never re-opened, never asked for its size — so the
//! source may be a pipe and no scratch file exists (con-leche task #180).
//! `parse_source` is `export_c::parse_chunks` over the chunks read — a
//! theorem (`Refine2/Frontend/Source.lean`), under the one hypothesis about
//! the input the binary trusts: that the reads are the file's bytes, in
//! order.

use std::io::Read;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;
use std::sync::Mutex;
use std::time::Instant;

use con_ron_core::arena::checker;
use con_ron_core::arena::checker::InstallHook;
use con_ron_core::arena::checker::PendingCheck;
use con_ron_core::arena::checker_split::ValueKind;
use con_ron_core::arena::env as ienv;
use con_ron_core::arena::env::{IDeclaration, IFEnv};
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
use con_ron_core::arena::store::EStore;
use con_ron_core::frontend::export_c;
use con_ron_core::frontend::export_c::ChunkSource;
use con_ron_core::frontend::export_c::ParseResultD;
use con_ron_core::frontend::types::Modeller;

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
// These eleven items are `Main.lean`'s own and say nothing about the term
// representation: the flag parsers and their caps, the exit-code mapping, the
// verdict word, the `CheckError` rendering and the read loop.  They were
// `crates/con-ron`'s before the swap and `con-ron` imported them across
// the crate line so that the two binaries of the differential sweep could not
// disagree about a command line; the swap deleted the other binary, so they
// live here, unchanged.
// ---------------------------------------------------------------------------

/// con-leche: none — the Lean runtime's per-thread stack reservation, which
/// `Main.lean`'s `--jobs` note measures at 1 GiB per worker.  The fold's
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

/// con-leche: ConLeche/Cached/ParsedC.lean:263-265 msSecs
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

/// con-leche: Main.lean:48-51 ConLeche.CheckError.exitCode
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

/// con-leche: Main.lean:992-1019 main
/// The `--jobs` default, which con-leche reads in `main` off
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

/// con-leche: Main.lean:436-459 jobsCount
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
             (a decimal numeral of at least 1), got {:?}",
            v
        )),
    }
}

/// con-leche: Main.lean:423-434 progressStride
/// The progress heartbeat's stride: no flag is off; bare `--progress` is
/// stride 1.  A value that is not a decimal numeral, and `0` — the flag asking
/// for no heartbeat — are usage errors: a run's output must be readable off
/// its invocation, never silently degraded.
pub fn progress_stride(v: &str) -> Result<u64, String> {
    match v.parse::<u64>() {
        Ok(0) => Err("--progress takes a declaration stride of at least 1 \
                      (a decimal numeral); omit the flag for no heartbeat"
            .to_string()),
        Ok(n) => Ok(n),
        Err(_) => Err(format!(
            "--progress takes a declaration stride \
             (a decimal numeral of at least 1), got {:?}",
            v
        )),
    }
}

/// con-leche: none — how a run *chooses* `checkDecls`' pin argument, which
/// con-leche does not have to: `Main.lean` passes `ConLeche.natOpPinSets`.
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
/// default, and the theorem's `pins` argument is that closed term
/// (`proof/ConRon/Refine/Pins.lean`).
///
/// The two overrides are **for testing only** and neither is a con-leche
/// spelling: `--pins FILE` reads a `con-ron-pins/1` dump through the
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
            let text = std::fs::read_to_string(p).map_err(|e| format!("{}: {}", p, e))?;
            con_ron_dump::parse_pins(&text).map_err(|e| format!("{}: {}", p, e))
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

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:44-48 ValueKind.word
/// The kind's word, for the check phase's heartbeat line.  `crate::driver`
/// has the same three words against `con_ron_core`'s `ValueKind`; the arena
/// has its own enum, so the three arms are spelled once more here rather than
/// converted.
pub fn value_kind_word(k: &ValueKind) -> &'static str {
    match k {
        ValueKind::Defn => "definition",
        ValueKind::Thm => "theorem",
        ValueKind::Opaque => "opaque",
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:267-276 declCLabel
/// con-leche: Main.lean:61-65 declCName
/// A record's display label, `crate::driver::decl_label`'s seven arms with
/// the names READ BACK out of the store: a handle is not a name until the
/// store is asked, which is the one thing every rendering in this crate has to
/// do that con-ron's does not.  A dangling handle renders as `?` rather than
/// failing — this is a log line, never a verdict.
pub fn decl_label(pers: &PersTier, ar: &EStore, d: &IDeclaration) -> String {
    let (kind, n) = match d {
        IDeclaration::AxiomDecl(cv) => ("axiom", Some(name_of(pers, ar, &cv.name))),
        IDeclaration::DefnDecl(cv, _, _) => ("def", Some(name_of(pers, ar, &cv.name))),
        IDeclaration::ThmDecl(cv, _) => ("theorem", Some(name_of(pers, ar, &cv.name))),
        IDeclaration::OpaqueDecl(cv, _) => ("opaque", Some(name_of(pers, ar, &cv.name))),
        IDeclaration::BasisDecl(_) => ("basis", None),
        IDeclaration::IndDecl(block, _) => (
            "inductive",
            block
                .first()
                .map(|ci| name_of(pers, ar, &ienv::i_constant_info_name(ci))),
        ),
        IDeclaration::QuotDecl(_, cv) => ("quot", Some(name_of(pers, ar, &cv.name))),
    };
    match n {
        Some(n) => format!("{} {}", kind, n),
        None => kind.to_string(),
    }
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

/// con-leche: Main.lean:318-421 checkDeclsIO
/// **`--no-mark-persistent`: accepted, and a no-op** — and here for a stronger
/// reason than `crate::driver::mark_persistent_note`'s.  con-leche's mark
/// turns off the Lean runtime's reference counting on the installed
/// environment; con-ron's counts are `std::sync::Arc`'s, atomic by type with
/// no runtime mark to clear.  **The arena has no reference counts at all**
/// (DESIGN.md §8.5: no `Arc`, no `ron::ptr`): a term is a
/// `u32` handle into a `Vec`, and the persistent tier is immutable in phase B
/// by construction.  So there is nothing the flag could turn off, and a run
/// that passes it says so rather than letting a log read as an A/B lane that
/// was never run.
pub fn mark_persistent_note() -> &'static str {
    "--no-mark-persistent accepted and ignored: the persistent mark is a Lean-runtime \
     reference-counting device (Runtime.markPersistent), and the arena has no reference \
     counts to mark — a term is a u32 handle into a Vec and the persistent tier is \
     immutable in phase B (DESIGN.md section 8.5)"
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// The worker count a run reports and the pool spawns: `max 1 (min jobs
/// pend.size)`, which is `workers_for` and nothing else —
/// the two binaries cannot drift on what `--jobs=<n>` means (task #97-P6-6b;
/// until then this clamped to ONE, because phase B was single-lane).
pub fn workers_for(jobs: u64, m: usize) -> usize {
    let w = if (jobs as usize) < m { jobs as usize } else { m };
    if w < 1 {
        1
    } else {
        w
    }
}

// ---------------------------------------------------------------------------
// The two phases (`Main.lean:67-141 installLoop`, `:160-191 checkLoop`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:143-158 checkHeartbeat
/// con-leche: Main.lean:318-421 checkDeclsIO
/// What a caller wants to know between the steps of the fold —
/// `crate::driver::PhaseObserver` over the arena's records, with the store
/// passed to every method because a handle is not a label until the store is
/// asked.  Every method defaults to nothing, so a caller implements the lines
/// it prints and no more.  The line printed BEFORE each install is not here:
/// phase A is the verified `checker::annot_fold_hooked`, and its hook is
/// `con_ron_core::arena::checker::InstallHook`, which every observer also
/// implements (task #97-P5-Driver).
pub trait PhaseObserver {
    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Phase A failed at fold position `pos`.
    fn install_failed(&mut self, _pos: u64, _total: usize) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The phase boundary: every record installed, `pend` checks pending, and
    /// the store as phase A left it — the node counts are the one number P6
    /// asked this line for, because they are what the install ADDED to the
    /// persistent tier on top of the parse's.  Since task #97-P6-2 phase A
    /// runs in the SCRATCH tier and promotes what the environment keeps, so
    /// the figure to compare with the Lean twin's (`Init`: **6 508 719**, the
    /// parse's 6 137 973 plus 370 746) is the PERSISTENT one, printed beside
    /// the total; phase B promotes nothing, so it is also the count at the
    /// end of the run.
    fn install_done(&mut self, _pers: &PersTier, _ar: &EStore, _total: usize, _pend: usize) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The worker count phase B is about to run on, so that the summary
    /// reports the lane the run actually took.
    fn phase_b_workers(&mut self, _workers: usize) {}

    /// con-leche: Main.lean:240-260 checkOne
    /// Does this observer print a line per check?  The driver asks ONCE, before
    /// the pool spawns: off, no worker touches the completed-count atomic or the
    /// observer lock at all, which is the difference between a plain pooled
    /// run and the `--progress` lane.
    fn wants_check_lines(&self) -> bool {
        false
    }

    /// con-leche: Main.lean:143-158 checkHeartbeat
    /// After the `done`-th of `m` recorded checks completed.
    fn check_after(&mut self, _pers: &PersTier, _ar: &EStore, _done: usize, _m: usize, _pc: &PendingCheck) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Phase B failed at fold position `pos`.
    fn check_failed(&mut self, _pos: u64) {}

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// Every recorded check passed.
    fn check_done(&mut self, _m: usize) {}
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// The observer a plain run (no `--progress`) hands the driver: it prints
/// nothing and wants no check lines, so no worker touches the completed-count
/// atomic or the observer lock at all.  ONE lane serves both runs since task
/// #97-P6-6b — the phase boundary freezes the tier, and a second path that
/// did not would be a second computation.
pub struct Silent;

/// con-leche: Main.lean:318-421 checkDeclsIO
impl PhaseObserver for Silent {}

/// con-leche: Main.lean:67-141 installLoop
impl InstallHook for Silent {
    /// con-leche: Main.lean:67-141 installLoop
    /// Nothing.
    fn install_before(&self, _pers: &PersTier, _ar: &EStore, _pos: u64, _total: usize, _d: &IDeclaration) {}
}

/// con-leche: Main.lean:143-158 checkHeartbeat
/// The heartbeat's line after phase B's `k`-th record, on the worker that
/// checked it: `parallel_all`'s `after` hook.  `heartbeat` is the port's
/// spelling of the cited `stride > 0` guard inside `checkOne`: off, no worker
/// touches the `done` counter or the observer lock at all.  It holds the
/// worker's state by `&` only.
#[allow(clippy::too_many_arguments)]
fn check_line<O: PhaseObserver>(
    heartbeat: bool,
    done: &AtomicUsize,
    obs: &Mutex<&mut O>,
    tier: &PersTier,
    w: &AState,
    m: usize,
    pc: &PendingCheck,
) {
    if heartbeat {
        let n = done.fetch_add(1, Ordering::Relaxed) + 1;
        // A poisoned lock means another worker panicked while printing; the
        // panic is the report and this line is dropped.
        if let Ok(mut g) = obs.lock() {
            g.check_after(tier, &w.store, n, m, pc);
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:392-416 collectChecks
/// Phase B's answer as a verdict: `parallel_all`'s first failing INDEX named
/// by its record's fold position, and the pool's own failures (a missing
/// result, a panicked worker) as internal errors — exit 3, never a verdict on
/// the input.
pub fn phase_b_verdict(
    pend: &[PendingCheck],
    r: Result<(), ParallelError<CheckError>>,
) -> Result<(), (CheckError, u64)> {
    let internal = |msg: String| con_ron_core::kernel::core_types::internal(msg.chars().map(|c| c as u32).collect());
    match r {
        Ok(()) => Ok(()),
        Err(ParallelError::Step(k, e)) => Err((e, pend[k].pos)),
        Err(ParallelError::Missing(k)) => Err((
            internal(format!("check phase: record {} was never checked", k)),
            pend[k].pos,
        )),
        Err(ParallelError::Panicked) => Err((internal("check phase: a worker panicked".to_string()), 0)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:438-455 checkDecls
/// con-leche: Main.lean:318-421 checkDeclsIO
/// **The driver**: `checker::check_decls_phased` with the boundary visible —
/// a straight line of calls, with the observer's lines between them and the
/// pool in the place of phase B's sequential walk (tasks #97-P5-Driver,
/// #98-POOL).  Each step is one premise of the capstone:
///
/// | step | here | the capstone's premise |
/// |---|---|---|
/// | phase A | `checker::annot_fold_hooked(…, fold_start(), ds, 0, obs)` | the same call accepts |
/// | boundary | `checker::freeze_tier(&mut st.store)` | the same call's value |
/// | phase B | `pool::parallel_all(m, workers, ‖ worker_state(pins), ‖w, k‖ check_pending(&tier, w, mode, &fe, &pend[k]), …)` | `ParallelAll pend.len (worker_state pins) (fun st k => check_pending tier st mode fe pend[k])` |
/// | after | `checker::thaw_tier(&mut st.store, tier)` | restores the store (`freeze_tier_ok`) |
///
/// `init` and `step` are calls into the verified crate; `parallel_all` is the
/// one trusted piece, and its contract (`pool.rs`'s note) is exactly
/// `ParallelAll`: on `Ok`, every record was checked by exactly one worker,
/// each worker folding `check_pending` over the records it claimed on ONE
/// `worker_state`.  Everything else here is the observer, which only ever
/// holds `&` the state (the hook of phase A by the trait's own signature, the
/// other lines through `&st.store` and the worker's `&AState`), so it cannot
/// change an outcome.
///
/// **The boundary is where the tier is FROZEN** (task #97-P6-6b).  Phase A
/// owns its persistent tier and appends to it; at the boundary
/// `checker::freeze_tier` moves the four stores' persistent tables out into
/// one `PersTier`, handed back `frozen`: every read through it goes to those
/// tables, and a worker's own store is frozen (`checker::worker_state`), so
/// every append there is a scratch append (task #98-FREEZE).  The
/// installed index goes to the workers by reference, since `check_pending`
/// takes the visibility bound as a scalar — so `n` workers share one
/// environment and one term DAG and own nothing but a scratch tier, their
/// caches and a copy of the pin handles (`checker::worker_state`).
pub fn check_decls_driver<O: PhaseObserver + InstallHook + Send>(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    ds: &Vec<IDeclaration>,
    jobs: u64,
    obs: &mut O,
) -> Result<IFEnv, (CheckError, u64)> {
    let total = ds.len();
    // PHASE A (ConRon.Capstone: h6): the verified fold, the heartbeat as hook.
    let p = match checker::annot_fold_hooked(pers, st, mode, pins, checker::fold_start(), ds, 0, &*obs) {
        Err(e) => {
            obs.install_failed(e.1, total);
            return Err(e);
        }
        Ok(p) => p,
    };
    let (_n_installed, fe, pend): (u64, IFEnv, Vec<PendingCheck>) = p;
    let m = pend.len();
    obs.install_done(pers, &st.store, total, m);
    let workers = workers_for(jobs, m);
    obs.phase_b_workers(workers);
    // THE PHASE BOUNDARY: the persistent tier leaves the state and becomes a
    // value every worker reads (the doc comment above).  `st` keeps its
    // (empty) store, its tables moved out, so the observer can still read a
    // label back through the tier.  (ConRon.Capstone: h7)
    let tier: PersTier = checker::freeze_tier(&mut st.store);
    // PHASE B: `check_pending` at every record, on `workers` threads, each
    // folding it over the records it claims on ONE `worker_state` — the
    // verdict and the record a rejection names are the one-worker walk's at
    // every `--jobs` (the least failing index).  (ConRon.Capstone: h8)
    let heartbeat = obs.wants_check_lines();
    let lock = Mutex::new(obs);
    let done = AtomicUsize::new(0);
    let r = parallel_all(
        m,
        workers,
        || checker::worker_state(&st.pins),
        |w: &mut AState, k| checker::check_pending(&tier, w, mode, &fe, &pend[k]),
        |w: &AState, k| check_line(heartbeat, &done, &lock, &tier, w, m, &pend[k]),
    );
    let obs: &mut O = match lock.into_inner() {
        Ok(o) => o,
        Err(e) => e.into_inner(),
    };
    // AND THE TIER GOES BACK.  Everything after the fold — the verdict line's
    // declaration label, the failing record's name, the receipts — reads a
    // handle back out of `st`, and a state left frozen over a tier that has
    // gone out of scope answers `None` to every one of them (the first
    // version of this printed `at theorem ?` where the tip printed `at
    // theorem addOk`).  `thaw_tier` is `freeze_tier` inverted.
    checker::thaw_tier(&mut st.store, tier);
    match phase_b_verdict(&pend, r) {
        Err((e, pos)) => {
            obs.check_failed(pos);
            Err((e, pos))
        }
        Ok(()) => {
            obs.check_done(m);
            Ok(fe)
        }
    }
}

// ---------------------------------------------------------------------------
// The progress heartbeat (`--progress[=<stride>]`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:318-421 checkDeclsIO
/// con-leche: Main.lean:143-158 checkHeartbeat
/// **The heartbeat**, `crate::driver::Heartbeat`'s line shapes with
/// `con-ron: ` for the prefix:
///
/// ```text
/// con-ron: parse done: <N> fold records — … t=<s>s (parse <s>s)
/// con-ron: install <i>/<N> <decl> t=<s>s
/// con-ron: install done: <N>/<N> declarations installed, <M> checks pending t=<s>s (install <s>s)
/// con-ron: check <done>/<M> <kind> <name> t=<s>s
/// con-ron: check done: <M>/<M> t=<s>s (check <s>s)
/// con-ron: done: parse <p>s, install <i>s, check <c>s, <n> worker t=<s>s
/// ```
///
/// An install line is printed BEFORE the record it names, so a run that dies
/// in phase A names on its last line the declaration it died in; a check line
/// is printed AFTER the check, so "a check that is running is not on any line,
/// the gap between two lines is where it sits".
pub struct Heartbeat {
    /// The stride; `0` is no flag and no heartbeat.
    pub stride: u64,
    /// The start of the run, which every `t=` is measured from.
    pub t0: Instant,
    /// When the parse finished, in ms since `t0` — `Main.lean`'s `tParse`.
    pub t_parse: u128,
    /// When phase A finished, in ms since `t0` — `Main.lean`'s `tCheck`.
    pub t_install: u128,
    /// The worker count phase B ran on, for the summary.
    pub workers: usize,
}

/// con-leche: Main.lean:318-421 checkDeclsIO
/// The heartbeat's own lines: the parse's, and the closing summary the failure
/// and success arms share.
impl Heartbeat {
    /// con-leche: Main.lean:461-711 checkMain
    /// A heartbeat at `stride` (0 for none), starting now.
    pub fn new(stride: u64, t0: Instant) -> Heartbeat {
        Heartbeat {
            stride,
            t0,
            t_parse: 0,
            t_install: 0,
            workers: 1,
        }
    }

    /// con-leche: none — `IO.monoMsNow`, in milliseconds since `t0`.
    fn now(&self) -> u128 {
        self.t0.elapsed().as_millis()
    }

    /// con-leche: Main.lean:461-711 checkMain
    /// `con-ron: parse done: …`, the heartbeat's first line.  Records
    /// `t_parse`, so the summary can price the parse whatever happens next.
    pub fn parse_done(
        &mut self,
        fold_records: usize,
        file_records: usize,
        gen_records: u64,
        synthesised: u64,
        nodes: (usize, usize, usize),
    ) {
        self.t_parse = self.now();
        if self.stride == 0 {
            return;
        }
        eprintln!(
            "con-ron: parse done: {} fold records — the file's {} ({} of them \
             generated in-process), {} built-in prelude records synthesised; store \
             {} expression, {} level, {} name nodes t={}s (parse {}s)",
            fold_records,
            file_records,
            gen_records,
            synthesised,
            nodes.0,
            nodes.1,
            nodes.2,
            ms_secs(self.t_parse),
            ms_secs(self.t_parse)
        );
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The `done:` summary — the three phase durations and the worker count.
    fn summary(&self, check_ms: Option<u128>) {
        if self.stride == 0 {
            return;
        }
        let now = self.now();
        match check_ms {
            None => eprintln!(
                "con-ron: done: parse {}s, install {}s, check not reached t={}s",
                ms_secs(self.t_parse),
                ms_secs(now - self.t_parse),
                ms_secs(now)
            ),
            Some(c) => eprintln!(
                "con-ron: done: parse {}s, install {}s, check {}s, {} worker{} t={}s",
                ms_secs(self.t_parse),
                ms_secs(self.t_install - self.t_parse),
                ms_secs(c),
                self.workers,
                if self.workers == 1 { "" } else { "s" },
                ms_secs(now)
            ),
        }
    }
}

/// con-leche: Main.lean:67-141 installLoop
/// The heartbeat's install line, as phase A's hook: it reads the clock and
/// the store and writes nothing but standard error.
impl InstallHook for Heartbeat {
    /// con-leche: Main.lean:67-141 installLoop
    /// `con-ron: install <i>/<N> <decl> t=<s>s`, before the install.
    fn install_before(
        &self,
        pers: &PersTier,
        ar: &EStore,
        pos: u64,
        total: usize,
        d: &IDeclaration,
    ) {
        if self.stride > 0 && pos % self.stride == 0 {
            eprintln!(
                "con-ron: install {}/{} {} t={}s",
                pos,
                total,
                decl_label(pers, ar, d),
                ms_secs(self.now())
            );
        }
    }
}

/// con-leche: Main.lean:143-158 checkHeartbeat
/// con-leche: Main.lean:318-421 checkDeclsIO
/// The heartbeat as an observer of the two phases.
impl PhaseObserver for Heartbeat {
    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron: install failed at <i>/<N> …`, then the summary.
    fn install_failed(&mut self, pos: u64, total: usize) {
        if self.stride > 0 {
            let now = self.now();
            eprintln!(
                "con-ron: install failed at {}/{} t={}s (install {}s)",
                pos,
                total,
                ms_secs(now),
                ms_secs(now - self.t_parse)
            );
        }
        self.summary(None);
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron: install done: <N>/<N> …, <M> checks pending …`.
    fn install_done(&mut self, pers: &PersTier, ar: &EStore, total: usize, pend: usize) {
        self.t_install = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron: install done: {}/{} declarations installed, {} checks \
                 pending; store {} expression ({} persistent), {} level, {} name nodes \
                 t={}s (install {}s)",
                total,
                total,
                pend,
                ar.node_count(pers),
                ar.pers_count(pers),
                ar.ls().node_count(pers),
                ar.ns().node_count(pers),
                ms_secs(self.t_install),
                ms_secs(self.t_install - self.t_parse)
            );
        }
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// The cited `workers`, for the summary's last field.
    fn phase_b_workers(&mut self, workers: usize) {
        self.workers = workers;
    }

    /// con-leche: Main.lean:240-260 checkOne
    /// The heartbeat prints a check line exactly when it has a stride.
    fn wants_check_lines(&self) -> bool {
        self.stride > 0
    }

    /// con-leche: Main.lean:143-158 checkHeartbeat
    /// `con-ron: check <done>/<M> <kind> <name> t=<s>s`, after the check.
    fn check_after(
        &mut self,
        pers: &PersTier,
        ar: &EStore,
        done: usize,
        m: usize,
        pc: &PendingCheck,
    ) {
        if self.stride > 0 && (done as u64) % self.stride == 0 {
            eprintln!(
                "con-ron: check {}/{} {} {} t={}s",
                done,
                m,
                value_kind_word(&pc.vg.kind),
                name_of(pers, ar, &pc.vg.cv_a.name),
                ms_secs(self.now())
            );
        }
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron: check failed at fold position <i> …`, then the summary.
    fn check_failed(&mut self, pos: u64) {
        let now = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron: check failed at fold position {} t={}s (check {}s)",
                pos,
                ms_secs(now),
                ms_secs(now - self.t_install)
            );
        }
        self.summary(Some(now - self.t_install));
    }

    /// con-leche: Main.lean:318-421 checkDeclsIO
    /// `con-ron: check done: <M>/<M> …`, then the summary.
    fn check_done(&mut self, m: usize) {
        let now = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron: check done: {}/{} t={}s (check {}s)",
                m,
                m,
                ms_secs(now),
                ms_secs(now - self.t_install)
            );
        }
        self.summary(Some(now - self.t_install));
    }
}

// ---------------------------------------------------------------------------
// The verdict lines
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:461-711 checkMain
/// **The accept line**, `crate::driver::verdict_accept`'s with this
/// binary's name: `records` is the FILE's declaration-record count — what the
/// parse produced, less the records the in-process modeller generated — and
/// nothing the preparation does moves it.  It is not the environment's
/// constant count, which is a property of the representation and not of the
/// input.  Printed on STDOUT, where a caller greps for a verdict.
pub fn verdict_accept(records: u64, mode_tag: &str) -> u8 {
    println!(
        "con-ron: accepted {} declarations ({})",
        records, mode_tag
    );
    0
}

/// con-leche: Main.lean:461-711 checkMain
/// The failure line: the error, the declaration it names and its FOLD
/// position, the mode, the elapsed time.  There is no second pass — the fold's
/// error carries the position, so the label is read off the record array the
/// driver already holds.
///
/// `i` is the fold position and is NOT the file's record index (the prepared
/// list starts with the prelude's records and carries the ones the in-process
/// modeller generated); the declaration NAME on the line is the portable
/// handle.  `owner` is the inductive block a generated `_model` record belongs
/// to, where the caller can say.
pub fn verdict_failure(
    pers: &PersTier,
    ar: &EStore,
    ds: &Vec<IDeclaration>,
    e: &CheckError,
    i: u64,
    owner: Option<String>,
    mode_tag: &str,
    t0: Instant,
) -> u8 {
    let code = exit_code(e);
    let loc = match ds.get(i as usize) {
        None => format!(" [at fold position {}]", i),
        Some(d) => match owner {
            Some(t) => format!(
                " [at {}, a generated model record of inductive {}, fold position {}]",
                decl_label(pers, ar, d),
                t,
                i
            ),
            None => format!(" [at {}, fold position {}]", decl_label(pers, ar, d), i),
        },
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
// `ConLeche/Frontend/ExportC.lean`'s `parseExportHandleD` and
// `parseExportStreamD`: the core's `export_c::parse_source` over the file
// handle.  Only the READS are here, for `crate::driver`'s reason:
// `IO.FS.Handle.read` has no model, and a theorem about the file is a
// theorem about its bytes.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
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

/// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
impl<'a, R: Read> ChunkSource for HandleSource<'a, R> {
    /// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
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

/// con-leche: ConLeche/Frontend/ExportC.lean:903-931 parseExportHandleD
/// Streaming direct parse off an open reader, into the persistent tier of
/// `ar`: the VERIFIED reader loop `export_c::parse_source` over the handle
/// (task #97-P5-Driver moved the loop into the core; what is left here is
/// the reads).  The chunk count comes back for the heartbeat, as the Lean
/// twin's `readFold` returns it.
pub fn parse_export_handle_d<R: Read, M: Modeller>(
    pers: &PersTier,
    m: &M,
    ar: &mut AState,
    h: &mut R,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    let mut src = HandleSource { h, chunk, chunks: 0, err: None };
    let r = export_c::parse_source(pers, m, ar, &mut src, in_model, census);
    match src.err {
        Some(e) => Err(e),
        None => Ok((r, src.chunks)),
    }
}

/// con-leche: ConLeche/Frontend/ExportC.lean:933-938 parseExportStreamD
/// Streaming direct parse of a file.
pub fn parse_export_stream_d<M: Modeller>(
    pers: &PersTier,
    m: &M,
    ar: &mut AState,
    path: &str,
    in_model: bool,
    census: bool,
    chunk: usize,
) -> std::io::Result<(Result<ParseResultD, (CheckError, u64)>, u64)> {
    let mut f = std::fs::File::open(path)?;
    parse_export_handle_d(pers, m, ar, &mut f, in_model, census, chunk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::frontend::types::DeclineModeller;

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
                parse_export_handle_d(pers, &DeclineModeller {}, &mut ar, &mut r, true, false, chunk)
                    .expect("no io error");
            let streamed = streamed
                .unwrap_or_else(|(e, l)| panic!("chunk {} line {}: {}", chunk, l, message(&e)));
            let mut ar2 = AState::init(EStore::empty());
            let cs: Vec<Vec<u8>> = b.chunks(chunk).map(|c| c.to_vec()).collect();
            let pure = export_c::parse_chunks(pers, &DeclineModeller {}, &mut ar2, &cs, true, false)
                .unwrap_or_else(|(e, l)| {
                    panic!("pure chunk {} line {}: {}", chunk, l, message(&e))
                });
            assert_eq!(streamed.decls.len(), pure.decls.len(), "chunk {}", chunk);
            assert_eq!(streamed.decls.len(), 1, "chunk {}", chunk);
            assert_eq!(ar.store.node_count(pers), ar2.store.node_count(pers), "chunk {}", chunk);
        }
    }

    /// The three words of the arena's own `ValueKind`, and the flag values,
    /// which are `crate::driver`'s and are called across the crate line so
    /// that the two binaries cannot drift.
    #[test]
    fn rendering_and_flag_values() {
        assert_eq!(value_kind_word(&ValueKind::Defn), "definition");
        assert_eq!(value_kind_word(&ValueKind::Thm), "theorem");
        assert_eq!(value_kind_word(&ValueKind::Opaque), "opaque");
        assert_eq!(progress_stride("1"), Ok(1));
        assert!(progress_stride("0").is_err());
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
        let tier = checker::freeze_tier(&mut st.store);
        assert!(tier.frozen);
        assert_eq!(name_of(&tier, &st.store, &n), "add");
        // and a worker, whose store is its own, reads it too
        let w = checker::worker_state(&st.pins);
        assert_eq!(name_of(&tier, &w.store, &n), "add");
        // thawed: the store is what phase A left
        checker::thaw_tier(&mut st.store, tier);
        assert!(!st.store.scratch_on);
        assert_eq!(name_of(empty, &st.store, &n), "add");
    }
}
