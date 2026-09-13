//! `driver` — con-leche's `Main.lean`: **the** driver, shared by both
//! binaries (task #40).
//!
//! Before this module `con-ron` (task #37) and `con-ron-check` (task #28)
//! each carried their own copy of the pieces of `Main.lean` that sit *above*
//! `check_decls`: the exit-code mapping, the declaration label, the two phase
//! loops with the boundary visible, and — the one that is load-bearing for a
//! verdict — the **taint-skip rule**.  Two copies of a rule that decides an
//! exit code is one copy too many, so the rule, the loops and the verdict
//! lines live here and the two binaries are argument parsers around them.
//!
//! What is *not* here is either binary's own front matter: `con-ron` reads a
//! raw lean4export stream (`frontend::export_c`) and `con-ron-check` a
//! `con-ron-decls/1` dump (`con_ron_dump::parse_decls_file`), and each has its
//! own flags and its own usage text.  What *is* here is everything from the
//! parsed `Vec<DeclC>` on.
//!
//! ## The two phases, and why they are spelled out here
//!
//! `check_decls_driver` is `installed::check_decls`' body with the phase
//! boundary visible (`Main.lean:330-449 checkDeclsIO`): phase A installs every
//! record with `annot_decl_step`, phase B checks every recorded declaration
//! from a fresh `CState` with `check_pending`.  It is step for step the fold
//! `ConLeche/Cached/Installed.lean:405-411 checkDecls` — which is why an
//! observer that prints between the steps changes no verdict, and why ONE
//! loop serves the plain run, the `--progress` heartbeat and `--stats` alike.
//! A run with no observer calls `installed::check_decls` itself and never
//! comes through here at all.
//!
//! `PhaseObserver` is the seam: con-leche prints its heartbeat from inside
//! `installLoop`/`checkLoop`, which it can because printing is in `IO` there;
//! the port's loops are pure over a `&mut O` instead, so `con-ron`'s
//! `Heartbeat` and `con-ron-check`'s stats reporter are two implementations
//! of one trait rather than two copies of one loop.
//!
//! ## Exit codes, and the two conventions that are *not* exit codes
//!
//! `Main.lean:15-31` and `OVERVIEW.md` §0:
//!
//! | exit | verdict | meaning |
//! |---|---|---|
//! | 0 | `accepted N declarations` | every declaration checked; `N` counts the stream's declaration records |
//! | 1 | `rejected` | a declaration is invalid |
//! | 2 | `declined` | the checker positively detected a feature it does not support, and says which |
//! | 3 | error | bad usage, malformed input, or an internal failure of unclear cause |
//!
//! The 1/2 distinction is deliberate and is con-leche's: a reject is a verdict
//! about the input, a decline a statement about the checker, and a decline is
//! never "something unexpectedly went wrong" — that is 3.  Only 0 carries the
//! theorem's guarantee.
//!
//! **Out of memory is not an exit code here, and con-leche's is.**  con-leche
//! documents OOM as exit 1: the Lean runtime's
//! `lean_internal_panic_out_of_memory` prints `INTERNAL PANIC: out of memory`
//! and calls `exit(1)`, uncatchable in process, so the stderr message is what
//! tells it from a reject.  The port has no such handler: a Rust allocation
//! failure goes to `alloc::handle_alloc_error`, which prints `memory
//! allocation of <n> bytes failed` and **aborts** — `SIGABRT`, which a shell
//! reports as **134**, never 1 — and an exhausted address space (`ulimit -v`)
//! or a blown 1 GiB stack aborts the same way.  So the two checkers' OOM
//! *codes* differ by construction, and a differential sweep must read the
//! stderr line, not the code; nothing in the port can narrow that, because
//! catching an abort would mean surviving the allocation that failed.
//!
//! **A panic is exit 3.**  The fold runs on a spawned thread (`STACK_BYTES`),
//! so a panic in it — a `debug` overflow, an index out of range, an
//! `unwrap` — comes back as a `join` error and both binaries turn that into
//! 3, "an internal failure of unclear cause", never a verdict on the input.
//! The panic message is on stderr above it.

use std::sync::Mutex;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::cached::parsed_c::PendingCheck;
use con_ron_core::cached::parsed_c::ValueKind;
use con_ron_core::cached::state_c;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::env::Env;
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_core::kernel::pins_decode;

use crate::frontend::export::name_str;
use crate::pool;

/// con-leche: none — the Lean runtime's per-thread stack reservation, which
/// `Main.lean`'s `--jobs` note measures at 1 GiB per worker.  The fold's
/// recursion depth is the term DAG's, and so is the frontend's
/// (`canon_expr_eq_fast`, `occurs_const_go`), so the whole run is on one.
pub const STACK_BYTES: usize = 1 << 30;

// ---------------------------------------------------------------------------
// Rendering: the exit-code mapping, the verdict words, the labels
// ---------------------------------------------------------------------------

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

/// con-leche: none — the verdict word `OVERVIEW.md` §0 tabulates against each
/// exit code.  con-leche prints the word only for the accept (`accepted N
/// declarations`) and the taint decline; a rejection's line is the error
/// message itself, so this is the port's own handle for a log to grep.
pub fn verdict_word(code: u8) -> &'static str {
    match code {
        0 => "accepted",
        1 => "rejected",
        2 => "declined",
        _ => "error",
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

/// con-leche: none — `checkDecls`' pin argument, which con-leche does not have
/// **The pin list a run checks with** (task #43).  con-leche's shipped fold
/// defaults to `natOpPinSets` (its last argument since task #285); the port
/// carries the same value as an
/// *embedded text constant inside the verified core*
/// (`kernel::pins_text::PINS_TEXT`) and decodes it with a verified decoder
/// (`kernel::pins_decode::decode_embedded`), so a run of either binary uses
/// con-leche's own pins with nothing supplied from outside.  That is the
/// default, and the theorem's `pins` argument is that closed term
/// (`proof/ConRon/Refine/Pins.lean`).
///
/// The two overrides are **for testing only** and neither is a con-leche
/// spelling: `--pins FILE` reads a `con-ron-pins/1` dump through the
/// *unverified* reader (task #31's arrangement, kept so that a differential
/// sweep can hand the checker a pin list the embedded one is not, e.g. after a
/// con-leche bump and before `scripts/gen-pins.sh` runs), and `--no-pins` is
/// the empty list, which is what exercises the pin loop's `[]` arm
/// (`scripts/diff-fixtures.sh --no-pins`).
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

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:44-48 ValueKind.word
/// The kind's word.  con-leche uses it in `checkDecl`'s type-mismatch message
/// *and* on the check phase's heartbeat line (`checkHeartbeat` prints
/// `e.pend[k].vg.kind.word`), which is why the port has it: DESIGN.md §3.7
/// keeps it out of the verified core as driver-only rendering, so the driver
/// carries it.
pub fn value_kind_word(k: &ValueKind) -> &'static str {
    match k {
        ValueKind::Defn => "definition",
        ValueKind::Thm => "theorem",
        ValueKind::Opaque => "opaque",
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:252-260 declCLabel
/// con-leche: Main.lean:61-65 declCName
/// A parsed declaration's display label.  DESIGN.md §3.7 kept it out of the
/// verified core as driver-only rendering ("the theorem never reads a
/// message"), so the driver carries it — and con-leche makes the same split
/// for the same reason: `declCLabel` lives beside the checker "because the
/// progress heartbeat's compiled hook prints it too, and the two must never
/// drift apart".  Deviation: `basisDecl` renders as `basis` rather than
/// `basis block <repr k>` (the port has no `Repr`).
pub fn decl_label(d: &DeclC) -> String {
    let (kind, n) = match d {
        DeclC::AxiomDecl(cv) => ("axiom", Some(name_str(&cv.name))),
        DeclC::DefnDecl(cv, _, _) => ("def", Some(name_str(&cv.name))),
        DeclC::ThmDecl(cv, _) => ("thm", Some(name_str(&cv.name))),
        DeclC::OpaqueDecl(cv, _) => ("opaque", Some(name_str(&cv.name))),
        DeclC::BasisDecl(_) => ("basis", None),
        DeclC::IndDecl(block, _) => (
            "inductive",
            block
                .first()
                .map(|ci| name_str(&env::constant_info_name(ci))),
        ),
    };
    match n {
        Some(n) => format!("{} {}", kind, n),
        None => kind.to_string(),
    }
}

/// con-leche: ConLeche/Cached/ParsedC.lean:248-250 msSecs
/// Milliseconds as seconds.  Also a deliberate skip in the core, for
/// `declCLabel`'s reason.  Deviation: three decimals rather than con-leche's
/// one.
pub fn ms_secs(ms: u128) -> String {
    format!("{}.{:03}", ms / 1000, ms % 1000)
}

// ---------------------------------------------------------------------------
// Flag values, and the retired spellings (`Main.lean:1057-1149 parseArgs`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:460-475 progressStride
/// The progress heartbeat's stride: no flag is off; bare `--progress` is
/// stride 1.  A value that is not a decimal numeral, and `0` — the flag asking
/// for no heartbeat — are usage errors, per the provenance discipline the
/// retired spellings follow: a run's output must be readable off its
/// invocation, never silently degraded.
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

/// con-leche: Main.lean:477-500 jobsCount
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

/// con-leche: Main.lean:502-797 checkMain
/// The `--jobs` default: con-leche's "one worker per hardware thread", capped
/// at `JOBS_DEFAULT_CAP` for the reason that constant's note gives.  A machine
/// that does not report its parallelism gets one worker.
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

/// con-leche: Main.lean:339-458 checkDeclsIO
/// The cited `workers := max 1 (min jobs pend.size)`: the count the summary
/// reports and the pool spawns.  A stream with fewer pending checks than `jobs`
/// gets one worker per check and no more.
pub fn workers_for(jobs: u64, m: usize) -> usize {
    let w = if (jobs as usize) < m { jobs as usize } else { m };
    if w < 1 {
        1
    } else {
        w
    }
}

/// con-leche: Main.lean:1066-1158 parseArgs
/// **The retired spellings.**  `Some(msg)` for every argument con-leche
/// rejects with a message naming what stands in its place; `None` for
/// anything else.  con-leche's rule, kept verbatim here because it is about
/// the *port's* verdicts too: "a retired spelling is a hard error naming what
/// replaced it — never a silent alias", so that a verdict's provenance is
/// readable off the invocation.  The run exits 3 without reading the input.
///
/// All thirteen spellings of `Main.lean`'s RETIRED FLAGS paragraph are here,
/// the four `=`-carrying ones included (`--set-model=p`, `--set-model=r`,
/// `--core=<c>`, `--check-range=<r>`).  The messages are con-leche's, minus
/// its DESIGN.md task numbers: those name *con-leche's* log, and a con-ron
/// user reading this line wants con-leche's vocabulary, not its history.
pub fn retired_flag(s: &str) -> Option<String> {
    let m = match s {
        "--set-model" => {
            "--set-model is retired; the verified mode is --verified, still the default \
             (con-leche's mode rename, 2026-09-06)"
        }
        "--set-model=p" => {
            "--set-model=p is retired; the verified mode is --verified, still the default \
             (con-leche's mode rename, 2026-09-06)"
        }
        "--set-model=r" => {
            "--set-model=r is retired; the R core (all certificates unconditional) and the \
             collapsed-model consistency proof it was the subject of were deleted after the \
             acceptance delta against the graded core measured ZERO.  The verified lane is \
             --verified"
        }
        "--no-model" => {
            "--no-model is retired; the unverified lane is --trusted (con-leche's mode \
             rename, 2026-09-06)"
        }
        "--tt-model" => {
            "--tt-model is retired; the declarative verification lane it selected was deleted \
             with the mode, and the certified mode is --verified (the default)"
        }
        "--yolo" => {
            "--yolo is retired; the cert-skipping lane is --trusted (checking-mode front door \
             included)"
        }
        "--infer-only" => {
            "--infer-only is retired; its discipline is part of --trusted, and the certified \
             mode is --verified (the default)"
        }
        "--pre" => {
            "--pre is retired; there is no preprocessor — every input is a raw lean4export \
             stream"
        }
        "--install-only" => {
            "--install-only is retired; the split install/check driver was arena machinery and \
             went with the interned representation"
        }
        "--check-range" => {
            "--check-range is retired; the split install/check driver was arena machinery and \
             went with the interned representation"
        }
        _ => {
            if s == "--core" || s.starts_with("--core=") {
                "--core is retired; there is one core and one expression representation (the \
                 interned arena and every driver over it were deleted)"
            } else if s.starts_with("--check-range=") {
                "--check-range is retired; the split install/check driver was arena machinery \
                 and went with the interned representation"
            } else {
                return None;
            }
        }
    };
    Some(m.to_string())
}

/// con-leche: Main.lean:339-458 checkDeclsIO
/// **`--no-mark-persistent`: accepted, and a no-op here.**  The line this
/// function returns is what a run that passes the flag prints, and the reason
/// is that the mark it turns off does not exist in Rust.
///
/// con-leche marks the installed environment persistent once at the phase
/// boundary (`unsafe Runtime.markPersistent`): the graph is read-only from
/// there on, and handing it to a worker task makes the Lean runtime mark it
/// MULTI-THREADED, after which every reference count on it is an atomic
/// read-modify-write on cache lines all the workers touch — pure overhead,
/// since nothing in the graph is freed or mutated again.  The mark removes the
/// counting altogether and is worth 18-32 % of wall time on the pool and 3.5 %
/// at one worker; `--no-mark-persistent` is the switch that measures it.
///
/// Every word of that is about the **Lean runtime's** reference counting, and
/// the port has no equivalent to switch off.  Its counts are
/// `std::sync::Arc`'s (§3.2, task #45) — atomic *by type*, on every handle,
/// in every lane, which is the ~15 % single-threaded the maintainer decided to
/// pay for the pool; there is no runtime-owned mark to set, no per-object
/// multi-threaded bit and no way to make a subgraph count-free short of
/// `unsafe` (§3's "Decisions of 2026-09-12" keeps that design written down as
/// the fallback).  So the flag is accepted — a script that measures both
/// checkers passes it to both — and does nothing, and a run that passes it
/// says so rather than letting a log read as an A/B lane that was never run.
///
/// **What that costs the pool is measured, not argued** (task #48): the port's
/// workers pay the atomic traffic con-leche's mark removes, on a graph that is
/// read-only for the whole of phase B, and the pool's speedup is short of
/// con-leche's for exactly the reason con-leche's own
/// `--no-mark-persistent` row prices at 18-32 % of pool wall time.  The
/// `Arc`-free way back is a type-level split of the handle (task #44's second
/// way out), not a flag.
pub fn mark_persistent_note() -> &'static str {
    "--no-mark-persistent accepted and ignored: the persistent mark is a Lean-runtime \
     reference-counting device (Runtime.markPersistent), and the port's counts are \
     std::sync::Arc counts — atomic by type, in every lane, with no runtime mark to clear"
}

// ---------------------------------------------------------------------------
// The two phases (`Main.lean:67-158 installLoop`, `:176-206 checkLoop`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:163-178 checkHeartbeat
/// con-leche: Main.lean:339-458 checkDeclsIO
/// What a caller wants to know between the steps of the fold.  Every method
/// defaults to nothing, so a caller implements the lines it prints and no
/// more; a run with no observer does not use this trait at all
/// (`installed::check_decls` is called directly).
///
/// The cited `checkHeartbeat` is the check phase's method here
/// (`check_after`), and it is `check_after` for con-leche's reason: the
/// counter is the number of COMPLETED checks and the line is printed *after*
/// the check rather than before it, so "a check that is running is not on any
/// line, the gap between two lines is where it sits".  Phase A is the other
/// way round (`install_before`): with stride 1 every declaration is announced
/// *before* it is installed, so a run that dies — an OOM, a timeout, a
/// `SIGKILL` — names on its last line the declaration it died in.
pub trait PhaseObserver {
    /// con-leche: Main.lean:67-161 installLoop
    /// Before record `pos` of `total` is installed.
    fn install_before(&mut self, _pos: u64, _total: usize, _d: &DeclC) {}

    /// con-leche: Main.lean:67-161 installLoop
    /// After record `done` of `total` was installed, with the memo state and
    /// the index it produced (`con-ron-check --stats-every` reads them).
    fn install_after(&mut self, _done: usize, _total: usize, _st: &CState, _fe: &FEnv, _pend: usize) {
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// Phase A failed at fold position `pos`, in this memo state.  The index
    /// is *not* passed: `annot_decl_step` consumed it and the error came back
    /// in its place, which is con-leche's shape too (`installLoop` returns
    /// `.error e` and the environment it had is gone).
    fn install_failed(&mut self, _pos: u64, _total: usize, _st: &CState) {}

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// The phase boundary: every record installed, `pend` checks pending.
    fn install_done(&mut self, _total: usize, _pend: usize, _st: &CState, _fe: &FEnv) {}

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// The worker count phase B is about to run on (the cited `workers`), so
    /// that the summary reports the lane the run actually took.
    fn phase_b_workers(&mut self, _workers: usize) {}

    /// con-leche: Main.lean:260-280 checkOne
    /// **Does this observer want a line per completed check?**  The port's
    /// spelling of the cited `stride > 0` guard, which con-leche reads off the
    /// stride the pool was handed: `false` and no worker touches the shared
    /// completed-counter or this observer at all, which is the difference
    /// between a plain pooled run and the `--progress` lane.  The sequential
    /// lane does not consult it — there `check_after` is one call on the
    /// checking thread and the stride test inside it is free.
    fn wants_check_lines(&self) -> bool {
        false
    }

    /// con-leche: Main.lean:163-178 checkHeartbeat
    /// After the `done`-th of `m` recorded checks completed — the record it
    /// was, the memo state it used, the index it left.
    fn check_after(
        &mut self,
        _done: usize,
        _m: usize,
        _pc: &PendingCheck,
        _st: &CState,
        _fe: &FEnv,
    ) {
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// Phase B failed at fold position `pos`, in this record's own memo
    /// state.
    fn check_failed(&mut self, _pos: u64, _st: &CState) {}

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// Every recorded check passed.
    fn check_done(&mut self, _m: usize) {}
}

/// con-leche: Main.lean:339-458 checkDeclsIO
/// con-leche: Main.lean:67-161 installLoop
/// con-leche: Main.lean:180-211 checkLoop
/// con-leche: ConLeche/Cached/Installed.lean:440-447 checkDecls
/// **The driver**: phase A installs every record, phase B checks every
/// recorded declaration against the prefix view of the installed index from a
/// fresh memo state.  This IS `check_decls`' body with the boundary visible,
/// step for step, which is why an observer printing between the steps changes
/// no outcome.
///
/// Four deviations from `checkDeclsIO`, all of them recorded elsewhere and
/// none of them a verdict:
///
/// 1. The `Prop`-indexed driver evidence (`InstallRun`, `GroupChecked`,
///    `FullyChecked`, and the subtype `checkDeclsIO` returns) is not ported —
///    DESIGN.md §3.7's skip list has that family and `installed.rs`'s module
///    note says why.  What comes back is the `Env`, and the caller's licence
///    to print an accept is that this is `check_decls`' body.
/// 2. **At `jobs <= 1` phase B runs on the calling thread**, where con-leche
///    task #269 moves it to a dedicated one whatever `--jobs` said.  That
///    finding is about Lean's per-thread mimalloc heaps and the main thread's
///    fragmentation after the install; the port's allocator is one heap for the
///    process, and both binaries already run the whole fold on one spawned
///    big-stack thread.
/// 3. There is no persistent mark at the boundary (`mark_persistent_note`).
/// 4. On a **pool** failure the observer's `check_failed` gets a fresh empty
///    memo state: the failing record's own state belongs to the worker that
///    built it and is gone by the join.  `--stats` therefore reports an empty
///    state for a pooled failure, which is rendering, never a verdict.
///
/// The pool itself is `crate::pool` (task #48): `jobs` workers claiming records
/// off a shared counter, their results merged by record index and walked in
/// record order, so the verdict and the failing record are the sequential
/// walk's at every count.  `jobs = 1` is the plain loop below, with no counter
/// and no table.
pub fn check_decls_driver<O: PhaseObserver + Send>(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    ds: &Vec<DeclC>,
    jobs: u64,
    obs: &mut O,
) -> Result<Env, (CheckError, u64)> {
    let total = ds.len();
    let mut st: CState = state_c::cstate_new();
    let mut p: (u64, FEnv, Vec<PendingCheck>) = (0, fenv::mk_fenv(env::empty()), Vec::new());
    let mut i = 0usize;
    while i < total {
        obs.install_before(p.0, total, &ds[i]);
        match installed::annot_decl_step(mode, pins, &mut st, p, &ds[i]) {
            Err(e) => {
                obs.install_failed(e.1, total, &st);
                return Err(e);
            }
            Ok(q) => p = q,
        }
        i += 1;
        obs.install_after(i, total, &st, &p.1, p.2.len());
    }
    let pend: Vec<PendingCheck> = p.2;
    let m = pend.len();
    let mut fe: FEnv = p.1;
    obs.install_done(total, m, &st, &fe);
    let workers = workers_for(jobs, m);
    obs.phase_b_workers(workers);
    if workers > 1 {
        // Phase B on the pool (`Main.lean:302-328 checkPool`): the installed
        // index is read-only from here on, every worker checks its claimed
        // records against it from a fresh `CState`, and the merged table is
        // walked in RECORD order — so this branch's verdict is the loop
        // below's, whichever worker computed which check (`pool`'s note).
        let cell = Mutex::new(&mut *obs);
        let r = pool::check_pool(mode, &fe, &pend, workers, &cell);
        drop(cell);
        match r {
            Err((e, pos)) => {
                obs.check_failed(pos, &state_c::cstate_new());
                return Err((e, pos));
            }
            Ok(()) => {}
        }
        obs.check_done(m);
        return Ok(fe.env);
    }
    // Phase B at one worker, `installed::check_pending_list`'s walk: a fresh
    // `CState` per record (§3.1's memo policy — a record is checked at its own
    // prefix view, where another record's entries would be unsound), the index
    // threaded through, no shared counter and no result table (`--jobs=1`'s
    // lane in `Main.lean:441-449`).
    let mut j = 0usize;
    while j < m {
        let mut stb: CState = state_c::cstate_new();
        match installed::check_pending(mode, &mut stb, fe, &pend[j]) {
            Err(e) => {
                obs.check_failed(pend[j].pos, &stb);
                return Err((e, pend[j].pos));
            }
            Ok(fe2) => fe = fe2,
        }
        j += 1;
        obs.check_after(j, m, &pend[j - 1], &stb, &fe);
    }
    obs.check_done(m);
    Ok(fe.env)
}

// ---------------------------------------------------------------------------
// The progress heartbeat (`--progress[=<stride>]`)
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:339-458 checkDeclsIO
/// con-leche: Main.lean:163-178 checkHeartbeat
/// **The heartbeat**, `OVERVIEW.md` §0's line shapes with con-leche's
/// `con-leche: ` prefix replaced by `con-ron: `:
///
/// ```text
/// con-ron: parse done: <N> fold records — ... t=<s>s (parse <s>s)
/// con-ron: install <i>/<N> <decl> t=<s>s
/// con-ron: install done: <N>/<N> declarations installed, <M> checks pending t=<s>s (install <s>s)
/// con-ron: check <done>/<M> <kind> <name> t=<s>s
/// con-ron: check done: <M>/<M> t=<s>s (check <s>s)
/// con-ron: done: parse <p>s, install <i>s, check <c>s, <n> worker(s) t=<s>s
/// ```
///
/// and on a failure the phase's closing line says so (`install failed at`,
/// `check failed at`) and the summary still prints, with `check not reached`
/// when phase A is the one that failed.  `<i>` on an install line is the FOLD
/// position, not the stream's record index: the parse folds the basis and
/// `quot` blocks, drops taint-skipped records and *adds* the in-process
/// modeller's, so the two drift apart by a stream-dependent amount — calibrate
/// by NAME.
///
/// The worker count on the summary is the count phase B actually ran on — the
/// driver hands it over at the boundary (`phase_b_workers`), which is
/// `max(1, min(jobs, M))`, so a stream with fewer pending checks than `--jobs`
/// asked for says so rather than reporting the request.
///
/// The three durations are measured here rather than passed in, because
/// con-leche measures them at the same three points: `t0` at the start of the
/// run, the parse's end when the caller calls `parse_done`, and the two phase
/// boundaries as the observer sees them.
pub struct Heartbeat {
    /// The stride; `0` is no flag and no heartbeat (every method returns at
    /// once, so a plain run pays one comparison per record).
    pub stride: u64,
    /// The start of the run, which every `t=` is measured from.
    pub t0: Instant,
    /// When the parse finished, in ms since `t0` — `Main.lean`'s `tParse`.
    pub t_parse: u128,
    /// When phase A finished, in ms since `t0` — `Main.lean`'s `tCheck`.
    pub t_install: u128,
    /// The worker count phase B ran on, for the summary: `Main.lean`'s
    /// `workers`, set by the driver at the boundary (`phase_b_workers`).
    pub workers: usize,
}

/// con-leche: Main.lean:339-458 checkDeclsIO
/// The heartbeat's own lines: the parse's, and the closing summary the
/// failure and success arms share.
impl Heartbeat {
    /// con-leche: Main.lean:502-797 checkMain
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

    /// con-leche: Main.lean:502-797 checkMain
    /// `con-leche: parse done: …`, the heartbeat's first line: the parse is
    /// done and the fold is about to start on this many records.  Records
    /// `t_parse`, so the summary can price the parse whatever happens next.
    pub fn parse_done(&mut self, fold_records: usize, prelude_count: u64, prelude_dropped: u64) {
        self.t_parse = self.now();
        if self.stride == 0 {
            return;
        }
        eprintln!(
            "con-ron: parse done: {} fold records — {} declarations after the {} \
             built-in prelude records ({} stream copies of prelude records dropped) \
             t={}s (parse {}s)",
            fold_records,
            fold_records as u64 - prelude_count,
            prelude_count,
            prelude_dropped,
            ms_secs(self.t_parse),
            ms_secs(self.t_parse)
        );
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// The `done:` summary — the three phase durations and the worker count.
    /// `check`'s duration is `None` when phase A failed, which is con-leche's
    /// `check not reached`.
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

/// con-leche: Main.lean:163-178 checkHeartbeat
/// con-leche: Main.lean:339-458 checkDeclsIO
/// The heartbeat as an observer of the two phases.
impl PhaseObserver for Heartbeat {
    /// con-leche: Main.lean:67-161 installLoop
    /// `con-leche: install <i>/<N> <decl> t=<s>s`, before the install.
    fn install_before(&mut self, pos: u64, total: usize, d: &DeclC) {
        if self.stride > 0 && pos % self.stride == 0 {
            eprintln!(
                "con-ron: install {}/{} {} t={}s",
                pos,
                total,
                decl_label(d),
                ms_secs(self.now())
            );
        }
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// `con-leche: install failed at <i>/<N> …`, then the summary.
    fn install_failed(&mut self, pos: u64, total: usize, _st: &CState) {
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

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// The cited `workers`, for the summary's last field.
    fn phase_b_workers(&mut self, workers: usize) {
        self.workers = workers;
    }

    /// con-leche: Main.lean:260-280 checkOne
    /// The cited `stride > 0`: with no heartbeat no worker bumps the shared
    /// completed-counter.
    fn wants_check_lines(&self) -> bool {
        self.stride > 0
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// `con-leche: install done: <N>/<N> …, <M> checks pending …`.
    fn install_done(&mut self, total: usize, pend: usize, _st: &CState, _fe: &FEnv) {
        self.t_install = self.now();
        if self.stride > 0 {
            eprintln!(
                "con-ron: install done: {}/{} declarations installed, {} checks \
                 pending t={}s (install {}s)",
                total,
                total,
                pend,
                ms_secs(self.t_install),
                ms_secs(self.t_install - self.t_parse)
            );
        }
    }

    /// con-leche: Main.lean:163-178 checkHeartbeat
    /// `con-leche: check <done>/<M> <kind> <name> t=<s>s`, after the check.
    fn check_after(&mut self, done: usize, m: usize, pc: &PendingCheck, _st: &CState, _fe: &FEnv) {
        if self.stride > 0 && (done as u64) % self.stride == 0 {
            eprintln!(
                "con-ron: check {}/{} {} {} t={}s",
                done,
                m,
                value_kind_word(&pc.vg.kind),
                name_str(&pc.vg.cv_a.name),
                ms_secs(self.now())
            );
        }
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// `con-leche: check failed at fold position <i> …`, then the summary.
    fn check_failed(&mut self, pos: u64, _st: &CState) {
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

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// `con-leche: check done: <M>/<M> …`, then the summary.
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
// The verdict, and the driver rule that lives above the fold
// ---------------------------------------------------------------------------

/// con-leche: Main.lean:502-797 checkMain
/// **The taint-skip rule, the one driver rule that decides an exit code.**
/// A clean fold over a stream whose frontend *skipped* declarations for a
/// tolerated axiom is still a decline — con-leche's user directive of
/// 2026-08-24: "uses of tolerated axioms are never accepted".  The skipped
/// declarations are absent from `decls`, so nothing tainted was checked or
/// installed, and the rest of the stream checked clean; that is not an
/// acceptance of the stream.
///
/// It must NOT live in the core: `check_decls` accepts the list it is given
/// and knows nothing of what the frontend dropped (task #28's reasoning, and
/// DESIGN.md §3.7's skip note for the driver rules).  It lives here, once, so
/// that both binaries apply the same rule — `con-ron` off its own frontend's
/// `taint_skipped`, `con-ron-check` off `--taint-skipped N`, since the count
/// is frontend state the dump does not carry (task #10's surprise 9).
///
/// con-leche prints the accept on STDOUT and every decline on stderr, and a
/// declined stream never says "accepted" (2026-09-07: it used to print the
/// accept line and *then* the decline, which reads as an accept to anything
/// that greps for one).  Returns the exit code.
pub fn verdict_accept(
    records: u64,
    taint_skipped: usize,
    detail: Option<&str>,
    mode_tag: &str,
) -> u8 {
    if taint_skipped == 0 {
        println!("con-ron: accepted {} declarations ({})", records, mode_tag);
        return 0;
    }
    match detail {
        Some(d) => eprintln!(
            "con-ron: declined ({} declarations checked, {} skipped for tolerated \
             axioms) ({}): {}",
            records, taint_skipped, mode_tag, d
        ),
        None => eprintln!(
            "con-ron: declined ({} declarations checked, {} skipped for tolerated \
             axioms) ({})",
            records, taint_skipped, mode_tag
        ),
    }
    2
}

/// con-leche: Main.lean:502-797 checkMain
/// The failure line: the error, the declaration it names and its FOLD
/// position, the mode, the elapsed time.  There is **no second pass** — the
/// fold's error carries the position, so the message is read off the record
/// array the driver already holds; con-leche deleted its diagnostic re-run
/// (`diagLoopC`) for the reason a re-check of the accepted prefix is "a lie
/// waiting to happen if the two runs ever disagreed".
///
/// `i` is the fold position and is NOT the stream's declaration-record index
/// (the parse folds, drops and generates records); the declaration NAME on the
/// line is the portable handle.  `owner` is the inductive block a generated
/// `_model` record belongs to, where the caller can say — the file has no
/// position for such a record, so the block is the handle.
///
/// Deviation: the line opens with `verdict_word`'s word (`rejected`,
/// `declined`, `error`) where con-leche opens with the message.  §3.1 lets
/// message strings differ, and the word is what `scripts/corpus.sh` greps a
/// run's output for — con-leche's own verdict vocabulary, put where a log can
/// find it.
pub fn verdict_failure(
    ds: &Vec<DeclC>,
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
                decl_label(d),
                t,
                i
            ),
            None => format!(" [at {}, fold position {}]", decl_label(d), i),
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

#[cfg(test)]
mod tests {
    use super::*;

    /// `Main.lean:48-51`'s three arms, and `OVERVIEW.md` §0's words.
    #[test]
    fn exit_codes_are_con_leches() {
        assert_eq!(exit_code(&CheckError::NotImplemented(Vec::new())), 2);
        assert_eq!(exit_code(&CheckError::Invalid(Vec::new())), 1);
        assert_eq!(exit_code(&CheckError::Internal(Vec::new())), 3);
        assert_eq!(verdict_word(0), "accepted");
        assert_eq!(verdict_word(1), "rejected");
        assert_eq!(verdict_word(2), "declined");
        assert_eq!(verdict_word(3), "error");
    }

    /// `progressStride`/`jobsCount`: `0` and a non-numeral are usage errors,
    /// and the message names the flag.
    #[test]
    fn flag_values_reject_zero_and_junk() {
        assert_eq!(progress_stride("1"), Ok(1));
        assert_eq!(progress_stride("1000"), Ok(1000));
        assert!(progress_stride("0").unwrap_err().contains("--progress"));
        assert!(progress_stride("x").unwrap_err().contains("--progress"));
        assert!(progress_stride("-1").is_err());
        assert_eq!(jobs_count("8"), Ok(8));
        assert!(jobs_count("0").unwrap_err().contains("--jobs"));
        assert!(jobs_count("many").unwrap_err().contains("--jobs"));
    }

    /// All thirteen retired spellings of `Main.lean`'s RETIRED FLAGS
    /// paragraph are rejected, and every message names the replacement.
    #[test]
    fn every_retired_spelling_names_its_replacement() {
        let cases: [(&str, &str); 13] = [
            ("--set-model", "--verified"),
            ("--set-model=p", "--verified"),
            ("--set-model=r", "--verified"),
            ("--no-model", "--trusted"),
            ("--tt-model", "--verified"),
            ("--yolo", "--trusted"),
            ("--infer-only", "--trusted"),
            ("--pre", "raw lean4export"),
            ("--core", "one core"),
            ("--core=c", "one core"),
            ("--install-only", "arena machinery"),
            ("--check-range", "arena machinery"),
            ("--check-range=1-2", "arena machinery"),
        ];
        for (flag, want) in cases {
            let got = retired_flag(flag)
                .unwrap_or_else(|| panic!("{} is not rejected", flag));
            assert!(got.starts_with(flag.split('=').next().unwrap()), "{}", got);
            assert!(got.contains("retired"), "{}", got);
            assert!(got.contains(want), "{} does not name {}", got, want);
        }
        // What is NOT retired stays unrecognised here, including the three
        // flags whose spelling is a prefix of a retired one.
        for ok in [
            "--verified",
            "--trusted",
            "--progress",
            "--progress=10",
            "--jobs=4",
            "--no-mark-persistent",
            "--help",
            "file.ndjson",
        ] {
            assert!(retired_flag(ok).is_none(), "{} must not be retired", ok);
        }
    }

    /// `Main.lean:330-449`'s `workers := max 1 (min jobs pend.size)`, and the
    /// capped default: never 0, never more workers than records, and an
    /// explicit count obeyed to the letter.
    #[test]
    fn the_worker_count_is_clamped_to_the_records() {
        assert_eq!(workers_for(1, 100), 1);
        assert_eq!(workers_for(8, 100), 8);
        assert_eq!(workers_for(8, 3), 3);
        assert_eq!(workers_for(8, 0), 1);
        assert_eq!(workers_for(96, 1_000_000), 96);
        let d = default_jobs();
        assert!(d >= 1 && d <= JOBS_DEFAULT_CAP);
    }

    /// `ValueKind.word` and `msSecs`, the two renderings the core deliberately
    /// does not carry.
    #[test]
    fn driver_only_rendering() {
        assert_eq!(value_kind_word(&ValueKind::Defn), "definition");
        assert_eq!(value_kind_word(&ValueKind::Thm), "theorem");
        assert_eq!(value_kind_word(&ValueKind::Opaque), "opaque");
        assert_eq!(ms_secs(0), "0.000");
        assert_eq!(ms_secs(7), "0.007");
        assert_eq!(ms_secs(1234), "1.234");
        assert_eq!(ms_secs(60_000), "60.000");
    }
}
