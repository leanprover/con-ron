//! `con-ron` — con-leche's `Main.lean`: the command-line driver, on a **raw**
//! lean4export stream.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!         [--progress[=<stride>]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron --help
//! ```
//!
//! It reads the file and checks the declarations in order.  The steps are
//! con-leche's four, and they are separable and pure (`Main.lean`'s `checkMain`
//! and the `do` chain of `ConLeche.no_False_declaration`):
//!
//! ```text
//! builtin_prelude_e  →  parse_chunks  →  prepare_prelude  →  check_decls
//! ```
//!
//! — the built-in prelude parses
//! (`con_ron_core::frontend::prelude`), the stream is decoded line by line off
//! the handle into the file's own records (`con_ron_core::frontend::export_c`;
//! mutual and nested inductive blocks get their `_model` family generated in
//! process by `in_model`, which the core calls through the `Modeller` trait,
//! and the projection functions are rewritten),
//! `con_ron_core::frontend::prepare` puts the prelude's declarations in front
//! and hoists a pinned `Nat` operation's ground, and the resulting
//! `Vec<Declaration>` goes to the fold — `con_ron::driver`, which is
//! `con_ron_core::cached::installed::check_decls`' body with the phase
//! boundary visible, the fold DESIGN.md §1's main theorem is about.  Since
//! con-leche task #295 all four steps fail in ONE error type, the checker's
//! `CheckError` paired with the failure's position (the input LINE number in
//! the frontend's half, the record's fold position in the fold's), which is
//! why the exit code below is `driver::exit_code` whichever step produced it.
//!
//! **This binary is the one true driver** (task #40): everything from the
//! prepared list on — the exit-code mapping, the two phase loops, the
//! `--progress` heartbeat, the verdict lines — lives in `con_ron::driver`,
//! which task #40 wrote as the shared body of this binary and the retired
//! `con-ron-check` and which task #80 left as this binary's alone.  What is
//! here is this binary's own front matter: the flags, the prelude, the parse,
//! the preparation, the receipts.
//!
//! **Since task #84 the four steps are the VERIFIED crate's**
//! (`con_ron_core::frontend::*`, OVERVIEW §3.7); what this crate still owns of
//! the parse is the reads (`driver::parse_export_stream_d`, whose pure
//! counterpart `parse_chunks` is the core's) and the in-process modeller the
//! core takes as a type parameter.
//!
//! Exit codes are con-leche's (`vendor/con-leche/Main.lean:15-31`, its
//! `OVERVIEW.md` §0): 0 accepted, 1 rejected, 2 declined, 3
//! usage/malformed/internal.  `driver`'s module note has the table, and the
//! two conventions that are not exit codes — out of memory (con-leche's
//! exit 1 is a Lean-runtime panic the port cannot reproduce: a Rust allocation
//! failure aborts, which a shell reports as 134) and a panic, which is 3.
//!
//! **NO TEMPORARY FILES** (con-leche task #180).  The checker writes nothing
//! outside its own stdout/stderr and reads its input strictly forward, 4 MiB
//! at a time, so a Mathlib-scale export never materialises anywhere.
//!
//! **Three flags differ from con-leche's, and say so here.**
//!
//! * `--jobs=<n>` is con-leche's flag and does con-leche's thing (task #48):
//!   `n` workers claim records off a shared counter in phase B
//!   (`con_ron::pool`), `--jobs=1` is the plain loop with no counter, and the
//!   verdict is the sequential walk's at every `n`.  What differs is the
//!   **default**: con-leche's is one worker per hardware thread, which on a
//!   96-thread machine asks for 96 GiB of address space and aborts under
//!   `ulimit -v`, so the port caps its default at
//!   `driver::JOBS_DEFAULT_CAP` and that constant's note has the arithmetic.
//! * `--no-mark-persistent` is **accepted and a no-op**, and a run that passes
//!   it says why: the mark it turns off is a Lean-runtime reference-counting
//!   device (`Runtime.markPersistent`), and the port's counts are
//!   `std::sync::Arc` counts — atomic by type, in every lane, with no runtime
//!   mark to clear (`driver::mark_persistent_note`).  It is accepted rather
//!   than rejected so that a script measuring both checkers can pass it to
//!   both.
//! * `--pins FILE` and `--no-pins` are con-ron's own and are **test
//!   overrides** (task #43).  The pin list is an explicit argument of the fold
//!   since con-leche task #304, and what the binary passes is `natOpPinSets`:
//!   here that value is an embedded text constant *inside the verified core*
//!   (`kernel::pins_text::PINS_TEXT`) which the core itself decodes
//!   (`kernel::pins_decode::decode_embedded`), so a plain run checks with
//!   con-leche's own pins and nothing is read from outside.  `--pins FILE`
//!   reads a `con-ron-pins/1` dump through the unverified reader instead
//!   (task #31's arrangement, which `scripts/diff-e2e.sh --pins-file` still
//!   exercises), and `--no-pins` is the empty list, i.e. the pin loop's `[]`
//!   arm — a `Nat.div`/`Nat.mod` stream then declines with "unsupported
//!   Nat.div/mod spelling", exactly as con-leche does for a stream matching no
//!   variant.
//!
//! Any other option is a usage error: the run reports it, prints the usage
//! text and exits 3 without reading its input.  con-leche's thirteen retired
//! spellings are gone **without a trace** since its task #303 — the repository
//! is public and no user has a retired invocation to protect — so they take
//! that same generic path here, and no message names them.

use std::process::ExitCode;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::declaration_names;
use con_ron_core::kernel::env::CheckMode;

use con_ron_core::frontend::export_c::{self, ParseResultD};
use con_ron_core::frontend::prelude;
use con_ron_core::frontend::prepare;

use con_ron::driver;
use con_ron::driver::Heartbeat;
use con_ron::driver::STACK_BYTES;
use con_ron::in_model::InProcess;
use con_ron::render::name_str;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for the `con-ron-pins/1` reader of `--pins` and for
// `natdec`, the decimal parser the frontend shares with it.  So `con-ron`
// declares none — but it *chooses*: `crates/con-ron/Cargo.toml` takes that
// crate with `default-features = false` and forwards `mimalloc` (the default)
// and `jemalloc`, so `cargo build --release --no-default-features` is glibc
// `malloc` (task #89).  The claim this comment used to make — that the flag
// worked without the forwarding — was false, and task #88 §5 measured the
// `mi_*` symbols still in the binary to prove it; `--help` now prints
// `con_ron_dump::ALLOCATOR` so a run can say which one it measured.

/// con-leche: Main.lean:714-944 usage
/// The usage text.  DESIGN.md §3.1: message strings need not match, and this
/// one deliberately does not — it is con-leche's synopsis plus the three flags
/// that differ and the one piece of `Main.lean` that is not ported.
const USAGE: &str = "\
usage: con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
               [--progress[=<stride>]] [--pins FILE|--no-pins]
               FILE.ndjson
       con-ron --help

  --verified        the default, and the mode the main theorem is about: every
                    environment the fold accepts in this mode has a model in
                    every set theory (ConLeche.model_exists,
                    ConLeche/MainTheorem.lean), so a stream declaring a
                    theorem of type False is never accepted
                    (ConLeche.no_False_theorem_accepted).  What the port
                    proves is that same statement about THIS program's fold
                    (DESIGN.md §1); con-leche's file-level corollary
                    ConLeche.no_False_declaration, which covers the parse as
                    well, is NOT yet claimed here -- task #84 put the parser
                    into the verified core, so the corollary is now reachable,
                    but its proof is the next task's.
  --trusted         the unverified mode: the SAME checker bodies at the mode
                    with the certification-only work switched off.  An accept
                    in this mode is outside the theorem.
  --jobs=<n>        the check phase's worker count: <n> workers claim records
                    one at a time off a shared counter, and --jobs=1 runs the
                    plain loop with no counter and no result table.  The
                    verdict, and the declaration a rejection names, are the
                    same at every <n>: the results are walked in RECORD order,
                    so the first failing record in fold order is the one
                    reported.  Each worker reserves 1 GiB of address space for
                    its stack, so a run under `ulimit -v` needs 3x the
                    checker's resident set plus a gigabyte per worker; the
                    DEFAULT is one worker per hardware thread capped at 16 for
                    that reason (con-leche's uncapped default aborts on a
                    96-thread machine).  0 or a non-numeral is a usage error,
                    as in con-leche.
  --no-mark-persistent
                    ACCEPTED AND A NO-OP: the mark it turns off is a
                    Lean-runtime reference-counting device
                    (Runtime.markPersistent), and this program's counts are
                    std::sync::Arc counts -- atomic by type, in every lane,
                    with no runtime mark to clear.  A run that passes it says
                    so on stderr.
  --progress[=<stride>]
                    opt-in progress heartbeat on STDERR, one line shape per
                    phase:
                      con-ron: parse done: <N> fold records ... t=<s>s
                      con-ron: install <i>/<N> <decl> t=<s>s
                      con-ron: install done: <N>/<N> ..., <M> checks pending t=<s>s
                      con-ron: check <done>/<M> <kind> <name> t=<s>s
                      con-ron: check done: <M>/<M> t=<s>s
                      con-ron: done: parse <p>s, install <i>s, check <c>s, <n> workers
                    An install line is printed BEFORE every <stride>-th
                    declaration is installed (<i> is its FOLD position, which
                    the stream's record index sits near but not at a fixed
                    offset above), so a run that dies in the install phase
                    names the declaration it died in on its last line.  A
                    check line is printed AFTER every <stride>-th COMPLETED
                    check.  On a failure the phase's closing line says so
                    ('install failed at', 'check failed at') and the summary
                    still prints.  Bare --progress is stride 1; a stride that
                    is not a decimal numeral, or 0, is a usage error.
  --pins FILE       con-ron's own, FOR TESTING: read the pin list from a
                    `con-ron-pins/1` dump instead of the core's own embedded
                    text (task #43), through the UNVERIFIED reader.
  --no-pins         con-ron's own, FOR TESTING: the empty pin list, the pin
                    loop's `[]` arm, under which a Nat.div/Nat.mod stream
                    declines.  Neither flag is needed for a normal run: the
                    pins are con-leche's `natOpPinSets`, embedded in the
                    verified core and decoded by it.
  --help            print this text on STDOUT and exit 0, in any argument
                    position; no input is read.  Its last line names the
                    global allocator THIS binary was built with (below), so a
                    measurement can be reproduced.

build-time selection (cargo features, not command-line flags): the global
allocator is `con-ron-dump`'s `#[global_allocator]`, chosen on this crate's
dependency edge -- `cargo build --release` is mimalloc, `--no-default-features`
is glibc `malloc`, and `--no-default-features --features jemalloc` is jemalloc.

Any other option is a usage error: the run reports it, prints this text and
exits 3 without reading its input.

exit codes: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal.
An out-of-memory condition is NEITHER: con-leche's exit 1 for it is the Lean
runtime's own panic, and this program instead aborts the way Rust aborts on a
failed allocation ('memory allocation of <n> bytes failed', SIGABRT, which a
shell reports as 134).  A panic is exit 3.

THE VERDICT LINE'S COUNT.  It counts the FILE's accepted declaration RECORDS:
one per def/theorem/opaque/axiom/inductive/quot record the file declares.  The
built-in prelude's own records are not counted, and neither are the records
the in-process modeller generates; a stream record that declares a prelude
declaration IS counted -- the preparation moves it to the front rather than
dropping it, and it is what installs.  That count is a property of the INPUT.
The number of environment CONSTANTS is not: an inductive record installs
several constants (type former, constructors, recursor, projection table), so
it moves when the representation moves.

THE BUILT-IN PRELUDE.  Every run installs, first and unconditionally, the
checker's own little prelude -- the six pinned basis blocks (Eq, Nat, PUnit,
Empty, False, Quot) and the toolchain's Bool and And blocks, embedded at build
time -- so the pin-certified Nat operations find their ground whatever order
the export chose.  The stream's OWN copy of a prelude declaration is moved to
the front in the prelude's order, and only the prelude records the stream does
not declare are synthesised; a pinned operation's stream-certified structural
ground (Nat.ble, Nat.sub, Nat.mul) is HOISTED ahead of the operation when the
stream declares it later.  All of that is one pure total function from the
file's records to the fold's input (con_ron::frontend::prepare); the parse
itself only decodes, and recognising a block as a pinned basis block or a
record as the quotient package's is the FOLD's.

environment (con-leche's):
  CON_LECHE_INMODEL=0          turn the in-process modeller off; a mutual or
                               nested block is then pushed bare and the FOLD
                               declines it, having found no route
  CON_LECHE_INMODEL_CENSUS=1   report every mutual/nested block's outcome
                               after the parse and stop (exit 2)
  CON_LECHE_PROJREC_TRACE      name each rewritten projection function
These are the in-process modeller's debug switches and they go with it: no
environment variable this program reads can shape a verdict, which is
con-leche's own rule -- every such switch is a command-line flag.

NOT PORTED: CON_LECHE_INMODEL_DUMP, the debug splice of the generated records
into a copy of the input -- it is written through con-leche's annotated-NDJSON
writer (`Frontend/ExportWrite.lean`), an output path this checker does not
have.";

/// con-leche: Main.lean:946-960 Args
/// What the command line asked for.  `no_mark` is here, as con-leche's
/// `noMark` is, because the flag is accepted — it just has nothing to turn
/// off (`driver::mark_persistent_note`).
struct Args {
    files: Vec<String>,
    verified: bool,
    progress: u64,
    jobs: Option<u64>,
    no_mark: bool,
    pins: Option<String>,
    /// `--no-pins` (task #43): the empty pin list, the pin loop's `[]` arm.  A
    /// test override; the default is the core's own embedded text.
    no_pins: bool,
    bad: Option<String>,
}

/// con-leche: Main.lean:962-990 parseArgs
/// The argument parse.  Since con-leche task #303 there are no retired
/// spellings to recognise: the thirteen that used to be hard errors naming
/// their successor fall through to the generic `starts_with('-')` arm, which
/// is "unknown option" and exit 3.  The two `=`-carrying live flags are read
/// there too, as con-leche reads them.
fn parse_args(argv: &[String]) -> Args {
    let mut a = Args {
        files: Vec::new(),
        verified: true,
        progress: 0,
        jobs: None,
        no_mark: false,
        pins: None,
        no_pins: false,
        bad: None,
    };
    let mut i = 0usize;
    while i < argv.len() {
        let s = argv[i].as_str();
        // The FIRST bad argument is the one reported, as con-leche's fold
        // reports the first `bad` it set.
        let bad = |m: String, a: &mut Args| {
            if a.bad.is_none() {
                a.bad = Some(m);
            }
        };
        match s {
            "--verified" => a.verified = true,
            "--trusted" => a.verified = false,
            "--progress" => a.progress = 1,
            "--no-mark-persistent" => a.no_mark = true,
            "--no-pins" => a.no_pins = true,
            "--pins" => {
                i += 1;
                if i >= argv.len() {
                    bad("--pins takes a file: --pins FILE".to_string(), &mut a);
                } else {
                    a.pins = Some(argv[i].clone());
                }
            }
            "--jobs" => bad(
                "--jobs takes a worker count: --jobs=<n>; omit the flag for one worker \
                 per hardware thread"
                    .to_string(),
                &mut a,
            ),
            _ => {
                if let Some(v) = s.strip_prefix("--progress=") {
                    match driver::progress_stride(v) {
                        Ok(n) => a.progress = n,
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--jobs=") {
                    match driver::jobs_count(v) {
                        Ok(n) => a.jobs = Some(n),
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--pins=") {
                    a.pins = Some(v.to_string());
                } else if s.starts_with('-') {
                    bad(format!("unknown option {}", s), &mut a);
                } else {
                    a.files.push(s.to_string());
                }
            }
        }
        i += 1;
    }
    a
}

/// con-leche: none — `IO.getEnv k == some v`, which `checkMain` writes inline
/// at each of its environment gates.
fn env_is(k: &str, v: &str) -> bool {
    std::env::var(k).ok().as_deref() == Some(v)
}

/// con-leche: none — the three verdict classes of a `CheckError` as the
/// frontend's callers report them.  con-leche writes the three arms out at
/// each of its two frontend gates (the prelude's and the parse's); the port
/// has a fourth constructor (`CheckError::Native`, a machine-word limit — the
/// port cannot carry this input), which is a DECLINE like `notImplemented`,
/// so the two gates below share this one classification.
enum FrontendClass {
    Declined(String),
    Invalid(String),
    Internal(String),
}

/// con-leche: none — `FrontendClass` of a `CheckError` (see there).
fn classify(e: &CheckError) -> FrontendClass {
    let m = driver::message(e);
    match e {
        CheckError::NotImplemented(_) => FrontendClass::Declined(m),
        CheckError::Native(_) => FrontendClass::Declined(m),
        CheckError::Invalid(_) => FrontendClass::Invalid(m),
        CheckError::Internal(_) => FrontendClass::Internal(m),
    }
}

/// con-leche: Main.lean:461-711 checkMain
/// con-leche: Main.lean:53-59 parseInput
/// The real driver's front matter: the prelude, the streaming parse, the
/// preparation, the receipts, then `driver` for the fold and the verdict.
/// **No environment variable read here can shape a verdict** (con-leche task
/// #287): what is left of them is the in-process modeller's three debug
/// switches, and they go with the modeller.
fn check_main(a: &Args, file: &str) -> u8 {
    let t0 = Instant::now();
    let mode_tag = if a.verified {
        "--verified"
    } else {
        "--trusted"
    };
    let mode = if a.verified {
        CheckMode::Verified
    } else {
        CheckMode::Trusted
    };
    // THE BUILT-IN PRELUDE: parsed from the committed
    // `pins/<toolchain>.prelude.ndjson`.  `prepare_prelude` below puts its
    // declarations in front of every stream.  A prelude that does not parse is
    // a corrupted build, reported before any input is read.
    // The in-process modeller, which the parse takes as a type parameter: the
    // verified core is quantified over an arbitrary `Modeller` (OVERVIEW §3.7),
    // and this unit struct is the one the binary supplies.
    let modeller = InProcess;
    let prelude_ix = match prelude::builtin_prelude_e(&modeller) {
        Ok(p) => p,
        Err((e, line)) => {
            let what = match classify(&e) {
                FrontendClass::Internal(m) => format!("does not parse (line {}: {})", line, m),
                FrontendClass::Declined(w) => format!("is unsupported ({})", w),
                FrontendClass::Invalid(w) => format!("contradicts itself ({})", w),
            };
            eprintln!(
                "con-ron: the built-in prelude {}; regenerate it with \
                 `lake exe natop-pins-export` ({})",
                what, mode_tag
            );
            return 3;
        }
    };
    let in_model = !env_is("CON_LECHE_INMODEL", "0");
    let census = env_is("CON_LECHE_INMODEL_CENSUS", "1");
    // Streaming frontend: the parse reads the file 4 MiB at a time, so
    // neither a wholesale text buffer nor a scratch file exists.  What comes
    // out is the FILE's records (plus the in-process modeller's) and nothing
    // else: since con-leche task #293 the decoder decodes, and every verdict
    // about a record's content is the fold's.
    let parsed: ParseResultD =
        match driver::parse_export_stream_d(
            &modeller,
            file,
            in_model,
            census,
            export_c::CHUNK_SIZE,
        ) {
            Err(e) => {
                eprintln!("con-ron: {}: {}", file, e);
                return 3;
            }
            Ok(Err((e, line))) => match classify(&e) {
                FrontendClass::Declined(what) => {
                    eprintln!("con-ron: declined: {} ({})", what, mode_tag);
                    return 2;
                }
                // A stream whose inductive block contradicts its own
                // declarations in a REDUNDANT field is rejected at the parse,
                // as official's replay rejects a recursor or constructor
                // record that is not the generated one.
                FrontendClass::Invalid(what) => {
                    eprintln!("con-ron: invalid: {} ({})", what, mode_tag);
                    return 1;
                }
                FrontendClass::Internal(msg) => {
                    eprintln!("con-ron: {}:{}: {}", file, line, msg);
                    return 3;
                }
            },
            Ok(Ok(r)) => r,
        };
    // the in-process modeller's receipt
    if !parsed.in_modelled.is_empty() {
        let names: Vec<String> = parsed.in_modelled.iter().map(name_str).collect();
        eprintln!(
            "con-ron: {} inductive blocks modelled in-process: {} ({} generated \
             records, checked by the fold as declarations and not counted as records \
             of the file)",
            parsed.in_modelled.len(),
            names.join(", "),
            parsed.gen_records
        );
    }
    // the census (`CON_LECHE_INMODEL_CENSUS=1`): every mutual/nested block's
    // outcome, then stop — the parse only, no fold.  Exit 2, never 0: the
    // census stops after the parse, so nothing is claimed about the stream.
    if census {
        for (n, why) in parsed.in_model_declined.iter() {
            eprintln!(
                "con-ron: inmodel declined {}: {}",
                name_str(n),
                con_ron::render::from_cps(why)
            );
        }
        eprintln!(
            "con-ron: inmodel census: {} modelled, {} declined ({}, parse only)",
            parsed.in_modelled.len(),
            parsed.in_model_declined.len(),
            mode_tag
        );
        return 2;
    }
    // **PREPARE** (`frontend::prepare`, con-leche task #293): what the fold
    // runs over is `prepare_prelude` of the file's records — the prelude's
    // declarations first (the stream's own copies where it has them, the rest
    // synthesised), then the stream's, with every pinned `Nat` operation's
    // stream-certified ground hoisted ahead of it.  Total, pure, no error
    // channel, and no record of the file is dropped or rewritten.  Fold
    // positions count from the prelude's first record; the VERDICT's count is
    // the file's own, which this step does not change.
    let file_records = parsed.decls.len();
    let prepared = prepare::prepare_d(prelude_ix, parsed.decls);
    // the projection-function rewrite's receipt
    if !parsed.proj_rewrites.is_empty() {
        eprintln!(
            "con-ron: {} projection functions of non-direct structure-likes \
             rewritten to recursor form",
            parsed.proj_rewrites.len()
        );
        if std::env::var("CON_LECHE_PROJREC_TRACE").is_ok() {
            for n in parsed.proj_rewrites.iter() {
                eprintln!("con-ron:   rewritten {}", name_str(n));
            }
        }
    }
    // the ground hoist's receipt, which is the preparation's now
    if !prepared.hoisted.is_empty() {
        let names: Vec<String> = prepared.hoisted.iter().map(name_str).collect();
        eprintln!(
            "con-ron: {} declarations hoisted ahead of the pinned Nat operations \
             they ground: {}",
            prepared.hoisted.len(),
            names.join(", ")
        );
    }
    let pins = match driver::pins_for_run(&a.pins, a.no_pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return 3;
        }
    };
    // The heartbeat's first line: the parse and the preparation are done, and
    // the fold is about to start on this many records.  The two phases print
    // their own lines and the summary closes the run (`driver::Heartbeat`).
    let mut hb = Heartbeat::new(a.progress, t0);
    hb.parse_done(
        prepared.decls.len(),
        file_records,
        parsed.gen_records,
        prepared.synthesised,
    );
    // ONE driver, and the heartbeat is printed between its steps: a plain run
    // calls `check_decls` itself, a heartbeat run calls the same body with the
    // boundary visible (`driver::check_decls_driver`), and the verdict below
    // is printed from an accept of `check_decls` and from nothing else.
    let jobs: u64 = match a.jobs {
        Some(n) => n,
        None => driver::default_jobs(),
    };
    let verdict = if a.progress > 0 || jobs > 1 {
        driver::check_decls_driver(&mode, &pins, &prepared.decls, jobs, &mut hb)
    } else {
        installed::check_decls(&mode, &pins, &prepared.decls)
    };
    // **The headline number is the FILE's declaration-record count**: the
    // records the PARSE produced, which are the file's own, less the records
    // the in-process modeller generated (they are checked as declarations, but
    // they are not in the file).  Nothing the preparation does moves it.
    let stream_records = file_records as u64 - parsed.gen_records;
    match &verdict {
        Ok(_) => driver::verdict_accept(stream_records, mode_tag),
        Err((e, i)) => {
            // A record the in-process modeller generated: the file has no
            // position for it, so the BLOCK it models is the handle.
            let owner = prepared.decls.get(*i as usize).and_then(|d| {
                declaration_names(d)
                    .into_iter()
                    .find_map(|n| parsed.gen_owner.get(&n).map(name_str))
            });
            driver::verdict_failure(&prepared.decls, e, *i, owner, mode_tag, t0)
        }
    }
}

/// con-leche: Main.lean:992-1019 main
/// The entry point.  The checker runs IN THIS PROCESS: it spawns no copy of
/// itself, and the whole fold is on one big-stack thread; a panic on it is
/// exit 3, never a verdict.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|s| s == "--help") {
        println!("{}", USAGE);
        // The one build-time choice a run's numbers depend on, printed rather
        // than merely documented (task #89): `con-ron-dump`'s `ALLOCATOR` is
        // this binary's, because this binary is the only program that links
        // that crate's `#[global_allocator]`.
        println!("this build's global allocator: {}", con_ron_dump::ALLOCATOR);
        return ExitCode::SUCCESS;
    }
    let a = parse_args(&argv);
    if let Some(msg) = &a.bad {
        eprintln!("con-ron: {}", msg);
        eprintln!("{}", USAGE);
        return ExitCode::from(3);
    }
    if a.files.len() != 1 {
        eprintln!("{}", USAGE);
        return ExitCode::from(3);
    }
    if a.no_mark {
        eprintln!("con-ron: {}", driver::mark_persistent_note());
    }
    let file = a.files[0].clone();
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || check_main(&a, &file));
    match h {
        Err(e) => {
            eprintln!("con-ron: cannot spawn the checking thread: {}", e);
            ExitCode::from(3)
        }
        Ok(h) => match h.join() {
            Ok(code) => ExitCode::from(code),
            Err(_) => {
                eprintln!("con-ron: the checking thread died");
                ExitCode::from(3)
            }
        },
    }
}
