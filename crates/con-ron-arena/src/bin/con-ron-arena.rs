//! `con-ron-arena` — con-leche's `Main.lean` over the ARENA (DESIGN.md §8.6,
//! task #97 P4f), on a **raw** lean4export stream.
//!
//! ```text
//! con-ron-arena [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!               [--progress[=<stride>]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron-arena --help
//! ```
//!
//! **The same program as `con-ron`, over handles.**  The steps are con-leche's
//! four and they are the Lean twin's `runPipeline` (`Arena/Main.lean`):
//!
//! ```text
//! builtin_prelude_e  →  parse (chunk_step/chunk_finish)  →  prepare_d
//!                    →  intern_all_pins  →  install_then_check
//! ```
//!
//! — the built-in prelude parses into the persistent tier of one `EStore`
//! (`arena_core::frontend::prelude`), the stream is read 4 MiB at a time and
//! decoded into the same tier (`arena_core::frontend::export_c`; mutual and
//! nested blocks get their `_model` family generated in process by
//! `con_ron_arena::in_model`, which is `crates/con-ron`'s own modeller behind
//! a readback), `arena_core::frontend::prepare` puts the prelude's
//! declarations in front and hoists a pinned `Nat` operation's ground, the pin
//! list is interned ONCE while the scratch tier is still off
//! (`checker::intern_all_pins`), and the resulting `Vec<IDeclaration>` goes to
//! the two-phase fold (`checker::install_then_check`, or `con_ron_arena::
//! driver::check_decls_driver` when the heartbeat wants the boundary visible).
//!
//! Exit codes are con-leche's (`Main.lean:15-31`): 0 accepted, 1 rejected, 2
//! declined, 3 usage/malformed/internal — `con_ron::driver::exit_code`, the
//! same mapping the other binary uses, so `scripts/diff-e2e.sh` reads the same
//! numbers off both.  Out of memory is neither (a Rust allocation failure
//! aborts, which a shell reports as 134) and a panic is 3.
//!
//! **NO TEMPORARY FILES** (con-leche task #180).  The checker writes nothing
//! outside its own stdout/stderr and reads its input strictly forward, 4 MiB
//! at a time.
//!
//! **The one flag that behaves differently from `con-ron`'s** is `--jobs=<n>`:
//! it is accepted and validated, and phase B is single-lane
//! (`driver`'s module note, item 4, and DESIGN.md §8.3's plan for the pool).
//! A run that asks for more than one worker is told on stderr that it got one.
//! `--no-mark-persistent`, `--pins FILE` and `--no-pins` are con-ron's own and
//! mean exactly what they mean there.

use std::process::ExitCode;
use std::time::Instant;

use arena_core::arena::checker;
use arena_core::arena::env::i_declaration_names;
use arena_core::arena::monad::AState;
use arena_core::arena::store::EStore;
use arena_core::frontend::export_c;
use arena_core::frontend::export_c::ParseResultD;
use arena_core::frontend::prelude;
use arena_core::frontend::prepare;

use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;

use con_ron_arena::driver;
use con_ron_arena::driver::Heartbeat;
use con_ron_arena::driver::STACK_BYTES;
use con_ron_arena::in_model::InProcess;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for the `con-ron-pins/1` reader of `--pins`.  So this
// crate declares none but *chooses*: `crates/con-ron-arena/Cargo.toml` takes
// that crate with `default-features = false` and forwards `mimalloc` (the
// default) and `jemalloc`, exactly as `crates/con-ron` does, so the two
// binaries are measured on the same allocator unless a build says otherwise.
// `--help` prints `con_ron_dump::ALLOCATOR` so a measurement can be
// reproduced.

/// con-leche: Main.lean:714-944 usage
/// The usage text.  DESIGN.md §3.1: message strings need not match.  It is
/// `con-ron`'s synopsis — the same flags in the same order, because
/// `scripts/diff-e2e.sh` passes them to whichever binary `--bin` names — with
/// the three paragraphs that are this checker's own: the representation, the
/// single-lane phase B, and what the two `--no-mark-persistent` reasons are.
const USAGE: &str = "\
usage: con-ron-arena [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
                     [--progress[=<stride>]] [--pins FILE|--no-pins]
                     FILE.ndjson
       con-ron-arena --help

  (C), the Rust arena checker of con-ron's DESIGN.md section 8: con-leche's
  pure checker over an append-only DAG of per-constructor handle arrays, with
  con-leche's command line and con-leche's exit codes, so that
  scripts/diff-e2e.sh can run the same 348 fixtures against this binary, the
  `con-ron` binary and the Lean twin `con-ron-lean` alike.  A term is a u32
  handle into a Vec: no Arc, no tagged pointer, no unsafe.

  --verified        the default, and the mode the main theorem is about: every
                    environment the fold accepts in this mode has a model in
                    every set theory (ConLeche.model_exists), so a stream
                    declaring a theorem of type False is never accepted.  What
                    the arena rewrite proves is that same statement about this
                    program's pipeline; the proof itself is phases P3 and P5
                    (DESIGN.md section 8.6) and is NOT done.
  --trusted         the unverified mode: the SAME checker bodies at the mode
                    with the certification-only work switched off.  An accept
                    in this mode is outside the theorem.
  --jobs=<n>        ACCEPTED AND VALIDATED, and today single-lane: the check
                    phase runs one worker whatever <n> says, and a run that
                    asks for more is told so on stderr.  DESIGN.md section 8.3
                    has the plan the flag is kept for — the persistent tier is
                    immutable in phase B and each worker owns a scratch tier
                    and its own caches, so the pool adds no atomics — and the
                    driver's phase-B loop is shaped for it.  0 or a
                    non-numeral is a usage error, as in con-leche.
  --no-mark-persistent
                    ACCEPTED AND A NO-OP, for a stronger reason than the
                    `con-ron` binary's: the mark it turns off is a
                    Lean-runtime reference-counting device
                    (Runtime.markPersistent), and this checker has no
                    reference counts at all -- a term is a u32 handle into a
                    Vec and the persistent tier is immutable in phase B.  A
                    run that passes it says so on stderr.
  --progress[=<stride>]
                    opt-in progress heartbeat on STDERR, one line shape per
                    phase:
                      con-ron-arena: parse done: <N> fold records ... t=<s>s
                      con-ron-arena: install <i>/<N> <decl> t=<s>s
                      con-ron-arena: install done: <N>/<N> ..., <M> pending
                      con-ron-arena: check <done>/<M> <kind> <name> t=<s>s
                      con-ron-arena: check done: <M>/<M> t=<s>s
                      con-ron-arena: done: parse <p>s, install <i>s, check <c>s
                    An install line is printed BEFORE every <stride>-th
                    declaration is installed, so a run that dies in the
                    install phase names the declaration it died in on its last
                    line; a check line is printed AFTER every <stride>-th
                    COMPLETED check.  On a failure the phase's closing line
                    says so and the summary still prints.  Bare --progress is
                    stride 1; a stride that is not a decimal numeral, or 0, is
                    a usage error.
  --pins FILE       con-ron's own, FOR TESTING: read the pin list from a
                    `con-ron-pins/1` dump instead of the core's own embedded
                    text (task #43), through the UNVERIFIED reader.  The pins
                    are interned into the persistent tier at startup, before
                    the fold (DESIGN.md section 8.6 P2d).
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
It is the same edge `crates/con-ron` has, so the two checkers are measured on
the same allocator unless a build says otherwise.

Any other option is a usage error: the run reports it, prints this text and
exits 3 without reading its input.

exit codes: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal.
An out-of-memory condition is NEITHER: this program aborts the way Rust aborts
on a failed allocation ('memory allocation of <n> bytes failed', SIGABRT,
which a shell reports as 134).  A panic is exit 3.

THE VERDICT LINE'S COUNT.  It counts the FILE's accepted declaration RECORDS:
one per def/theorem/opaque/axiom/inductive/quot record the file declares.  The
built-in prelude's own records are not counted, and neither are the records
the in-process modeller generates; a stream record that declares a prelude
declaration IS counted.  That count is a property of the INPUT; the number of
environment CONSTANTS is not.

THE BUILT-IN PRELUDE.  Every run installs, first and unconditionally, the
checker's own little prelude -- the six pinned basis blocks (Eq, Nat, PUnit,
Empty, False, Quot) and the toolchain's Bool and And blocks, embedded at build
time -- so the pin-certified Nat operations find their ground whatever order
the export chose.  It is parsed into the SAME store as the stream, which is
what the persistent tier is for: the prelude's nodes and the stream's are
hash-consed together.

environment (con-leche's):
  CON_LECHE_INMODEL=0          turn the in-process modeller off; a mutual or
                               nested block is then pushed bare and the FOLD
                               declines it, having found no route
  CON_LECHE_INMODEL_CENSUS=1   report every mutual/nested block's outcome
                               after the parse and stop (exit 2)
  CON_LECHE_PROJREC_TRACE      name each rewritten projection function
These are the in-process modeller's debug switches and they go with it: no
environment variable this program reads can shape a verdict, which is
con-leche's own rule -- every such switch is a command-line flag.";

/// con-leche: Main.lean:946-960 Args
/// What the command line asked for — `con-ron`'s `Args`, field for field, so
/// that a script written against one binary reads against the other.
struct Args {
    files: Vec<String>,
    verified: bool,
    progress: u64,
    jobs: Option<u64>,
    no_mark: bool,
    pins: Option<String>,
    no_pins: bool,
    bad: Option<String>,
}

/// con-leche: Main.lean:962-990 parseArgs
/// The argument parse, clause for clause as `con-ron`'s: the mode flags in
/// either order with the heartbeat, `=`-carrying spellings after the bare
/// ones, an unknown `-`-leading word a usage error, everything else a file.
/// The two flag VALUES are `con_ron::driver`'s own functions, called across
/// the crate line so that the two binaries cannot drift.
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
        // The FIRST bad argument is the one reported.
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
                    match con_ron::driver::progress_stride(v) {
                        Ok(n) => a.progress = n,
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--jobs=") {
                    match con_ron::driver::jobs_count(v) {
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
/// frontend's callers report them (`con_ron`'s own `FrontendClass`).  The
/// port's fourth constructor (`CheckError::Native`, the arena's `2^27` handle
/// cap among them) is a DECLINE like `notImplemented`: the checker cannot
/// carry this input, and says so rather than rejecting the stream or claiming
/// a bug.  Deviation from the Lean twin, which maps `native` to 3; the port
/// keeps `con_ron::driver::exit_code`'s mapping so that the two Rust binaries
/// are one sweep.
enum FrontendClass {
    Declined(String),
    Invalid(String),
    Internal(String),
}

/// con-leche: none — `FrontendClass` of a `CheckError` (see there).
fn classify(e: &CheckError) -> FrontendClass {
    let m = con_ron::driver::message(e);
    match e {
        CheckError::NotImplemented(_) => FrontendClass::Declined(m),
        CheckError::Native(_) => FrontendClass::Declined(m),
        CheckError::Invalid(_) => FrontendClass::Invalid(m),
        CheckError::Internal(_) => FrontendClass::Internal(m),
    }
}

/// con-leche: none — a frontend failure's exit, one place: the decline, the
/// reject and the internal error of the two frontend gates and of the
/// preparation (con-leche writes the three arms out at each gate).
fn frontend_exit(e: &CheckError, mode_tag: &str) -> u8 {
    match classify(e) {
        FrontendClass::Declined(what) => {
            eprintln!("con-ron-arena: declined: {} ({})", what, mode_tag);
            2
        }
        FrontendClass::Invalid(what) => {
            eprintln!("con-ron-arena: invalid: {} ({})", what, mode_tag);
            1
        }
        FrontendClass::Internal(msg) => {
            eprintln!("con-ron-arena: {} ({})", msg, mode_tag);
            3
        }
    }
}

/// con-leche: Main.lean:461-711 checkMain
/// con-leche: Main.lean:53-59 parseInput
/// The driver's front matter: the prelude, the streaming parse, the
/// preparation, the pin walk, the receipts, then the fold and the verdict.
/// It is the Lean twin's `runPipelineIO` with the heartbeat and the receipts
/// around it (`Arena/Main.lean`), and `con-ron`'s `check_main` with the
/// handles in place of the trees.
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
    // ONE store for the whole run: the prelude, the stream and the pins are
    // hash-consed together into its persistent tier (DESIGN.md §8.3).
    let mut st = AState::init(EStore::empty());
    // The in-process modeller, which the parse takes as a type parameter: the
    // arena core is quantified over an arbitrary `Modeller`, and this is the
    // one the binary supplies — `crates/con-ron`'s own generator behind a
    // readback (`con_ron_arena::in_model`).
    let modeller = InProcess::new();
    // THE BUILT-IN PRELUDE, parsed into that store before anything else.
    let prelude_ix = match prelude::builtin_prelude_e(&modeller, &mut st) {
        Ok(p) => p,
        Err((e, line)) => {
            let what = match classify(&e) {
                FrontendClass::Internal(m) => format!("does not parse (line {}: {})", line, m),
                FrontendClass::Declined(w) => format!("is unsupported ({})", w),
                FrontendClass::Invalid(w) => format!("contradicts itself ({})", w),
            };
            eprintln!(
                "con-ron-arena: the built-in prelude {}; regenerate it with \
                 `lake exe natop-pins-export` ({})",
                what, mode_tag
            );
            return 3;
        }
    };
    let in_model = !env_is("CON_LECHE_INMODEL", "0");
    let census = env_is("CON_LECHE_INMODEL_CENSUS", "1");
    // Streaming frontend: the file is read 4 MiB at a time and each buffer is
    // parsed and dropped, so neither a wholesale text buffer nor a scratch
    // file exists.  What comes out is the FILE's records as HANDLES into the
    // store above (plus the in-process modeller's).
    let parsed: ParseResultD = match driver::parse_export_stream_d(
        &modeller,
        &mut st,
        file,
        in_model,
        census,
        export_c::CHUNK_SIZE,
    ) {
        Err(e) => {
            eprintln!("con-ron-arena: {}: {}", file, e);
            return 3;
        }
        Ok((Err((e, line)), _)) => match classify(&e) {
            FrontendClass::Declined(what) => {
                eprintln!("con-ron-arena: declined: {} ({})", what, mode_tag);
                return 2;
            }
            // A stream whose inductive block contradicts its own declarations
            // in a REDUNDANT field is rejected at the parse.
            FrontendClass::Invalid(what) => {
                eprintln!("con-ron-arena: invalid: {} ({})", what, mode_tag);
                return 1;
            }
            FrontendClass::Internal(msg) => {
                eprintln!("con-ron-arena: {}:{}: {}", file, line, msg);
                return 3;
            }
        },
        Ok((Ok(r), _)) => r,
    };
    // the in-process modeller's receipt
    if !parsed.in_modelled.is_empty() {
        let names: Vec<String> = parsed
            .in_modelled
            .iter()
            .map(|n| driver::name_of(&st.store, n))
            .collect();
        eprintln!(
            "con-ron-arena: {} inductive blocks modelled in-process: {} ({} generated \
             records, checked by the fold as declarations and not counted as records \
             of the file)",
            parsed.in_modelled.len(),
            names.join(", "),
            parsed.gen_records
        );
    }
    // the census (`CON_LECHE_INMODEL_CENSUS=1`): every mutual/nested block's
    // outcome, then stop — the parse only, no fold.  Exit 2, never 0.
    if census {
        for (n, why) in parsed.in_model_declined.iter() {
            eprintln!(
                "con-ron-arena: inmodel declined {}: {}",
                driver::name_of(&st.store, n),
                con_ron::render::from_cps(why)
            );
        }
        eprintln!(
            "con-ron-arena: inmodel census: {} modelled, {} declined ({}, parse only)",
            parsed.in_modelled.len(),
            parsed.in_model_declined.len(),
            mode_tag
        );
        return 2;
    }
    // the projection-function rewrite's receipt
    if !parsed.proj_rewrites.is_empty() {
        eprintln!(
            "con-ron-arena: {} projection functions of non-direct structure-likes \
             rewritten to recursor form",
            parsed.proj_rewrites.len()
        );
        if std::env::var("CON_LECHE_PROJREC_TRACE").is_ok() {
            for n in parsed.proj_rewrites.iter() {
                eprintln!("con-ron-arena:   rewritten {}", driver::name_of(&st.store, n));
            }
        }
    }
    let file_records = parsed.decls.len();
    let gen_records = parsed.gen_records;
    // From here on the store is the checker's state: the memo tables and the
    // per-declaration caches join it (`AState`), and every handle the parse
    // produced indexes into it.
    // **PREPARE** (`frontend::prepare`): what the fold runs over is
    // `prepare_prelude` of the file's records — the prelude's declarations
    // first (the stream's own copies where it has them, the rest synthesised),
    // then the stream's, with every pinned `Nat` operation's stream-certified
    // ground hoisted ahead of it.  It takes the whole state since task
    // #97-P4d: step 2 is the real ground hoist, which interns.
    let prepared = match prepare::prepare_d(&mut st, prelude_ix, parsed.decls) {
        Ok(p) => p,
        Err(e) => return frontend_exit(&e, mode_tag),
    };
    // the ground hoist's receipt
    if !prepared.hoisted.is_empty() {
        let names: Vec<String> = prepared
            .hoisted
            .iter()
            .map(|n| driver::name_of(&st.store, n))
            .collect();
        eprintln!(
            "con-ron-arena: {} declarations hoisted ahead of the pinned Nat operations \
             they ground: {}",
            prepared.hoisted.len(),
            names.join(", ")
        );
    }
    let pins = match con_ron::driver::pins_for_run(&a.pins, a.no_pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron-arena: {}", e);
            return 3;
        }
    };
    // The heartbeat's first line: the parse and the preparation are done.
    let mut hb = Heartbeat::new(a.progress, t0);
    hb.parse_done(
        prepared.decls.len(),
        file_records,
        gen_records,
        prepared.synthesised,
        (
            st.store.node_count(),
            st.store.ls().node_count(),
            st.store.ns().node_count(),
        ),
    );
    // **THE STARTUP PIN WALK** (DESIGN.md §8.6 P2d, task #97-P4d): every
    // pinned datum the checker compares a stream record against — the six
    // basis blocks in both forms, the axiom pins, the reserved names and the
    // `Nat`-operation variants — interned ONCE, here, while the scratch tier
    // is still off, so that nothing the fold compares against lives in a tier
    // that is about to vanish.  Its result is the fold's pin parameter.
    let ipins = match checker::intern_all_pins(&mut st, &pins) {
        Ok(p) => p,
        Err(e) => return frontend_exit(&e, mode_tag),
    };
    // ONE driver, and the heartbeat is printed between its steps: a plain run
    // calls `install_then_check` itself, a heartbeat run calls the same body
    // with the boundary visible (`driver::check_decls_driver`).
    let jobs: u64 = match a.jobs {
        Some(n) => n,
        None => 1,
    };
    let verdict = if a.progress > 0 {
        driver::check_decls_driver(&mut st, &mode, &ipins, &prepared.decls, jobs, &mut hb)
    } else {
        checker::install_then_check(&mut st, &mode, &ipins, &prepared.decls)
    };
    // **The headline number is the FILE's declaration-record count**: the
    // records the PARSE produced, which are the file's own, less the records
    // the in-process modeller generated.  Nothing the preparation does moves
    // it.
    let stream_records = file_records as u64 - gen_records;
    match &verdict {
        Ok(_) => driver::verdict_accept(stream_records, mode_tag),
        Err((e, i)) => {
            // A record the in-process modeller generated: the file has no
            // position for it, so the BLOCK it models is the handle.
            let owner = prepared.decls.get(*i as usize).and_then(|d| {
                i_declaration_names(d).into_iter().find_map(|n| {
                    parsed
                        .gen_owner
                        .get(&n)
                        .map(|o| driver::name_of(&st.store, o))
                })
            });
            driver::verdict_failure(
                &st.store,
                &prepared.decls,
                e,
                *i,
                owner,
                mode_tag,
                t0,
            )
        }
    }
}

/// con-leche: Main.lean:992-1019 main
/// The entry point.  The checker runs IN THIS PROCESS: it spawns no copy of
/// itself, and the whole run — parse, preparation, pin walk, fold — is on one
/// 1 GiB-stack thread, which the arena needs more than the tree checker did
/// (`driver::STACK_BYTES`).  A panic on it is exit 3, never a verdict.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|s| s == "--help") {
        println!("{}", USAGE);
        // The one build-time choice a run's numbers depend on, printed rather
        // than merely documented (task #89).
        println!("this build's global allocator: {}", con_ron_dump::ALLOCATOR);
        return ExitCode::SUCCESS;
    }
    let a = parse_args(&argv);
    if let Some(msg) = &a.bad {
        eprintln!("con-ron-arena: {}", msg);
        eprintln!("{}", USAGE);
        return ExitCode::from(3);
    }
    if a.files.len() != 1 {
        eprintln!("{}", USAGE);
        return ExitCode::from(3);
    }
    if a.no_mark {
        eprintln!("con-ron-arena: {}", driver::mark_persistent_note());
    }
    // The other accepted-and-ignored flag says so too, and says it BEFORE the
    // run rather than at the phase boundary: a log must read as the lane it
    // was, and the lane is decided here.
    if let Some(n) = a.jobs {
        if n > 1 {
            eprintln!(
                "con-ron-arena: --jobs={} accepted and clamped to 1: the arena checker's \
                 phase B is single-lane today (DESIGN.md section 8.3 has the plan, and \
                 con_ron_arena::driver's phase-B loop is shaped for it)",
                n
            );
        }
    }
    let file = a.files[0].clone();
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || check_main(&a, &file));
    match h {
        Err(e) => {
            eprintln!("con-ron-arena: cannot spawn the checking thread: {}", e);
            ExitCode::from(3)
        }
        Ok(h) => match h.join() {
            Ok(code) => ExitCode::from(code),
            Err(_) => {
                eprintln!("con-ron-arena: the checking thread died");
                ExitCode::from(3)
            }
        },
    }
}
