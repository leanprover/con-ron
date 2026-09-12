//! `con-ron` — con-leche's `Main.lean`: the command-line driver, on a **raw**
//! lean4export stream.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!         [--progress[=<stride>]] [--pins FILE] [--dump-decls OUT] FILE.ndjson
//! con-ron --help
//! ```
//!
//! It reads the file and checks the declarations in order: the built-in
//! prelude is prepended (`frontend::prelude`), the stream is parsed line by
//! line off the handle (`frontend::export_c`), mutual and nested inductive
//! blocks get their `_model` family generated in process (`in_model`), the
//! Nat-operation ground is hoisted and the projection functions rewritten, and
//! the resulting `Vec<DeclC>` goes to the driver — `con_ron::driver`, which is
//! `con_ron_core::cached::installed::check_decls`' body with the phase
//! boundary visible, the fold DESIGN.md §1's main theorem is about.
//!
//! **This binary is the one true driver** (task #40): everything from the
//! parsed list on — the exit-code mapping, the two phase loops, the
//! `--progress` heartbeat, the taint-skip rule, the verdict lines — lives in
//! `con_ron::driver` and is shared with `con-ron-check`, which is the same
//! driver reading a `con-ron-decls/1` dump instead of a stream.  What is here
//! is this binary's own front matter: the flags, the prelude, the parse, the
//! receipts.
//!
//! Exit codes are con-leche's (`vendor/con-leche/Main.lean:15-31`, its
//! `OVERVIEW.md` §0): 0 accepted, 1 rejected, 2 declined, 3
//! usage/malformed/internal.  `driver`'s module note has the table, and the
//! two conventions that are not exit codes — out of memory (con-leche's
//! exit 1 is a Lean-runtime panic the port cannot reproduce: a Rust allocation
//! failure aborts, which a shell reports as 134) and a panic, which is 3.
//!
//! **NO TEMPORARY FILES** (con-leche task #180).  The checker writes nothing
//! outside its own stdout/stderr — and `--dump-decls OUT`, which is con-ron's
//! own flag, writes only where the user named — and reads its input strictly
//! forward, 4 MiB at a time, so a Mathlib-scale export never materialises
//! anywhere.
//!
//! **Four flags differ from con-leche's, and say so here.**
//!
//! * `--jobs=<n>` is **accepted and validated but not acted on**: the check
//!   phase is sequential in this build.  con-leche's thread pool waits on a
//!   thread-shareable handle, whose price task #44 measured (DESIGN.md;
//!   `driver`'s note), so a
//!   run prints `con-ron: --jobs=<n> accepted; the check phase is sequential
//!   in this build` and the `--progress` summary says `1 worker` — no log can
//!   mistake a sequential run for a pooled one.
//! * `--no-mark-persistent` is **accepted and a no-op**, and a run that passes
//!   it says why: the mark it turns off is a Lean-runtime reference-counting
//!   device (`Runtime.markPersistent`), and the port's counts are its own
//!   non-atomic `Rc` counts with no runtime mark to clear
//!   (`driver::mark_persistent_note`).  It is accepted rather than rejected so
//!   that a script measuring both checkers can pass it to both.
//! * `--pins FILE` is con-ron's own, and is DESIGN.md §3.6's pin-list
//!   parameter (task #31): con-leche carries `natOpPinSets` as kernel data
//!   computed at elaboration time, and the port takes it as an argument of
//!   `check_decls`.  Without the flag the list is empty, which is the `[]` arm
//!   of the pin loop — a `Nat.div`/`Nat.mod` stream then declines with
//!   "unsupported Nat.div/mod spelling", exactly as con-leche does for a
//!   stream matching no variant.  `scripts/diff-e2e.sh` passes the dump
//!   `scripts/dump-fixtures.sh` writes.
//! * `--dump-decls OUT` is con-ron's own too: it writes the parsed
//!   `Vec<DeclC>` in the `con-ron-decls/1` format (task #10's specification,
//!   task #19's byte-exact writer) and exits without folding.  That is the
//!   oracle of `scripts/diff-frontend.sh`: the bytes must equal the Lean
//!   frontend's.
//!
//! Every retired con-leche spelling — `--set-model[=p|=r]`, `--no-model`,
//! `--tt-model`, `--yolo`, `--infer-only`, `--pre`, `--core[=<c>]`,
//! `--install-only`, `--check-range[=<r>]` — is a hard error here too, with
//! the message naming its replacement, for con-leche's reason: a verdict's
//! provenance must be readable off the invocation, so a retired spelling is
//! never a silent alias (`driver::retired_flag`).

use std::io::Write;
use std::process::ExitCode;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

use con_ron::driver;
use con_ron::driver::Heartbeat;
use con_ron::driver::STACK_BYTES;
use con_ron::frontend::export::{name_str, taint_detail, taint_summary, FrontendError};
use con_ron::frontend::export_c::{self, ParseResultD};
use con_ron::frontend::nat_op_ground::{decl_names, NameKey};
use con_ron::frontend::prelude;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for the `con-ron-decls/1` writer of `--dump-decls` and
// the `con-ron-pins/1` reader of `--pins`.  So `con-ron` declares none, and
// `cargo build --no-default-features` gives glibc `malloc` back to both.

/// con-leche: Main.lean:791-1039 usage
/// The usage text.  DESIGN.md §3.1: message strings need not match, and this
/// one deliberately does not — it is con-leche's synopsis plus the four flags
/// that differ and the one piece of `Main.lean` that is not ported.
const USAGE: &str = "\
usage: con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
               [--progress[=<stride>]] [--pins FILE] [--dump-decls OUT]
               FILE.ndjson
       con-ron --help

  --verified        the default, and the mode the main theorem is about: if
                    the declaration fold accepts a stream in this mode, the
                    environment holds no constant whose type is False
                    (ConLeche.no_proof_of_False, and DESIGN.md §1's
                    conron.no_proof_of_False for the port).
  --trusted         the unverified mode: the SAME checker bodies at the mode
                    with the certification-only work switched off.  An accept
                    in this mode is outside the theorem.
  --jobs=<n>        ACCEPTED AND VALIDATED, then not acted on: the check phase
                    is sequential in this build, and the --progress summary
                    says `1 worker` whatever <n> was.  The pool needs a
                    thread-shareable handle, whose price task #44 measured
                    (DESIGN.md); 0 or a non-numeral is a usage error, as in
                    con-leche.
  --no-mark-persistent
                    ACCEPTED AND A NO-OP: the mark it turns off is a
                    Lean-runtime reference-counting device
                    (Runtime.markPersistent), and this program's counts are
                    its own non-atomic Rc counts with no runtime mark to
                    clear.  A run that passes it says so on stderr.
  --progress[=<stride>]
                    opt-in progress heartbeat on STDERR, one line shape per
                    phase:
                      con-ron: parse done: <N> fold records ... t=<s>s
                      con-ron: install <i>/<N> <decl> t=<s>s
                      con-ron: install done: <N>/<N> ..., <M> checks pending t=<s>s
                      con-ron: check <done>/<M> <kind> <name> t=<s>s
                      con-ron: check done: <M>/<M> t=<s>s
                      con-ron: done: parse <p>s, install <i>s, check <c>s, 1 worker
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
  --pins FILE       con-ron's own: the `con-ron-pins/1` dump of con-leche's
                    `natOpPinSets` (DESIGN.md §3.6, task #31).  Without it
                    the pin list is empty and a Nat.div/Nat.mod stream
                    declines.
  --dump-decls OUT  con-ron's own: write the parsed declaration list in the
                    `con-ron-decls/1` format and exit, without folding.
  --help            print this text on STDOUT and exit 0, in any argument
                    position; no input is read.

exit codes: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal.
An out-of-memory condition is NEITHER: con-leche's exit 1 for it is the Lean
runtime's own panic, and this program instead aborts the way Rust aborts on a
failed allocation ('memory allocation of <n> bytes failed', SIGABRT, which a
shell reports as 134).  A panic is exit 3.

environment (con-leche's):
  CON_LECHE_INMODEL=0          turn the in-process modeller off; a mutual or
                               nested block is then pushed bare and the FOLD
                               declines it, having found no route
  CON_LECHE_INMODEL_CENSUS=1   report every mutual/nested block's outcome
                               after the parse and stop (exit 2)
  CON_LECHE_PROJREC_TRACE      name each rewritten projection function
  CON_LECHE_VERBOSE            print the environment's constant count

RETIRED FLAGS.  --set-model, --set-model=p, --set-model=r, --no-model,
--tt-model, --yolo, --infer-only, --pre, --core, --core=<c>, --install-only,
--check-range and --check-range=<r> are never silent aliases: each is
rejected with a message naming what stands in its place, and the run exits 3
without reading the input, so a verdict's provenance is readable off the
invocation.

NOT PORTED: CON_LECHE_ROUTE_TRACE, the install-route audit (it reads the
recognisers on the environment the step sees, which is a second dispatch of
the fold, not a print); CON_LECHE_INMODEL_DUMP, the debug splice of the
generated records into a copy of the input — it is written through
con-leche's annotated-NDJSON writer (`Frontend/ExportWrite.lean`), an output
path this checker does not have; and the worker pool of --jobs (above).";

/// con-leche: Main.lean:1041-1055 Args
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
    dump_decls: Option<String>,
    bad: Option<String>,
}

/// con-leche: Main.lean:1057-1149 parseArgs
/// The argument parse.  The retired spellings are hard errors, not silently
/// ignored (`driver::retired_flag` holds all thirteen with their messages):
/// a verdict's provenance must be readable off the invocation.
fn parse_args(argv: &[String]) -> Args {
    let mut a = Args {
        files: Vec::new(),
        verified: true,
        progress: 0,
        jobs: None,
        no_mark: false,
        pins: None,
        dump_decls: None,
        bad: None,
    };
    let mut i = 0usize;
    while i < argv.len() {
        let s = argv[i].as_str();
        // The FIRST bad argument is the one reported, as con-leche's fold
        // reports the first `bad` it set.
        if let Some(m) = driver::retired_flag(s) {
            if a.bad.is_none() {
                a.bad = Some(m);
            }
            i += 1;
            continue;
        }
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
            "--pins" => {
                i += 1;
                if i >= argv.len() {
                    bad("--pins takes a file: --pins FILE".to_string(), &mut a);
                } else {
                    a.pins = Some(argv[i].clone());
                }
            }
            "--dump-decls" => {
                i += 1;
                if i >= argv.len() {
                    bad(
                        "--dump-decls takes an output file: --dump-decls OUT".to_string(),
                        &mut a,
                    );
                } else {
                    a.dump_decls = Some(argv[i].clone());
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
                } else if let Some(v) = s.strip_prefix("--dump-decls=") {
                    a.dump_decls = Some(v.to_string());
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

/// con-leche: none — DESIGN.md §3.6's pin-list parameter of `check_decls`
/// (task #31): con-leche's `natOpPinSets` is kernel data computed at
/// elaboration time, and the port takes it as runtime data.
fn read_pins(path: &Option<String>) -> Result<Vec<NatOpPinSet>, String> {
    match path {
        None => Ok(Vec::new()),
        Some(p) => {
            let text = std::fs::read_to_string(p).map_err(|e| format!("{}: {}", p, e))?;
            con_ron_dump::parse_pins(&text).map_err(|e| format!("{}: {}", p, e))
        }
    }
}

/// con-leche: Main.lean:493-788 checkMain
/// con-leche: Main.lean:53-59 parseInput
/// The real driver's front matter: the retired environment gates, the
/// prelude, the streaming parse, the receipts, then `driver` for the fold and
/// the verdict.  `--dump-decls` returns before the fold.
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
    // The retired environment variables are hard errors, not silently
    // ignored, for the retired flags' reason.
    if env_is("CON_LECHE_NO_PROOF_CERTS", "1") {
        eprintln!(
            "con-ron: CON_LECHE_NO_PROOF_CERTS is retired; the cert-skipping \
             measurement lane is the --trusted mode"
        );
        return 3;
    }
    if env_is("CON_LECHE_INFER_ONLY", "1") {
        eprintln!(
            "con-ron: CON_LECHE_INFER_ONLY is retired; the infer-only internal \
             discipline is part of the --trusted mode, and the certified mode is \
             --verified, the default"
        );
        return 3;
    }
    // THE BUILT-IN PRELUDE: parsed from the committed
    // `pins/<toolchain>.prelude.ndjson` and PREPENDED to every parsed stream.
    // A prelude that does not parse is a corrupted build, reported before any
    // input is read.
    let prelude_ix = match prelude::builtin_prelude_e() {
        Ok(p) => p,
        Err(e) => {
            let what = match e {
                FrontendError::ParseError(l, m) => format!("does not parse (line {}: {})", l, m),
                FrontendError::Unsupported(w) => format!("is unsupported ({})", w),
                FrontendError::Invalid(w) => format!("contradicts itself ({})", w),
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
    // neither a wholesale text buffer nor a scratch file exists.
    let parsed: ParseResultD = match export_c::parse_export_stream_d(
        file,
        prelude_ix,
        in_model,
        census,
        export_c::CHUNK_SIZE,
    ) {
        Err(e) => {
            eprintln!("con-ron: {}: {}", file, e);
            return 3;
        }
        Ok(Err(FrontendError::Unsupported(what))) => {
            eprintln!("con-ron: declined: {} ({})", what, mode_tag);
            return 2;
        }
        Ok(Err(FrontendError::Invalid(what))) => {
            eprintln!("con-ron: invalid: {} ({})", what, mode_tag);
            return 1;
        }
        Ok(Err(FrontendError::ParseError(line, msg))) => {
            eprintln!("con-ron: {}:{}: {}", file, line, msg);
            return 3;
        }
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
            eprintln!("con-ron: inmodel declined {}: {}", name_str(n), why);
        }
        eprintln!(
            "con-ron: inmodel census: {} modelled, {} declined ({}, parse only)",
            parsed.in_modelled.len(),
            parsed.in_model_declined.len(),
            mode_tag
        );
        return 2;
    }
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
    // the ground hoist's receipt
    if !parsed.hoisted.is_empty() {
        let names: Vec<String> = parsed.hoisted.iter().map(name_str).collect();
        eprintln!(
            "con-ron: {} declarations hoisted ahead of the pinned Nat operations \
             they ground: {}",
            parsed.hoisted.len(),
            names.join(", ")
        );
    }
    let t_parse = t0.elapsed();
    // `--dump-decls OUT`: the parsed list in the `con-ron-decls/1` format,
    // and no fold.  This is `scripts/diff-frontend.sh`'s oracle.
    if let Some(out) = &a.dump_decls {
        let text = con_ron_dump::dump_decls(&parsed.decls);
        let n = text.len();
        match std::fs::File::create(out).and_then(|mut f| f.write_all(text.as_bytes())) {
            Err(e) => {
                eprintln!("con-ron: {}: {}", out, e);
                return 3;
            }
            Ok(()) => {}
        }
        eprintln!(
            "con-ron: dumped {} records ({} bytes) to {}  parse {:.3}s",
            parsed.decls.len(),
            n,
            out,
            t_parse.as_secs_f64()
        );
        return 0;
    }
    let pins = match read_pins(&a.pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return 3;
        }
    };
    // The heartbeat's first line: the parse is done, and the fold is about to
    // start on this many records.  The two phases print their own lines and
    // the summary closes the run (`driver::Heartbeat`).
    let mut hb = Heartbeat::new(a.progress, t0);
    hb.parse_done(
        parsed.decls.len(),
        parsed.prelude_count,
        parsed.prelude_dropped,
    );
    // ONE driver, and the heartbeat is printed between its steps: a plain run
    // calls `check_decls` itself, a heartbeat run calls the same body with the
    // boundary visible (`driver::check_decls_driver`), and the verdict below
    // is printed from an accept of `check_decls` and from nothing else.
    let verdict = if a.progress > 0 {
        driver::check_decls_driver(&mode, &pins, &parsed.decls, &mut hb)
    } else {
        installed::check_decls(&mode, &pins, &parsed.decls)
    };
    // **The headline number is the STREAM's declaration-record count**: the
    // records the fold consumed minus the built-in prelude's, plus the stream
    // records dropped as identical copies of prelude records (they ARE
    // installed — from the prelude), minus the records the in-process
    // modeller generated (they are checked as declarations, but they are not
    // in the file).
    let stream_records = parsed.decls.len() as u64 - parsed.prelude_count
        + parsed.prelude_dropped
        - parsed.gen_records;
    match &verdict {
        Ok(envr) => {
            let detail = taint_detail(&parsed.taint_skipped);
            let code = driver::verdict_accept(
                stream_records,
                parsed.taint_skipped.len(),
                Some(&detail),
                mode_tag,
            );
            if std::env::var("CON_LECHE_VERBOSE").is_ok() {
                eprintln!(
                    "con-ron: environment: {} constants from {} fold records \
                     ({} built-in prelude records, {} stream copies of them dropped)",
                    envr.consts.len(),
                    parsed.decls.len(),
                    parsed.prelude_count,
                    parsed.prelude_dropped
                );
            }
            code
        }
        Err((e, i)) => {
            // A record the in-process modeller generated: the file has no
            // position for it, so the BLOCK it models is the handle.
            let owner = parsed.decls.get(*i as usize).and_then(|d| {
                decl_names(d)
                    .into_iter()
                    .find_map(|n| parsed.gen_owner.get(&NameKey(n)).map(name_str))
            });
            let code = driver::verdict_failure(&parsed.decls, e, *i, owner, mode_tag, t0);
            // On a stream that also FAILED, the skips are reported beside the
            // failure and the failure's own exit code stands.
            if !parsed.taint_skipped.is_empty() {
                eprintln!(
                    "con-ron: declined: {} ({})",
                    taint_summary(&parsed.taint_skipped),
                    mode_tag
                );
            }
            code
        }
    }
}

/// con-leche: Main.lean:1151-1183 main
/// The entry point.  The checker runs IN THIS PROCESS (con-leche task #230
/// removed the out-of-memory supervisor that used to re-exec it), on one
/// big-stack thread; a panic on it is exit 3, never a verdict.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|s| s == "--help") {
        println!("{}", USAGE);
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
    if let Some(n) = a.jobs {
        eprintln!(
            "con-ron: --jobs={} accepted; the check phase is sequential in this build \
             (a pool needs a thread-shareable handle; see DESIGN.md task #44)",
            n
        );
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
