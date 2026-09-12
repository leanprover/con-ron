//! `con-ron` — con-leche's `Main.lean`: the command-line driver.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]]
//!         [--pins FILE] [--dump-decls OUT] FILE.ndjson
//! con-ron --help
//! ```
//!
//! It reads a **raw** lean4export NDJSON file and checks the declarations in
//! order: the built-in prelude is prepended (`frontend::prelude`), the stream
//! is parsed line by line off the handle (`frontend::export_c`), the
//! Nat-operation ground is hoisted and the projection functions rewritten,
//! and the resulting `Vec<DeclC>` goes to `con_ron_core::cached::installed::
//! check_decls` — the fold DESIGN.md §1's main theorem is about.
//!
//! Exit codes are con-leche's (`vendor/con-leche/Main.lean:15-31`, its
//! `OVERVIEW.md` §0):
//!
//! | exit | verdict |
//! |---|---|
//! | 0 | all declarations accepted |
//! | 1 | a declaration was rejected as invalid |
//! | 2 | the checker declined: it positively detected a feature it does not support |
//! | 3 | bad usage, malformed input, or an internal failure of unclear cause |
//!
//! **NO TEMPORARY FILES** (con-leche task #180).  The checker writes nothing
//! outside its own stdout/stderr — and `--dump-decls OUT`, which is con-ron's
//! own flag, writes only where the user named — and reads its input strictly
//! forward, 4 MiB at a time, so a Mathlib-scale export never materialises
//! anywhere.
//!
//! **Three flags differ from con-leche's, and say so here.**
//!
//! * `--jobs=<n>` is **accepted and validated but ignored**: the check phase
//!   is sequential in this build.  con-leche's thread pool is DESIGN.md §1's
//!   last cherry and is not part of task #37; a run prints
//!   `con-ron: --jobs=<n> accepted; the check phase is sequential in this
//!   build` so no log can mistake a sequential run for a pooled one.
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
//! The retired con-leche spellings (`--yolo`, `--pre`, `--core`,
//! `--install-only`, `--check-range`, `--infer-only`) are hard errors here
//! too, for con-leche's reason: a verdict's provenance must be readable off
//! the invocation.

use std::io::Write;
use std::process::ExitCode;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::cached::parsed_c::PendingCheck;
use con_ron_core::cached::state_c;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::env::Env;
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

use con_ron::frontend::export::{name_str, taint_detail, taint_summary, FrontendError};
use con_ron::frontend::export_c::{self, ParseResultD};
use con_ron::frontend::prelude;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for the `con-ron-decls/1` writer of `--dump-decls` and
// the `con-ron-pins/1` reader of `--pins`.  So `con-ron` declares none, and
// `cargo build --no-default-features` gives glibc `malloc` back to both.

/// con-leche: none — the Lean runtime's per-thread stack reservation, which
/// `Main.lean`'s `--jobs` note measures at 1 GiB per worker.  The fold's
/// recursion depth is the term DAG's, and so is the frontend's
/// (`canon_expr_eq_fast`, `occurs_const_go`), so the whole run is on one.
const STACK_BYTES: usize = 1 << 30;

/// con-leche: Main.lean:791-1039 usage
/// The usage text.  DESIGN.md §3.1: message strings need not match, and this
/// one deliberately does not — it documents the three flags that differ (the
/// module note) and the one piece of `Main.lean` that is not ported.
const USAGE: &str = "\
usage: con-ron [--verified|--trusted] [--jobs=<n>] [--progress[=<stride>]]
               [--pins FILE] [--dump-decls OUT] FILE.ndjson
       con-ron --help

  --verified        the default, and the mode the main theorem is about.
  --trusted         the unverified mode: the same checker bodies at the
                    mode with the certificate checks off.
  --jobs=<n>        ACCEPTED AND IGNORED in this build: the check phase is
                    sequential (con-leche's thread pool is not ported yet).
                    A decimal numeral of at least 1; 0 and a non-numeral are
                    usage errors, as in con-leche.
  --progress[=<stride>]
                    one stderr line per <stride> declarations of each phase;
                    bare --progress is stride 1, which announces every
                    declaration before installing it, so a run that dies
                    names the declaration it died in.
  --pins FILE       con-ron's own: the `con-ron-pins/1` dump of con-leche's
                    `natOpPinSets` (DESIGN.md §3.6, task #31).  Without it
                    the pin list is empty and a Nat.div/Nat.mod stream
                    declines.
  --dump-decls OUT  con-ron's own: write the parsed declaration list in the
                    `con-ron-decls/1` format and exit, without folding.
  --help            this text.

exit codes: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal.

environment (con-leche's):
  CON_LECHE_INMODEL=0          turn the in-process modeller off; a mutual or
                               nested block is then pushed bare and the FOLD
                               declines it, having found no route
  CON_LECHE_INMODEL_CENSUS=1   report every mutual/nested block's outcome
                               after the parse and stop (exit 2)
  CON_LECHE_PROJREC_TRACE      name each rewritten projection function
  CON_LECHE_VERBOSE            print the environment's constant count

NOT PORTED: CON_LECHE_INMODEL_DUMP, the debug splice of the generated
records into a copy of the input — it is written through con-leche's
annotated-NDJSON writer (`Frontend/ExportWrite.lean`), an output path this
checker does not have.";

/// con-leche: Main.lean:48-51 ConLeche.CheckError.exitCode
fn exit_code(e: &CheckError) -> u8 {
    match e {
        CheckError::NotImplemented(_) => 2,
        CheckError::Invalid(_) => 1,
        CheckError::Internal(_) => 3,
    }
}

/// con-leche: none — rendering a `CheckError`'s payload, which
/// `core_types` carries as a `Vec<u32>` of code points (DESIGN.md §3.4) where
/// Lean carries a `String`.
fn message(e: &CheckError) -> String {
    let cps: &Vec<u32> = match e {
        CheckError::NotImplemented(m) => m,
        CheckError::Invalid(m) => m,
        CheckError::Internal(m) => m,
    };
    cps.iter()
        .map(|c| char::from_u32(*c).unwrap_or('\u{fffd}'))
        .collect()
}

/// con-leche: ConLeche/Cached/ParsedC.lean:249-257 declCLabel
/// con-leche: Main.lean:61-65 declCName
/// A parsed declaration's display label.  DESIGN.md §3.7's skip list keeps it
/// out of the verified core as driver-only rendering ("the theorem never reads
/// a message"), so the driver carries it.  Deviation: `basisDecl` renders as
/// `basis` rather than `basis block <repr k>` (the port has no `Repr`).
fn decl_label(d: &DeclC) -> String {
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

/// con-leche: ConLeche/Cached/ParsedC.lean:245-247 msSecs
/// Milliseconds as seconds.  Also a deliberate skip in the core.  Deviation:
/// three decimals rather than con-leche's one.
fn ms_secs(ms: u128) -> String {
    format!("{}.{:03}", ms / 1000, ms % 1000)
}

/// con-leche: Main.lean:451-466 progressStride
/// The progress heartbeat's stride: no flag is off; bare `--progress` is
/// stride 1.  A value that is not a decimal numeral, and `0` — the flag asking
/// for no heartbeat — are usage errors, per the provenance discipline the
/// retired spellings follow: a run's output must be readable off its
/// invocation, never silently degraded.
fn progress_stride(v: &str) -> Result<u64, String> {
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

/// con-leche: Main.lean:468-491 jobsCount
/// The worker count: a decimal numeral of at least 1.  Validated exactly as
/// con-leche validates it, and then ignored — the check phase is sequential in
/// this build (the module note).
fn jobs_count(v: &str) -> Result<u64, String> {
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

/// con-leche: Main.lean:1041-1055 Args
/// What the command line asked for.  `noMark` is not here: it turns off the
/// pool's persistent mark, and there is no pool.
struct Args {
    files: Vec<String>,
    verified: bool,
    progress: u64,
    jobs: Option<u64>,
    pins: Option<String>,
    dump_decls: Option<String>,
    bad: Option<String>,
}

/// con-leche: Main.lean:1057-1149 parseArgs
/// The argument parse.  The retired spellings are hard errors, not silently
/// ignored: a verdict's provenance must be readable off the invocation.
fn parse_args(argv: &[String]) -> Args {
    let mut a = Args {
        files: Vec::new(),
        verified: true,
        progress: 0,
        jobs: None,
        pins: None,
        dump_decls: None,
        bad: None,
    };
    let mut i = 0usize;
    while i < argv.len() {
        let s = argv[i].as_str();
        let bad = |m: String, a: &mut Args| {
            if a.bad.is_none() {
                a.bad = Some(m);
            }
        };
        match s {
            "--verified" => a.verified = true,
            "--trusted" => a.verified = false,
            "--progress" => a.progress = 1,
            "--no-mark-persistent" => {}
            "--yolo" => bad(
                "--yolo is retired; the cert-skipping lane is --trusted".to_string(),
                &mut a,
            ),
            "--infer-only" => bad(
                "--infer-only is retired; its discipline is part of --trusted, and the \
                 certified mode is --verified (default)"
                    .to_string(),
                &mut a,
            ),
            "--pre" => bad(
                "--pre is retired; there is no preprocessor — every input is a raw \
                 lean4export stream"
                    .to_string(),
                &mut a,
            ),
            "--core" => bad(
                "--core is retired; there is one core and one expression representation"
                    .to_string(),
                &mut a,
            ),
            "--install-only" | "--check-range" => bad(
                format!("{} is retired; the split install/check driver was arena machinery", s),
                &mut a,
            ),
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
                    match progress_stride(v) {
                        Ok(n) => a.progress = n,
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--jobs=") {
                    match jobs_count(v) {
                        Ok(n) => a.jobs = Some(n),
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--pins=") {
                    a.pins = Some(v.to_string());
                } else if let Some(v) = s.strip_prefix("--dump-decls=") {
                    a.dump_decls = Some(v.to_string());
                } else if s.starts_with("--core=") || s.starts_with("--check-range=") {
                    bad(format!("{} is retired", s), &mut a);
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

/// con-leche: Main.lean:67-158 installLoop
/// con-leche: Main.lean:176-206 checkLoop
/// con-leche: Main.lean:330-449 checkDeclsIO
/// con-leche: ConLeche/Cached/Installed.lean:405-411 checkDecls
/// `check_decls`' body with the phase boundary visible, so `--progress` can
/// announce each declaration of phase A before it is installed and each
/// completed check of phase B.  The verdict is `check_decls`' — this IS its
/// body, step for step, which is why the flag changes no outcome and why ONE
/// loop serves the plain run and the heartbeat alike.
///
/// Three deviations from `checkDeclsIO`: the `Prop`-indexed driver evidence
/// (`InstallRun`, `GroupChecked`, `FullyChecked`) is not ported — DESIGN.md
/// §3.7's skip list has that family, and `installed.rs`'s module note says
/// why; there is no thread pool (`checkPool`), so phase B is the sequential
/// `checkLoop`; and phase B runs on the same thread as phase A rather than a
/// dedicated one (con-leche task #269's allocator finding, which is about
/// Lean's per-thread heaps).
fn check_decls_progress(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    ds: &Vec<DeclC>,
    stride: u64,
    t0: Instant,
) -> Result<Env, (CheckError, u64)> {
    let mut st: CState = state_c::cstate_new();
    let mut p: (u64, FEnv, Vec<PendingCheck>) = (0, fenv::mk_fenv(env::empty()), Vec::new());
    let total = ds.len();
    let mut i = 0usize;
    while i < total {
        if stride > 0 && p.0 % stride == 0 {
            eprintln!(
                "con-ron: install {}/{} {} t={}s",
                p.0,
                total,
                decl_label(&ds[i]),
                ms_secs(t0.elapsed().as_millis())
            );
        }
        match installed::annot_decl_step(mode, pins, &mut st, p, &ds[i]) {
            Err(e) => return Err(e),
            Ok(q) => p = q,
        }
        i += 1;
    }
    let pend: Vec<PendingCheck> = p.2;
    let mut fe: FEnv = p.1;
    let n_pend = pend.len();
    let mut j = 0usize;
    while j < n_pend {
        let mut stb: CState = state_c::cstate_new();
        match installed::check_pending(mode, &mut stb, fe, &pend[j]) {
            Err(e) => return Err((e, pend[j].pos)),
            Ok(fe2) => fe = fe2,
        }
        j += 1;
        if stride > 0 && (j as u64) % stride == 0 {
            eprintln!(
                "con-ron: check {}/{} t={}s",
                j,
                n_pend,
                ms_secs(t0.elapsed().as_millis())
            );
        }
    }
    Ok(fe.env)
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
/// The real driver: the prelude, the streaming parse, the receipts, the fold
/// and the verdict line.  `--dump-decls` returns before the fold.
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
    if env_is("CON_LECHE_NO_PROOF_CERTS", "1") {
        eprintln!(
            "con-ron: CON_LECHE_NO_PROOF_CERTS is retired; the cert-skipping \
             measurement lane is the --trusted mode"
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
    if a.progress > 0 {
        eprintln!(
            "con-ron: parse done: {} fold records — {} declarations after the {} \
             built-in prelude records ({} stream copies of prelude records dropped) \
             t={}s",
            parsed.decls.len(),
            parsed.decls.len() as u64 - parsed.prelude_count,
            parsed.prelude_count,
            parsed.prelude_dropped,
            ms_secs(t_parse.as_millis())
        );
    }
    let t1 = Instant::now();
    let verdict = if a.progress > 0 {
        check_decls_progress(&mode, &pins, &parsed.decls, a.progress, t0)
    } else {
        installed::check_decls(&mode, &pins, &parsed.decls)
    };
    let t_check = t1.elapsed();
    // **The headline number is the STREAM's declaration-record count**: the
    // records the fold consumed minus the built-in prelude's, plus the stream
    // records dropped as identical copies of prelude records (they ARE
    // installed — from the prelude), minus the records the in-process
    // modeller generated (they are checked as declarations, but they are not
    // in the file).
    let stream_records = parsed.decls.len() as u64 - parsed.prelude_count
        + parsed.prelude_dropped
        - parsed.gen_records;
    let code = match &verdict {
        Ok(envr) => {
            // A DECLINED stream never says "accepted": declarations using
            // tolerated axioms were skipped at parse, so nothing tainted was
            // checked or installed, and a clean run over the rest is still not
            // an acceptance of the stream.
            if parsed.taint_skipped.is_empty() {
                println!(
                    "con-ron: accepted {} declarations ({})",
                    stream_records, mode_tag
                );
            } else {
                eprintln!(
                    "con-ron: declined ({} declarations checked, {} skipped for \
                     tolerated axioms) ({}): {}",
                    stream_records,
                    parsed.taint_skipped.len(),
                    mode_tag,
                    taint_detail(&parsed.taint_skipped)
                );
            }
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
            if parsed.taint_skipped.is_empty() {
                0
            } else {
                2
            }
        }
        Err((e, i)) => {
            // `i` is the FOLD position, and it is NOT the stream's
            // declaration-record index: the parse folds the four `quot`
            // records into one `basisDecl` and drops a few others.  The
            // declaration NAME on the line is the portable handle.
            let loc = match parsed.decls.get(*i as usize) {
                Some(d) => format!(" [at {}, fold position {}]", decl_label(d), i),
                None => format!(" [at fold position {}]", i),
            };
            eprintln!(
                "con-ron: {}{} ({}) t={}s",
                message(e),
                loc,
                mode_tag,
                ms_secs(t0.elapsed().as_millis())
            );
            if !parsed.taint_skipped.is_empty() {
                eprintln!(
                    "con-ron: declined: {} ({})",
                    taint_summary(&parsed.taint_skipped),
                    mode_tag
                );
            }
            exit_code(e)
        }
    };
    if a.progress > 0 {
        eprintln!(
            "con-ron: done: parse {}s check {}s total {}s",
            ms_secs(t_parse.as_millis()),
            ms_secs(t_check.as_millis()),
            ms_secs(t0.elapsed().as_millis())
        );
    }
    code
}

/// con-leche: Main.lean:1151-1183 main
/// The entry point.  The checker runs IN THIS PROCESS (con-leche task #230
/// removed the out-of-memory supervisor that used to re-exec it), on one
/// big-stack thread.
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
             (con-leche's thread pool is not ported yet)",
            n
        );
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
