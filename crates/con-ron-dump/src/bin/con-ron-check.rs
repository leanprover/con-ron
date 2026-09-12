//! `con-ron-check` — run the ported checker over a `con-ron-decls/1` dump and
//! print con-leche's verdict.
//!
//! The driver half of DESIGN.md §3.6's differential seam (task #28).  The
//! dump is the *parsed* declaration list con-leche's own frontend produced
//! (`lake exe con-ron-dump`, task #10), so this tool is exactly con-leche's
//! `Main.lean` minus the frontend: read the records, run the fold, print the
//! verdict line, exit with con-leche's code.
//!
//! ```text
//! con-ron-check [--verified|--trusted] [--pins FILE] [--taint-skipped N]
//!               [--stats] [--quiet] FILE.decls
//! ```
//!
//! The verdict vocabulary and the exit codes are con-leche's
//! (`vendor/con-leche/OVERVIEW.md` §0, `Main.lean:48-51,744-788`):
//!
//! | exit | verdict |
//! |---|---|
//! | 0 | `accepted N declarations` — every declaration checked |
//! | 1 | `rejected` — `CheckError.invalid`: a declaration is invalid |
//! | 2 | `declined` — `CheckError.notImplemented`, or the taint-skip rule |
//! | 3 | error — `CheckError.internal`, bad usage, malformed dump |
//!
//! Three details this driver mirrors deliberately:
//!
//! * **The taint-skip decline** (`Main.lean:637-645,749-753`): a clean fold
//!   over a stream from which the frontend *skipped* declarations for
//!   tolerated axioms is still a decline — "uses of tolerated axioms are
//!   never accepted".  The skip count is frontend state and is **not** in the
//!   dump (task #10's surprise 9), so it is a parameter here,
//!   `--taint-skipped N`; the core (`check_decls`) must not know the rule.
//! * **`N` counts declaration records.**  con-leche subtracts its built-in
//!   prelude and the generated inductive model records from `decls.size`; the
//!   dump has already absorbed the prelude, so `N` here is the dump's record
//!   count and the two numbers differ by the prelude.  Nothing compares them
//!   — con-leche's expectation files pin the exit code alone
//!   (`vendor/con-leche/tests/*-expected.txt`).
//! * **The fold position** is printed with a failure, as `Main.lean:786-788`
//!   does, because it is what `check_decls` returns beside the error; the
//!   expectation files do not record it, so `scripts/diff-fixtures.sh`
//!   compares it only against another con-ron run.
//!
//! `--pins FILE` is the §3.6 pin-list parameter.  It is accepted and
//! reported, but no pins-dump *reader* exists yet (con-leche's
//! `pins/*.json` is `con-leche-natop-pins/3`, a different format from
//! `con-ron-decls/1`), and `check_decls`' `pins` argument is not yet threaded
//! to the pin loop either (`cached::installed`'s deviation 4), so the run is
//! the empty pin list whatever the flag says: a `Nat.div`/`Nat.mod` stream
//! declines.  Both halves are task #22's.
//!
//! The fold runs on a thread with a **1 GiB stack**: `check_decls`, like
//! con-leche's, is deep recursion over the term DAG, and con-leche reserves
//! 1 GiB per worker for exactly this.

use std::process::ExitCode;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::cached::state_c;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::env::Env;
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;
use con_ron_dump::parse_decls;

const USAGE: &str = "usage: con-ron-check [--verified|--trusted] [--pins FILE] \
                     [--taint-skipped N] [--stats] [--quiet] FILE.decls";

/// con-leche reserves 1 GiB of stack per checking worker; the fold's
/// recursion depth is the term DAG's, so the port needs the same.
const STACK_BYTES: usize = 1 << 30;

/// What the command line asked for.
struct Args {
    path: String,
    mode: CheckMode,
    mode_tag: &'static str,
    pins: Option<String>,
    taint_skipped: u64,
    stats: bool,
    quiet: bool,
}

/// A `CheckError`'s message, as con-leche would print it: the payload is a
/// `Vec<u32>` of code points (`core_types`' stringless errors, §3.4).
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

/// `ConLeche.CheckError.exitCode` (`vendor/con-leche/Main.lean:48-51`):
/// `notImplemented` declines (2), `invalid` rejects (1), `internal` errors
/// (3).
fn exit_code(e: &CheckError) -> u8 {
    match e {
        CheckError::NotImplemented(_) => 2,
        CheckError::Invalid(_) => 1,
        CheckError::Internal(_) => 3,
    }
}

/// The verdict word `OVERVIEW.md` §0 tabulates against each code.
fn verdict_word(code: u8) -> &'static str {
    match code {
        1 => "rejected",
        2 => "declined",
        _ => "error",
    }
}

fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut path: Option<String> = None;
    let mut mode_verified = true;
    let mut pins: Option<String> = None;
    let mut taint_skipped: u64 = 0;
    let mut stats = false;
    let mut quiet = false;
    let mut i = 0usize;
    while i < argv.len() {
        let a = argv[i].as_str();
        match a {
            "--verified" => mode_verified = true,
            "--trusted" => mode_verified = false,
            "--stats" => stats = true,
            "--quiet" => quiet = true,
            "--pins" => {
                i += 1;
                if i >= argv.len() {
                    return Err("--pins needs a file".to_string());
                }
                pins = Some(argv[i].clone());
            }
            "--taint-skipped" => {
                i += 1;
                if i >= argv.len() {
                    return Err("--taint-skipped needs a number".to_string());
                }
                match argv[i].parse::<u64>() {
                    Ok(n) => taint_skipped = n,
                    Err(_) => return Err(format!("not a number: {}", argv[i])),
                }
            }
            _ => {
                if a.starts_with("--pins=") {
                    pins = Some(a["--pins=".len()..].to_string());
                } else if a.starts_with("--taint-skipped=") {
                    match a["--taint-skipped=".len()..].parse::<u64>() {
                        Ok(n) => taint_skipped = n,
                        Err(_) => return Err(format!("not a number: {}", a)),
                    }
                } else if a.starts_with('-') {
                    return Err(format!("unknown option: {}", a));
                } else if path.is_some() {
                    return Err("one dump at a time".to_string());
                } else {
                    path = Some(a.to_string());
                }
            }
        }
        i += 1;
    }
    match path {
        None => Err("no dump given".to_string()),
        Some(p) => Ok(Args {
            path: p,
            mode: if mode_verified {
                CheckMode::Verified
            } else {
                CheckMode::Trusted
            },
            mode_tag: if mode_verified {
                "--verified"
            } else {
                "--trusted"
            },
            pins,
            taint_skipped,
            stats,
            quiet,
        }),
    }
}

/// The `CState` field sizes after phase A, for `--stats`: the memo tables the
/// flush does not empty are the interesting ones (`ienv` and the three
/// level-operation memos, `state_c::flushed`).
fn stats_line(st: &CState) -> String {
    format!(
        "  cstate ienv={} constTyAt={} constValAt={} ruleRhsAt={} \
         whnfCore={} whnf={} infer={} inferIo={} defeq={} annot={} \
         lsimp={} lnz={} eqv={} inst={}",
        st.ienv.len(),
        st.const_ty_at.len(),
        st.const_val_at.len(),
        st.rule_rhs_at.len(),
        st.whnf_core_c.len(),
        st.whnf_c.len(),
        st.infer_c.len(),
        st.infer_io_c.len(),
        st.defeq_c.len(),
        st.annot_c.len(),
        st.lsimp_c.len(),
        st.lnz_c.len(),
        st.eqv_c.len(),
        st.inst_c.len(),
    )
}

/// `installed::check_decls`' body with the phase boundary visible, so
/// `--stats` can report the install phase's memo state: the fold, the sizes,
/// then the record walk.  The verdict is `check_decls`' — this *is* its body
/// (`ConLeche/Cached/Installed.lean:407-411`), which is why the flag changes
/// no outcome.
fn check_decls_with_stats(
    mode: &CheckMode,
    ds: &Vec<DeclC>,
) -> (Result<Env, (CheckError, u64)>, String) {
    let mut st: CState = state_c::cstate_new();
    match installed::annot_decl_fold_from(
        mode,
        &mut st,
        (0, fenv::mk_fenv(env::empty()), Vec::new()),
        ds,
        0,
    ) {
        Err(e) => (Err(e), stats_line(&st)),
        Ok(p) => {
            let line = format!("{} records={}", stats_line(&st), p.2.len());
            (installed::check_decls_phase_b(mode, p.1, p.2), line)
        }
    }
}

/// The whole run, on the big-stack thread: parse, fold, verdict.  Returns the
/// exit code.
fn run(args: &Args) -> u8 {
    let t0 = Instant::now();
    let text = match std::fs::read_to_string(&args.path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("con-ron: {}: {}", args.path, e);
            return 3;
        }
    };
    let ds: Vec<DeclC> = match parse_decls(&text) {
        Ok(ds) => ds,
        Err(e) => {
            eprintln!("con-ron: {}: {}", args.path, e);
            return 3;
        }
    };
    let t_parse = t0.elapsed();
    if let Some(p) = &args.pins {
        eprintln!(
            "con-ron: warning: --pins {} ignored — no pins-dump reader yet, and \
             check_decls' pin list is not threaded to the pin loop (DESIGN.md \
             §3.6, task #22); running with the empty pin list",
            p
        );
    }
    let pins: Vec<NatOpPinSet> = Vec::new();
    let t1 = Instant::now();
    let (r, stats) = if args.stats {
        let (r, s) = check_decls_with_stats(&args.mode, &ds);
        (r, Some(s))
    } else {
        (installed::check_decls(&args.mode, &pins, &ds), None)
    };
    let t_check = t1.elapsed();
    let code: u8 = match &r {
        Ok(_) => {
            // `Main.lean:749-753`: an accepting fold over a stream with
            // taint skips is a DECLINE, never an accept.
            if args.taint_skipped > 0 {
                eprintln!(
                    "con-ron: declined ({} declarations checked, {} skipped for \
                     tolerated axioms) ({})",
                    ds.len(),
                    args.taint_skipped,
                    args.mode_tag
                );
                2
            } else {
                println!(
                    "con-ron: accepted {} declarations ({})",
                    ds.len(),
                    args.mode_tag
                );
                0
            }
        }
        Err((e, pos)) => {
            let code = exit_code(e);
            eprintln!(
                "con-ron: {}: {} [at fold position {}] ({})",
                verdict_word(code),
                message(e),
                pos,
                args.mode_tag
            );
            code
        }
    };
    if !args.quiet {
        let consts: usize = match &r {
            Ok(env) => env.consts.len(),
            Err(_) => 0,
        };
        eprintln!(
            "  records {} constants {} parse {:.3}s check {:.3}s total {:.3}s",
            ds.len(),
            consts,
            t_parse.as_secs_f64(),
            t_check.as_secs_f64(),
            t0.elapsed().as_secs_f64()
        );
        if let Some(s) = stats {
            eprintln!("{}", s);
        }
    }
    code
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|a| a == "-h" || a == "--help") {
        println!("{}", USAGE);
        return ExitCode::SUCCESS;
    }
    let args = match parse_args(&argv) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            eprintln!("{}", USAGE);
            return ExitCode::from(3);
        }
    };
    let h = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(move || run(&args));
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
