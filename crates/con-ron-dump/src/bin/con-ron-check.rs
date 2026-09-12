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
//!               [--stats] [--stats-every N] [--parse-only] [--quiet] FILE.decls
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
//! `--pins FILE` is the §3.6 pin-list parameter, live since task #31: the
//! file is a `con-ron-pins/1` dump of con-leche's own `natOpPinSets`
//! (`lake exe con-ron-dump-pins`, `proof/ConRon/Dump/FORMAT.md` §7), read by
//! `con_ron_dump::parse_pins` and handed to `check_decls(mode, pins, ds)`,
//! which threads it to `checker::check_div_mod_pin_loop`.  Without the flag
//! the pin list is **empty**, which is the `[]` arm of the loop: a
//! `Nat.div`/`Nat.mod` stream then declines with "unsupported Nat.div/mod
//! spelling", exactly as con-leche does for a stream matching no variant —
//! sound for the accept direction (§1), and 17 of the corpus's fixtures turn
//! on it.
//!
//! Two flags exist for the memory budget (DESIGN.md task #36).
//! `--parse-only` stops after the reader, which is how the parse half of the
//! budget is measured on its own; and every run reports the peak resident set
//! (`VmHWM`) **twice**, once at the end of the parse and once at the end of
//! the fold, so the two halves of the 3x rule are visible separately.  The
//! dump itself is never held: `parse_decls_file` streams it line by line, so
//! the 3 GB of Mathlib text is not part of either number.
//!
//! The fold runs on a thread with a **1 GiB stack**: `check_decls`, like
//! con-leche's, is deep recursion over the term DAG, and con-leche reserves
//! 1 GiB per worker for exactly this.

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
use con_ron_dump::parse_decls_file;
use con_ron_dump::parse_pins;
use con_ron_dump::peak_rss_kb;

const USAGE: &str = "usage: con-ron-check [--verified|--trusted] [--pins FILE] \
                     [--taint-skipped N] [--stats] [--stats-every N] \
                     [--parse-only] [--quiet] FILE.decls";

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
    /// `--stats-every N`: report the map sizes every `N` declarations in each
    /// phase (0 = only at the phase boundary).
    stats_every: u64,
    /// `--parse-only` (task #36): read the dump and stop, so that the parse
    /// half of the memory budget can be measured without the fold.  The
    /// verdict is then "parsed N declarations" and the exit code 0.
    parse_only: bool,
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
    let mut stats_every: u64 = 0;
    let mut parse_only = false;
    let mut quiet = false;
    let mut i = 0usize;
    while i < argv.len() {
        let a = argv[i].as_str();
        match a {
            "--verified" => mode_verified = true,
            "--trusted" => mode_verified = false,
            "--stats" => stats = true,
            "--parse-only" => parse_only = true,
            "--stats-every" => {
                i += 1;
                if i >= argv.len() {
                    return Err("--stats-every needs a number".to_string());
                }
                match argv[i].parse::<u64>() {
                    Ok(n) => stats_every = n,
                    Err(_) => return Err(format!("not a number: {}", argv[i])),
                }
            }
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
                if a.starts_with("--stats-every=") {
                    match a["--stats-every=".len()..].parse::<u64>() {
                        Ok(n) => stats_every = n,
                        Err(_) => return Err(format!("not a number: {}", a)),
                    }
                } else if a.starts_with("--pins=") {
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
            stats_every,
            parse_only,
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

/// The process's current resident set, in KB, from `/proc/self/statm` (page
/// counts) — the periodic report's memory column.  Zero where the file is not
/// readable.
fn rss_kb() -> u64 {
    match std::fs::read_to_string("/proc/self/statm") {
        Err(_) => 0,
        Ok(t) => {
            let mut it = t.split_whitespace();
            let _total = it.next();
            match it.next() {
                None => 0,
                Some(pages) => pages.parse::<u64>().unwrap_or(0) * 4,
            }
        }
    }
}

/// The `FEnv` sizes beside the `CState` ones: the index, the constant list
/// and (phase A) the pending-check list.
fn fenv_line(fe: &FEnv, pend: usize) -> String {
    format!(
        "  fenv idx={} consts={} visible_below={} pending={} rss={}KB",
        fe.idx.len(),
        fe.env.consts.len(),
        fe.visible_below,
        pend,
        rss_kb()
    )
}

/// `installed::check_decls`' body with the phase boundary visible, so
/// `--stats` can report the install phase's memo state, and with the two
/// folds spelled out here so `--stats-every N` can report every `N`
/// declarations.  The verdict is `check_decls`' — this *is* its body
/// (`ConLeche/Cached/Installed.lean:407-411`), step for step
/// (`annot_decl_step` per record in phase A, `check_pending` from a fresh
/// `CState` per record in phase B), which is why the flags change no
/// outcome.
fn check_decls_with_stats(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    ds: &Vec<DeclC>,
    every: u64,
) -> (Result<Env, (CheckError, u64)>, String) {
    let mut st: CState = state_c::cstate_new();
    let mut p: (u64, FEnv, Vec<PendingCheck>) = (0, fenv::mk_fenv(env::empty()), Vec::new());
    let mut i: usize = 0;
    while i < ds.len() {
        match installed::annot_decl_step(mode, pins, &mut st, p, &ds[i]) {
            Err(e) => return (Err(e), stats_line(&st)),
            Ok(q) => p = q,
        }
        i += 1;
        if every > 0 && (i as u64) % every == 0 {
            eprintln!(
                "  [A {}/{}]\n{}\n{}",
                i,
                ds.len(),
                stats_line(&st),
                fenv_line(&p.1, p.2.len())
            );
        }
    }
    let line = format!("{} records={}", stats_line(&st), p.2.len());
    if every > 0 {
        eprintln!(
            "  [A done]\n{}\n{}",
            stats_line(&st),
            fenv_line(&p.1, p.2.len())
        );
    }
    // Phase B, `installed::check_pending_list`'s walk: a fresh `CState` per
    // record, the index threaded through.
    let pend: Vec<PendingCheck> = p.2;
    let mut fe: FEnv = p.1;
    let mut j: usize = 0;
    while j < pend.len() {
        let mut stb: CState = state_c::cstate_new();
        match installed::check_pending(mode, &mut stb, fe, &pend[j]) {
            Err(e) => return (Err((e, pend[j].pos)), stats_line(&stb)),
            Ok(fe2) => fe = fe2,
        }
        j += 1;
        if every > 0 && (j as u64) % every == 0 {
            eprintln!(
                "  [B {}/{}]\n{}\n{}",
                j,
                pend.len(),
                stats_line(&stb),
                fenv_line(&fe, pend.len() - j)
            );
        }
    }
    (Ok(fe.env), line)
}

/// The whole run, on the big-stack thread: parse, fold, verdict.  Returns the
/// exit code.
fn run(args: &Args) -> u8 {
    let t0 = Instant::now();
    // The dump is *streamed* (task #36): the reader takes it one line at a
    // time and never holds the text, so `Init`'s 165 MB and Mathlib's 3.06 GB
    // are not part of the run's peak at all.  Task #32 had already dropped
    // the text before the fold; the file is now never a `String` to begin
    // with, which also removes the `Vec<&str>` line index that used to be
    // 1.7 GB of Mathlib's parse.
    let ds: Vec<DeclC> = match parse_decls_file(&args.path) {
        Ok((ds, _)) => ds,
        Err(e) => {
            eprintln!("con-ron: {}: {}", args.path, e);
            return 3;
        }
    };
    let t_parse = t0.elapsed();
    let rss_parse = peak_rss_kb();
    if args.parse_only {
        println!("con-ron: parsed {} declarations ({})", ds.len(), args.mode_tag);
        if !args.quiet {
            eprintln!(
                "  records {} parse {:.3}s peak RSS after parse {} MB",
                ds.len(),
                t_parse.as_secs_f64(),
                rss_parse / 1024
            );
        }
        return 0;
    }
    // The pin list (§3.6's parameter).  No `--pins` is the empty list, i.e.
    // the pin loop's `[]` arm; a `Nat.div`/`Nat.mod` stream then declines.
    let t_pins0 = Instant::now();
    let pins: Vec<NatOpPinSet> = match &args.pins {
        None => Vec::new(),
        Some(p) => match std::fs::read_to_string(p) {
            Err(e) => {
                eprintln!("con-ron: {}: {}", p, e);
                return 3;
            }
            Ok(text) => match parse_pins(&text) {
                Err(e) => {
                    eprintln!("con-ron: {}: {}", p, e);
                    return 3;
                }
                Ok(ps) => ps,
            },
        },
    };
    let t_pins = t_pins0.elapsed();
    let t1 = Instant::now();
    let (r, stats) = if args.stats || args.stats_every > 0 {
        let (r, s) = check_decls_with_stats(&args.mode, &pins, &ds, args.stats_every);
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
            "  records {} constants {} pin sets {} parse {:.3}s pins {:.3}s \
             check {:.3}s total {:.3}s",
            ds.len(),
            consts,
            pins.len(),
            t_parse.as_secs_f64(),
            t_pins.as_secs_f64(),
            t_check.as_secs_f64(),
            t0.elapsed().as_secs_f64()
        );
        // The two halves of DESIGN.md's 3x memory rule, separately (task
        // #36): `VmHWM` is a high-water mark, so the first number is the
        // reader's own peak and the second is the whole run's.
        eprintln!(
            "  peak RSS after parse {} MB, after check {} MB  (VmHWM)",
            rss_parse / 1024,
            peak_rss_kb() / 1024
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
