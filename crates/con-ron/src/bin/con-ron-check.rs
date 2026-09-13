//! `con-ron-check` — the same driver as `con-ron`, over a `con-ron-decls/1`
//! dump instead of a raw stream.
//!
//! The driver half of DESIGN.md §3.6's differential seam (task #28).  The
//! dump is the *parsed* declaration list con-leche's own frontend produced
//! (`lake exe con-ron-dump`, task #10), so this tool is exactly con-leche's
//! `Main.lean` minus the frontend: read the records, run the fold, print the
//! verdict line, exit with con-leche's code.
//!
//! ```text
//! con-ron-check [--verified|--trusted] [--pins FILE] [--taint-skipped N]
//!               [--progress[=<stride>]] [--jobs=<n>] [--no-mark-persistent]
//!               [--stats] [--stats-every N] [--parse-only] [--quiet]
//!               FILE.decls
//! ```
//!
//! **Everything from the parsed list on is `con_ron::driver`** (task #40),
//! shared with the `con-ron` binary: the exit-code mapping, the declaration
//! label, the two phase loops, the `--progress` heartbeat, the taint-skip rule
//! and the verdict lines.  Before task #40 this file carried its own copy of
//! each; the taint-skip rule *decides an exit code*, so two copies of it was
//! one too many.  What is this binary's own is the dump reader, the memory
//! report and the `--stats` instrumentation.
//!
//! The verdict vocabulary and the exit codes are con-leche's
//! (`vendor/con-leche/OVERVIEW.md` §0, `Main.lean:48-51,744-788`): 0 accepted,
//! 1 rejected, 2 declined, 3 usage/malformed/internal, with `driver`'s module
//! note for the table and for the two conventions that are not exit codes (an
//! out-of-memory abort, and a panic).
//!
//! Three details this driver mirrors deliberately:
//!
//! * **The taint-skip decline** (`Main.lean:637-645,749-753`): a clean fold
//!   over a stream from which the frontend *skipped* declarations for
//!   tolerated axioms is still a decline — "uses of tolerated axioms are
//!   never accepted".  The skip count is frontend state and is **not** in the
//!   dump (task #10's surprise 9), so it is a parameter here,
//!   `--taint-skipped N`, and the rule itself is `driver::verdict_accept`,
//!   which the `con-ron` binary reaches with its own frontend's count.  The
//!   core (`check_decls`) must not know the rule.
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
//! `--progress`, `--jobs=<n>` and `--no-mark-persistent` mean here exactly
//! what they mean in the `con-ron` binary, because they are the same code:
//! the heartbeat's line shapes are `OVERVIEW.md` §0's, `--jobs=<n>` runs phase
//! B on `con_ron::pool` (task #48) with the verdict walked in record order at
//! every count, and the persistent mark has no Rust counterpart to switch off.
//! The retired con-leche spellings are hard errors here too.
//!
//! Two flags exist for the memory budget (DESIGN.md task #36).
//! `--parse-only` stops after the reader, which is how the parse half of the
//! budget is measured on its own; and every run reports the peak resident set
//! (`VmHWM`) **twice**, once at the end of the parse and once at the end of
//! the fold, so the two halves of the 3x rule are visible separately.  The
//! dump itself is never held: `parse_decls_file` streams it line by line, so
//! the 3 GB of Mathlib text is not part of either number.
//!
//! The fold runs on a thread with a **1 GiB stack** (`driver::STACK_BYTES`):
//! `check_decls`, like con-leche's, is deep recursion over the term DAG, and
//! con-leche reserves 1 GiB per worker for exactly this.

use std::process::ExitCode;
use std::time::Instant;

use con_ron_core::cached::installed;
use con_ron_core::cached::parsed_c::DeclC;
use con_ron_core::cached::parsed_c::PendingCheck;
use con_ron_core::cached::state_c::CState;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::nat_op_pins::NatOpPinSet;

use con_ron::driver;
use con_ron::driver::Heartbeat;
use con_ron::driver::PhaseObserver;
use con_ron::driver::STACK_BYTES;
use con_ron_dump::parse_decls_file;
use con_ron_dump::peak_rss_kb;

/// con-leche: Main.lean:800-1048 usage
/// The usage text.  §3.1: message strings need not match; this binary's
/// synopsis is `con-ron`'s minus the frontend's flags, plus the dump reader's
/// own (`--taint-skipped`, `--stats`, `--parse-only`).
const USAGE: &str = "\
usage: con-ron-check [--verified|--trusted] [--pins FILE|--no-pins]
                     [--taint-skipped N]
                     [--progress[=<stride>]] [--jobs=<n>]
                     [--no-mark-persistent] [--stats] [--stats-every N]
                     [--parse-only] [--quiet] FILE.decls

  the same driver as `con-ron`, reading a `con-ron-decls/1` dump instead of a
  raw lean4export stream.  --taint-skipped N supplies the frontend state the
  dump does not carry (a clean fold over a stream with skips is a DECLINE).
  --jobs=<n> is the check phase's worker count (task #48): <n> workers claim
  records off a shared counter and the results are walked in RECORD order, so
  the verdict is the same at every <n>; --jobs=1 is the plain loop.  Each
  worker reserves 1 GiB of address space, and the default is one per hardware
  thread capped at 16.  --no-mark-persistent is accepted and a no-op (the mark
  is a Lean-runtime reference-counting device).  Every retired con-leche
  spelling is a hard error naming its replacement.

exit codes: 0 accepted, 1 rejected, 2 declined, 3 usage/malformed/internal.";

/// con-leche: Main.lean:1050-1064 Args
/// What the command line asked for.
struct Args {
    path: String,
    mode: CheckMode,
    mode_tag: &'static str,
    pins: Option<String>,
    /// `--no-pins` (task #43): the empty pin list, i.e. the pin loop's `[]`
    /// arm.  A test override; the default is the core's embedded text.
    no_pins: bool,
    taint_skipped: u64,
    /// `--progress[=<stride>]`: the shared heartbeat's stride; 0 is no flag.
    progress: u64,
    /// `--jobs=<n>`: the check phase's worker count; `None` is the capped
    /// default (`driver::default_jobs`).
    jobs: Option<u64>,
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

/// con-leche: Main.lean:1066-1158 parseArgs
/// The argument parse.  The retired spellings go through
/// `driver::retired_flag`, so both binaries reject the same thirteen with the
/// same messages; `--progress`/`--jobs` go through the same validators.
fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut path: Option<String> = None;
    let mut mode_verified = true;
    let mut pins: Option<String> = None;
    let mut no_pins = false;
    let mut taint_skipped: u64 = 0;
    let mut progress: u64 = 0;
    let mut jobs: Option<u64> = None;
    let mut stats = false;
    let mut stats_every: u64 = 0;
    let mut parse_only = false;
    let mut quiet = false;
    let mut i = 0usize;
    while i < argv.len() {
        let a = argv[i].as_str();
        if let Some(m) = driver::retired_flag(a) {
            return Err(m);
        }
        match a {
            "--verified" => mode_verified = true,
            "--trusted" => mode_verified = false,
            "--stats" => stats = true,
            "--parse-only" => parse_only = true,
            "--progress" => progress = 1,
            // Accepted and a no-op, with `driver::mark_persistent_note`'s
            // reason; `main` prints it.
            "--no-mark-persistent" => {}
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
            "--no-pins" => no_pins = true,
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
            "--jobs" => {
                return Err("--jobs takes a worker count: --jobs=<n>".to_string());
            }
            _ => {
                if let Some(v) = a.strip_prefix("--progress=") {
                    progress = driver::progress_stride(v)?;
                } else if let Some(v) = a.strip_prefix("--jobs=") {
                    jobs = Some(driver::jobs_count(v)?);
                } else if let Some(v) = a.strip_prefix("--stats-every=") {
                    match v.parse::<u64>() {
                        Ok(n) => stats_every = n,
                        Err(_) => return Err(format!("not a number: {}", a)),
                    }
                } else if let Some(v) = a.strip_prefix("--pins=") {
                    pins = Some(v.to_string());
                } else if let Some(v) = a.strip_prefix("--taint-skipped=") {
                    match v.parse::<u64>() {
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
            no_pins,
            taint_skipped,
            progress,
            jobs,
            stats,
            stats_every,
            parse_only,
            quiet,
        }),
    }
}

/// con-leche: none — the `CState` field sizes after a phase, for `--stats`:
/// the memo tables the flush does not empty are the interesting ones (`ienv`
/// and the three level-operation memos, `state_c::flushed`).
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

/// con-leche: none — the process's current resident set, in KB, from
/// `/proc/self/statm` (page counts): the periodic report's memory column.
/// Zero where the file is not readable.  Deliberately *not* `peak_rss_kb`,
/// which is `VmHWM` and is what the two budget numbers report.
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

/// con-leche: none — the `FEnv` sizes beside the `CState` ones: the index, the
/// constant list and (phase A) the pending-check list.
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

/// con-leche: Main.lean:163-178 checkHeartbeat
/// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::Stats_refines, then delete this line
/// **`--stats`/`--stats-every` as a `PhaseObserver`**, beside the heartbeat it
/// wraps: the two flags print different lines at the same points of the same
/// loop (`driver::check_decls_driver`), so this observer forwards every event
/// to the `Heartbeat` and then prints its own.  `after_a` is the phase-A
/// summary line `--stats` reports at the end of the run, captured at the
/// boundary because the phase-A `CState` is gone by then.
struct Stats {
    hb: Heartbeat,
    every: u64,
    after_a: Option<String>,
}

/// con-leche: Main.lean:163-178 checkHeartbeat
/// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::impl PhaseObserver for Stats_refines, then delete this line
/// The forwarding observer.
impl PhaseObserver for Stats {
    /// con-leche: Main.lean:67-161 installLoop
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::install_before_refines, then delete this line
    /// The heartbeat's install line.
    fn install_before(&mut self, pos: u64, total: usize, d: &DeclC) {
        self.hb.install_before(pos, total, d);
    }

    /// con-leche: Main.lean:67-161 installLoop
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::install_after_refines, then delete this line
    /// `[A <i>/<N>]` with the memo state and the index, every `every`
    /// declarations.
    fn install_after(&mut self, done: usize, total: usize, st: &CState, fe: &FEnv, pend: usize) {
        self.hb.install_after(done, total, st, fe, pend);
        if self.every > 0 && (done as u64) % self.every == 0 {
            eprintln!(
                "  [A {}/{}]\n{}\n{}",
                done,
                total,
                stats_line(st),
                fenv_line(fe, pend)
            );
        }
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::install_failed_refines, then delete this line
    /// Phase A failed: the heartbeat's line, and the memo state it failed in
    /// (which is what `--stats` reports in place of the phase-A summary the
    /// boundary never reached).
    fn install_failed(&mut self, pos: u64, total: usize, st: &CState) {
        self.hb.install_failed(pos, total, st);
        self.after_a = Some(stats_line(st));
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::install_done_refines, then delete this line
    /// The boundary: the heartbeat's line, `[A done]`, and the phase-A
    /// summary `--stats` prints at the end.
    fn install_done(&mut self, total: usize, pend: usize, st: &CState, fe: &FEnv) {
        self.hb.install_done(total, pend, st, fe);
        self.after_a = Some(format!("{} records={}", stats_line(st), pend));
        if self.every > 0 {
            eprintln!("  [A done]\n{}\n{}", stats_line(st), fenv_line(fe, pend));
        }
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::phase_b_workers_refines, then delete this line
    /// The worker count, for the heartbeat's summary.
    fn phase_b_workers(&mut self, workers: usize) {
        self.hb.phase_b_workers(workers);
    }

    /// con-leche: Main.lean:260-280 checkOne
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::wants_check_lines_refines, then delete this line
    /// The cited `stride > 0`, plus `--stats-every`'s own per-check line: the
    /// pool's workers bump the completed-counter and call this observer when
    /// EITHER flag wants a line.
    fn wants_check_lines(&self) -> bool {
        self.hb.wants_check_lines() || self.every > 0
    }

    /// con-leche: Main.lean:163-178 checkHeartbeat
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::check_after_refines, then delete this line
    /// The heartbeat's check line, and `[B <done>/<M>]`.
    fn check_after(&mut self, done: usize, m: usize, pc: &PendingCheck, st: &CState, fe: &FEnv) {
        self.hb.check_after(done, m, pc, st, fe);
        if self.every > 0 && (done as u64) % self.every == 0 {
            eprintln!(
                "  [B {}/{}]\n{}\n{}",
                done,
                m,
                stats_line(st),
                fenv_line(fe, m - done)
            );
        }
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::check_failed_refines, then delete this line
    /// Phase B failed: the heartbeat's line, and the record's memo state.
    fn check_failed(&mut self, pos: u64, st: &CState) {
        self.hb.check_failed(pos, st);
        self.after_a = Some(stats_line(st));
    }

    /// con-leche: Main.lean:339-458 checkDeclsIO
    /// con-leche: CHANGED since 3e004805 — re-port, re-test, re-prove con-ron-check::check_done_refines, then delete this line
    /// Every check passed.
    fn check_done(&mut self, m: usize) {
        self.hb.check_done(m);
    }
}

/// con-leche: Main.lean:502-797 checkMain
/// The whole run, on the big-stack thread: parse, fold, verdict.  Returns the
/// exit code.
fn run(args: &Args) -> u8 {
    let t0 = Instant::now();
    // The dump is *streamed* (task #36): the reader takes it one line at a
    // time and never holds the text, so `Init`'s 165 MB and Mathlib's 3.06 GB
    // are not part of the run's peak at all.
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
        println!(
            "con-ron: parsed {} declarations ({})",
            ds.len(),
            args.mode_tag
        );
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
    // ONE driver: the heartbeat's `parse done` line prices this binary's own
    // parse (the dump reader) exactly as `con-ron`'s prices the stream's, and
    // the fold below is `check_decls`' body either way.  A run with no flag
    // calls `check_decls` itself and comes through no observer at all.  The
    // `0`s are the prelude counts: the dump has already absorbed the prelude,
    // so there is none to subtract (the module note's second bullet).
    let mut obs = Stats {
        hb: Heartbeat::new(args.progress, t0),
        every: args.stats_every,
        after_a: None,
    };
    obs.hb.parse_done(ds.len(), 0, 0);
    // The pin list.  The default is the core's own embedded text, decoded by
    // the core (task #43); `--pins FILE` and `--no-pins` are the test
    // overrides (`driver::pins_for_run`).
    let t_pins0 = Instant::now();
    let pins: Vec<NatOpPinSet> = match driver::pins_for_run(&args.pins, args.no_pins) {
        Ok(ps) => ps,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return 3;
        }
    };
    let t_pins = t_pins0.elapsed();
    let t1 = Instant::now();
    // The pool is the driver's, so `--jobs>1` goes through the driver whether
    // or not anything is observing it (task #48).
    let jobs: u64 = match args.jobs {
        Some(n) => n,
        None => driver::default_jobs(),
    };
    let observed = args.progress > 0 || args.stats || args.stats_every > 0;
    let r = if observed || jobs > 1 {
        driver::check_decls_driver(&args.mode, &pins, &ds, jobs, &mut obs)
    } else {
        installed::check_decls(&args.mode, &pins, &ds)
    };
    let t_check = t1.elapsed();
    let code: u8 = match &r {
        // `Main.lean:749-753` through `driver::verdict_accept`: an accepting
        // fold over a stream with taint skips is a DECLINE, never an accept.
        // The detail is the frontend's and the dump does not carry it, so
        // only the count is printed here.
        Ok(_) => driver::verdict_accept(
            ds.len() as u64,
            args.taint_skipped as usize,
            None,
            args.mode_tag,
        ),
        Err((e, pos)) => driver::verdict_failure(&ds, e, *pos, None, args.mode_tag, t0),
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
        if let Some(s) = &obs.after_a {
            eprintln!("{}", s);
        }
    }
    code
}

/// con-leche: Main.lean:1160-1192 main
/// The entry point: one big-stack thread, and a panic on it is exit 3.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.iter().any(|a| a == "-h" || a == "--help") {
        println!("{}", USAGE);
        return ExitCode::SUCCESS;
    }
    if argv.iter().any(|a| a == "--no-mark-persistent") {
        eprintln!("con-ron: {}", driver::mark_persistent_note());
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
