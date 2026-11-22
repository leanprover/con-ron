//! `con-ron` — con-leche's `Driver/Cli.lean` and `Main.lean` over the ARENA (DESIGN.md §8.6,
//! task #97 P4f), on a **raw** lean4export stream.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>]
//!         [--progress[=N|P%|Ss]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron [flags] --olean --search-path=DIR[:DIR...] [--constant=NAME]... [--] MODULE...
//! con-ron [flags] --compare [--] CHALLENGE.ndjson SOLUTION.ndjson
//! con-ron [flags] --olean --compare [--trusted-search-path=DIRS] --search-path=DIRS
//!         [--constant=NAME]... [--] CHALLENGE SOLUTION
//! con-ron --help
//! ```
//!
//! **The same program as `con-ron`, over handles.**  The steps are con-leche's
//! four and they are the Lean twin's `runPipeline` (`Arena/Main.lean`):
//!
//! ```text
//! intern_reserved_pins  →  builtin_prelude_e  →  parse (chunk_step/
//! chunk_finish)  →  prepare_d  →  intern_all_pins  →  check_decls_driver
//! ```
//!
//! — the checker's own reserved constants are interned once into the
//! persistent tier of one `EStore` (`con_ron_core::arena::pins`, task
//! #97-P6-4a; every later `pin_*` is a field read, and a read before this has
//! run is an `Internal` stop), the built-in prelude parses into that tier
//! (`con_ron_core::frontend::prelude`), the stream is read 4 MiB at a time and
//! decoded into the same tier (`con_ron_core::frontend::export_c`; every
//! inductive block — mutual and nested included — installs through the
//! kernel's uniform installer now, no model ever read from the input, task
//! #105), `con_ron_core::frontend::prepare` puts the prelude's
//! declarations in front and hoists a pinned `Nat` operation's ground, the pin
//! list is interned ONCE while the scratch tier is still off
//! (`checker::intern_all_pins`), and the resulting `Vec<IDeclaration>` goes to
//! `con_ron::driver::check_decls_driver` — the stream's index
//! (`stream_index::build_index`), the frozen tier, and the worker pool over
//! `checker::run_job`, every record's check a job.
//!
//! Exit codes are con-leche's (`Driver/CheckMain.lean`'s `exitCode`): 0 accepted, 1 rejected, 2
//! declined, 3 usage/malformed/internal — `con_ron::driver::exit_code`, the
//! same mapping the other binary uses, so `scripts/diff-e2e.sh` reads the same
//! numbers off both.  Out of memory is neither (a Rust allocation failure
//! aborts, which a shell reports as 134) and a panic is 3.
//!
//! **NO TEMPORARY FILES** (con-leche task #180).  The checker writes nothing
//! outside its own stdout/stderr and reads its input strictly forward, 4 MiB
//! at a time.
//!
//! **`--jobs=<n>` is real** since task #97-P6-6b: the check phase runs on `n`
//! worker threads sharing the frozen persistent tier and the stream's index by
//! reference (`con_ron::pool`), and the default is one per hardware
//! thread capped at sixteen — `con_ron::driver::default_jobs`, the same
//! function `con-ron` uses.  `--pins FILE` and
//! `--no-pins` are con-ron's own and mean exactly what they mean there.

use std::io::Write;
use std::time::Instant;

use con_ron_core::arena::checker;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::pins::max_nat_size_default;
use con_ron_core::ron::nat::Nat;
use con_ron_core::frontend::export_c;
use con_ron_core::frontend::export_c::ParseResultD;
use con_ron_core::frontend::prelude;
use con_ron_core::frontend::prepare;

use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;

use con_ron::driver;
use con_ron::driver::Heartbeat;
use con_ron_core::frontend::pace::Pace;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
use con_ron_core::frontend::olean::records::{value_cache_empty, ModRef, OleanRead, ValueCache};
use con_ron_core::frontend::olean::spec::OleanPins;
use con_ron_core::arena::store::PersTier;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for the `con-ron-pins/2` reader of `--pins`.  So this
// crate declares none but *chooses*: `crates/con-ron/Cargo.toml` takes
// that crate with `default-features = false` and forwards `mimalloc` (the
// default) and `jemalloc`, exactly as `crates/con-ron` does, so the two
// binaries are measured on the same allocator unless a build says otherwise.
// `--help` prints `con_ron_dump::ALLOCATOR` so a measurement can be
// reproduced.

/// con-leche: ConLeche/Driver/Cli.lean:116-132 synopsis
/// The invocation forms, printed on their own when there are no arguments.
/// `--pins`/`--no-pins` are the port's own testing flags (`driver::pins_for_run`)
/// and are not in con-leche's synopsis; they are in the help text's options.
const SYNOPSIS: &str = "\
Usage:
  con-ron [OPTIONS] [--] FILE.ndjson
  con-ron [OPTIONS] --compare [--] CHALLENGE.ndjson SOLUTION.ndjson
  con-ron [OPTIONS] --olean --search-path=DIRS [--] MODULE...
  con-ron [OPTIONS] --check-graph --search-path=DIRS [--] MODULE...
  con-ron [OPTIONS] --olean --module --search-path=DIRS [--] MODULE
  con-ron [OPTIONS] --olean --modular --search-path=DIRS [--] MODULE
  con-ron [OPTIONS] --olean --schedule[-OPT=V] --search-path=DIRS [--] MODULE
  con-ron [OPTIONS] --olean --compare [--trusted-search-path=DIRS]
          --search-path=DIRS [--] CHALLENGE SOLUTION
  con-ron [OPTIONS] --check-graph --compare [--trusted-search-path=DIRS]
          --search-path=DIRS [--] CHALLENGE SOLUTION
  con-ron [OPTIONS] --olean --module|--modular|--schedule[-OPT=V]
          --compare [--trusted-search-path=DIRS] --search-path=DIRS
          [--] CHALLENGE SOLUTION";

/// con-leche: ConLeche/Driver/Cli.lean:134-135 tryHelp
/// The line after a usage error.
const TRY_HELP: &str = "Try 'con-ron --help' for more information.";

/// con-leche: ConLeche/Driver/Cli.lean:137-260 helpText
/// The `--help` text: con-leche's, with this binary's name, the port's two
/// testing flags, and con-ron's documentation.  DESIGN.md §3.1: message
/// strings need not match.
const HELP_HEAD: &str = "\
Check Lean declarations from a lean4export file or from .olean modules.
";

/// con-leche: ConLeche/Driver/Cli.lean:137-260 helpText
/// The rest of the `--help` text, after the synopsis.  The scheduler is the
/// simple one (`con_ron::schedule`): its settings con-ron does not run are
/// listed by name, as usage errors, in place of their descriptions.
const HELP_TAIL: &str = "\
Options:
  --verified          Check in the mode the soundness theorem covers (default)
  --trusted           Skip the checks only the proof needs; outside the theorem
  --jobs=N            Worker threads (default: one per hardware thread, at most 16)
  --max-nat-size=N    Largest Nat numeral in bytes the checker takes in or
                      computes; a larger one is rejected (default 134217728)
  --progress[=PACE]   Report progress on stderr: PACE is N declarations
                      (default 1), P% of each phase, or Ss seconds
  --pins FILE         Testing only: check with this Nat pin list instead of
                      the embedded one (outside the theorems)
  --no-pins           Testing only: check with no Nat pin list
  --help              Print this help and exit
  --                  End of options

lean4export input:
  --compare           CHALLENGE.ndjson SOLUTION.ndjson: check SOLUTION, then
                      check CHALLENGE, its axioms justified by SOLUTION: each
                      axiom of CHALLENGE (but the standard ones) and each
                      declaration whose value uses sorry is accepted as an
                      axiom of its statement when SOLUTION holds a constant
                      of that name and type, up to the names of level
                      parameters, and everything that type reads is the same
                      in both, record by record. Prints the justified axioms

.olean input:
  --olean             Read modules and their import closure from .olean files
  --search-path=DIRS  Colon-separated .olean directories; repeatable
  --constant=NAME     Check only NAME and what it mentions; repeatable
                      (outside the theorems)
  --compare           CHALLENGE SOLUTION: check the closure of the module
                      SOLUTION, then the closure of CHALLENGE, its axioms
                      justified by SOLUTION's as for lean4export input.
                      Prints the justified axioms. With --constant=NAME
                      (declarations of CHALLENGE itself), only NAME and
                      what it reads. With --check-graph, --module,
                      --modular or --schedule: CHALLENGE as one more module
                      of a modular run over the closures of both, with
                      `import all SOLUTION` added to its header: a
                      declaration of CHALLENGE that a loaded module holds
                      must be that constant (a hole, theorem or opaque
                      constant by its type, a definition with its value, up
                      to the names of level parameters; an inductive type
                      as it is), every other one is checked (its --module
                      run is the compare worker; the guarantee needs every
                      command to exit 0)
  --trusted-search-path=DIRS
                      With --compare: CHALLENGE and all it imports must be
                      in DIRS, and are read from there only; SOLUTION's
                      modules from DIRS first, then --search-path (the
                      modular modes read every module so). With --module
                      alone: MODULE's closure read from DIRS first, then
                      --search-path.
                      Colon-separated; repeatable
  --check-graph       Check only that the modules' import graph is acyclic
                      and that every import is on the search path
  --module            Check MODULE's own declarations alone, against what
                      they read of the modules it loads
  --modular           Check every module of MODULE's closure as --module
                      does, in this one process
  --schedule          Check every module of MODULE's closure by a --module
                      process each (--jobs=1 each), at most --jobs=N at a
                      time; a line per finished module on stdout, then each
                      failing module's verdict and last stderr line, and the
                      run's verdict: the first failing module in the graph's
                      order, its code (timeout, stack, a signal: 3); with
  --schedule-timeout=S     a time limit per worker
  --worker-stack-size=SIZE the workers' thread stacks (with a unit: 8G), set
                           as their LEAN_STACK_SIZE_KB (without the flag they
                           inherit the environment; con-ron's default is 1G)
  --schedule-order=ORDER   shuffled (default; by a hash of the names) or graph:
                           the order in which the modules start
  --schedule-commands      start nothing; print on stdout, one per line and
                           shell-quoted, the commands that check the closure:
                           the --check-graph run, then one --module run per
                           module in the start order (--jobs=N only if given);
                           the modular guarantee needs every one to exit 0 on
                           one unchanged snapshot of the files (with
                           --worker-stack-size, each worker's line starts
                           with LEAN_STACK_SIZE_KB=K); -memory, -log and
                           -timeout are ignored

con-leche's scheduler settings con-ron does not run (a usage error, exit 3):
  --schedule-log=FILE, --schedule-memory=SIZE (con-ron's --schedule keeps no
  log and no memory budget)

Exit status:
  0  accepted
  1  rejected: a declaration is invalid
  2  declined: an unsupported feature
  3  error: bad usage, malformed input or an internal failure

Documentation:
  README.md and OVERVIEW.md of the con-ron repository";

/// con-leche: none — a usage error's two lines (con-leche writes them out at
/// each site of `runArgs`): the message, then the pointer to `--help`.
fn usage_error(msg: &str) -> u8 {
    eprintln!("con-ron: {}", msg);
    eprintln!("{}", TRY_HELP);
    3
}

/// con-leche: ConLeche/Driver/Cli.lean:262-303 Args
/// What the command line asked for — `con-ron`'s `Args`, field for field, so
/// that a script written against one binary reads against the other.
struct Args {
    files: Vec<String>,
    verified: bool,
    progress: Pace,
    jobs: Option<u64>,
    /// The maximum `Nat` size in bytes (`--max-nat-size=<n>`).
    max_nat_size: Nat,
    pins: Option<String>,
    no_pins: bool,
    /// `--olean`: the positional arguments are root module names.
    olean: bool,
    /// `--search-path=DIR:DIR...`: where `--olean` looks for the files.
    search_path: Vec<String>,
    /// `--constant=NAME`: with `--olean`, the constants to start from.
    constants: Vec<String>,
    /// `--check-graph` (a mode con-ron does not run: `unsupported`).
    check_graph: bool,
    /// `--module` (not run by con-ron).
    module: bool,
    /// `--modular` (not run by con-ron).
    modular: bool,
    /// the values after `--schedule` of every `--schedule[-OPT=VALUE]` flag, `""`
    /// for the bare flag (`modular::opts_parse`)
    schedule: Vec<String>,
    /// some `--schedule` flag was given
    scheduled: bool,
    /// `--compare`: the two arguments are a challenge and its solution.
    compare: bool,
    /// `--trusted-search-path=DIR:DIR...`: with `--compare`, where the
    /// challenge is read, and where the solution is read first.
    trusted_path: Vec<String>,
    /// `--worker-stack-size=SIZE` was given, with a valid size
    worker_stack: bool,
    /// its value in KiB (`modular::parse_size`), which `--schedule-commands`
    /// prints as each worker's `LEAN_STACK_SIZE_KB`
    worker_stack_kb: Option<u64>,
    /// the `--max-nat-size` value as a decimal, for the printed workers
    max_nat_text: String,
    bad: Option<String>,
}

/// con-leche: ConLeche/Driver/Cli.lean:319-324 Args.closed
/// The arguments once all are read: `--worker-stack-size` without
/// `--schedule` is a usage error (no other run starts a worker).
fn closed(mut a: Args) -> Args {
    if a.worker_stack && !a.scheduled && a.bad.is_none() {
        a.bad = Some("--worker-stack-size takes --schedule".to_string());
    }
    a
}

/// con-leche: ConLeche/Driver/Cli.lean:326-377 parseArgs
/// The argument parse, clause for clause as `con-ron`'s: the mode flags in
/// either order with the heartbeat, `=`-carrying spellings after the bare
/// ones, an unknown `-`-leading word a usage error, everything else a file.
/// The two flag VALUES are `crate::driver`'s own functions (task #97-SWAP
/// folded that module back into this crate, and con-leche's command line is
/// still what they parse).
fn parse_args(argv: &[String]) -> Args {
    let mut a = Args {
        files: Vec::new(),
        verified: true,
        progress: Pace::Off,
        jobs: None,
        max_nat_size: max_nat_size_default(),
        pins: None,
        no_pins: false,
        olean: false,
        search_path: Vec::new(),
        constants: Vec::new(),
        check_graph: false,
        module: false,
        modular: false,
        schedule: Vec::new(),
        scheduled: false,
        compare: false,
        trusted_path: Vec::new(),
        worker_stack: false,
        worker_stack_kb: None,
        max_nat_text: match con_ron_core::ron::nat::to_u64(&max_nat_size_default()) {
            Some(k) => k.to_string(),
            None => String::new(),
        },
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
            // The end of the options: every argument after it is a file.
            "--" => {
                a.files.extend(argv[i + 1..].iter().cloned());
                return closed(a);
            }
            "--verified" => a.verified = true,
            "--trusted" => a.verified = false,
            "--progress" => a.progress = Pace::Every(1),
            "--no-pins" => a.no_pins = true,
            "--olean" => a.olean = true,
            "--check-graph" => a.check_graph = true,
            "--module" => a.module = true,
            "--modular" => a.modular = true,
            "--compare" => a.compare = true,
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
                    match con_ron::driver::progress_pace(v) {
                        Ok(n) => a.progress = n,
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--jobs=") {
                    match con_ron::driver::jobs_count(v) {
                        Ok(n) => a.jobs = Some(n),
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--max-nat-size=") {
                    match con_ron::driver::max_nat_size_arg(v) {
                        Ok(n) => {
                            a.max_nat_text = match con_ron_core::ron::nat::to_u64(&n) {
                                Some(k) => k.to_string(),
                                None => v.chars().filter(|c| *c != '_').collect(),
                            };
                            a.max_nat_size = n
                        }
                        Err(m) => bad(m, &mut a),
                    }
                } else if let Some(v) = s.strip_prefix("--pins=") {
                    a.pins = Some(v.to_string());
                } else if let Some(v) = s.strip_prefix("--constant=") {
                    a.constants.push(v.to_string());
                } else if let Some(v) = s.strip_prefix("--search-path=") {
                    a.search_path
                        .extend(v.split(':').filter(|d| !d.is_empty()).map(|d| d.to_string()));
                } else if let Some(v) = s.strip_prefix("--trusted-search-path=") {
                    a.trusted_path
                        .extend(v.split(':').filter(|d| !d.is_empty()).map(|d| d.to_string()));
                } else if let Some(v) = s.strip_prefix("--schedule") {
                    a.schedule.push(v.to_string());
                    a.scheduled = true;
                } else if let Some(v) = s.strip_prefix("--worker-stack-size=") {
                    if con_ron::driver::size_positive(v) {
                        a.worker_stack = true;
                        a.worker_stack_kb = con_ron::modular::parse_size(v);
                    } else {
                        bad(
                            format!(
                                "--worker-stack-size takes a size with a unit, K, M, G or T \
                                 (e.g. 8G), got {}",
                                con_ron::render::display_str(v)
                            ),
                            &mut a,
                        );
                    }
                } else if s.starts_with('-') {
                    bad(
                        format!("unknown option {}", con_ron::render::display_str(s)),
                        &mut a,
                    );
                } else {
                    a.files.push(s.to_string());
                }
            }
        }
        i += 1;
    }
    closed(a)
}

/// con-leche: none — `c == s` over the parsed module names (`Name`'s `BEq`)
/// Two module names of the command line, the same module: compared as
/// parsed, so `«A»` and `A` are one module.
fn same_module(a: &con_ron_core::kernel::name::Name, b: &con_ron_core::kernel::name::Name) -> bool {
    con_ron::render::name_str(a) == con_ron::render::name_str(b)
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
/// `--check-graph`'s usage checks, con-leche's in its order, then the graph
/// check (`modular::check_graph`, `modular::check_graph_cmp`).
fn check_graph_usage(a: &Args) -> u8 {
    if a.olean || a.module || !a.constants.is_empty() || (!a.trusted_path.is_empty() && !a.compare) {
        return usage_error(
            "--check-graph takes none of --olean, --module and --constant, and \
             --trusted-search-path only with --compare",
        );
    }
    if a.files.is_empty() || (a.search_path.is_empty() && a.trusted_path.is_empty()) {
        return usage_error("--check-graph takes one or more module names and a --search-path=DIRS");
    }
    let mut roots = Vec::new();
    for f in &a.files {
        match con_ron_core::frontend::olean::files::parse_mod_name(&con_ron::render::cps(f)) {
            Some(n) => roots.push(n),
            None => {
                return usage_error(&format!("not a module name: {}", con_ron::render::display_str(f)))
            }
        }
    }
    if a.compare {
        if roots.len() != 2 {
            return usage_error(
                "--check-graph --compare takes two module names, a challenge and its solution",
            );
        }
        if same_module(&roots[0], &roots[1]) {
            return usage_error("--compare takes two different modules, a challenge and its solution");
        }
        let dirs = |v: &Vec<String>| -> Vec<Vec<u32>> { v.iter().map(|d| con_ron::render::cps(d)).collect() };
        let s = roots.pop();
        let c = roots.pop();
        return match (c, s) {
            (Some(c), Some(s)) => con_ron::modular::check_graph_cmp(&con_ron::compare::CmpRequest {
                challenge: c,
                solution: s,
                trusted: dirs(&a.trusted_path),
                path: dirs(&a.search_path),
                constants: Vec::new(),
            }),
            _ => 3,
        };
    }
    let sp = con_ron_core::frontend::olean::files::roots_of_path(
        a.search_path.iter().map(|d| con_ron::render::cps(d)).collect(),
    );
    con_ron::modular::check_graph(&sp, &roots)
}

/// con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
/// A worker's request off the command line: the module (a compared run's
/// challenge), its solution (none: the module itself), the trusted path and the
/// search path (`--module`'s lookup is the solution's: the trusted path, then the
/// search path).
fn cmp_request(a: &Args, c: con_ron_core::kernel::name::Name, s: Option<con_ron_core::kernel::name::Name>) -> con_ron::compare::CmpRequest {
    let dirs = |v: &Vec<String>| -> Vec<Vec<u32>> { v.iter().map(|d| con_ron::render::cps(d)).collect() };
    let s = match s {
        Some(s) => s,
        None => con_ron_core::kernel::name::dup(&c),
    };
    con_ron::compare::CmpRequest {
        challenge: c,
        solution: s,
        trusted: dirs(&a.trusted_path),
        path: dirs(&a.search_path),
        constants: Vec::new(),
    }
}

/// con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
/// A `--schedule` request off the command line (`modular::schedule`).
fn schedule_req<'a>(a: &'a Args, root: con_ron_core::kernel::name::Name, cmp: Option<con_ron_core::kernel::name::Name>) -> con_ron::modular::ScheduleReq<'a> {
    con_ron::modular::ScheduleReq {
        trusted: &a.trusted_path,
        path: &a.search_path,
        root,
        cmp,
        opts: &a.schedule,
        mode_tag: if a.verified { "--verified" } else { "--trusted" },
        max_nat_size: a.max_nat_text.clone(),
        pace: &a.progress,
        jobs: a.jobs,
        stack_kb: a.worker_stack_kb,
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:305-308 helpWanted
/// `--help` before any `--`: after a `--` every argument is a file, whatever it
/// is called.
fn help_wanted(argv: &[String]) -> bool {
    argv.iter().take_while(|s| s.as_str() != "--").any(|s| s == "--help")
}

/// con-leche: none — the three verdict classes of a `CheckError` as the
/// frontend's callers report them (`con_ron`'s own `FrontendClass`).  The
/// port's fourth constructor (`CheckError::Native`, the arena's handle-index
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
            eprintln!("con-ron: declined: {} ({})", what, mode_tag);
            2
        }
        FrontendClass::Invalid(what) => {
            eprintln!("con-ron: invalid: {} ({})", what, mode_tag);
            1
        }
        FrontendClass::Internal(msg) => {
            eprintln!("con-ron: {} ({})", msg, mode_tag);
            3
        }
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:55-62 Input
/// **What a run reads**: a lean4export stream, or the import closure of root
/// modules read from their `.olean` files along a search path.
enum Input {
    Ndjson(String),
    Oleans(con_ron::olean_fs::OleanRequest),
}

/// con-leche: ConLeche/Driver/Dispatch.lean:26-62 Req
/// **What a run is**: a check of one input (`check_main`), or a compared run of
/// two lean4export files or two modules (`con_ron::compare`).
enum Run {
    Check(Input),
    CompareJson(String, String),
    CompareOleans(con_ron::compare::CmpRequest),
    /// `--olean --module [--compare]`: the challenge's worker (with `true`, the
    /// compare worker), every module read through the solution's lookup
    Module(con_ron::compare::CmpRequest, bool),
    /// `--olean --modular [--compare]`: every module of the closure, its worker each
    Modular(con_ron::compare::CmpRequest, bool),
}

/// con-leche: ConLeche/Driver/CheckMain.lean:233-385 checkMainG
/// con-leche: ConLeche/Driver/CheckMain.lean:87-98 readInputG
/// The driver's front matter: the prelude, the streaming parse, the
/// preparation, the pin walk, the receipts, then the index, the check phase
/// and the verdict.
/// It is the Lean twin's `runPipelineIO` with the heartbeat and the receipts
/// around it (`Arena/Main.lean`), and `con-ron`'s `check_main` with the
/// handles in place of the trees.
fn check_main(a: &Args, input: &Input) -> u8 {
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
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // THE PERSISTENT TIER a worker reads (DESIGN.md §8.3, task #97-P6-6b).
    // The parse, the pin walk and the index build own their own — the store is
    // owned (not frozen) — so what they are handed here is the EMPTY tier; the
    // check phase freezes the store's tier, the index with it, into a
    // `PersTier` and hands `&` it to every worker (`check_decls_driver`).
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    // THE RESERVED-NAME PINS, interned once into that persistent tier before
    // anything else touches it (task #97-P6-4a, `arena::pins`): the scratch
    // tier is closed here, so every pinned handle is persistent and survives
    // every job's bracket.  Until this has run, every `pin_*`
    // read raises `Internal` rather than answering — which is what makes the
    // initialisation-order hazard task #97c named impossible rather than
    // unlikely.
    // ConRon.Capstone: h1
    match con_ron_core::arena::pins::intern_reserved_pins(pers, &mut st) {
        Ok(()) => (),
        Err(e) => {
            eprintln!(
                "con-ron: the reserved-name pins do not intern ({}) ({})",
                con_ron::driver::message(&e),
                mode_tag
            );
            return 3;
        }
    }
    // The heartbeat (`--progress`), and its first line: what the run reads.
    let mut hb = Heartbeat::new(con_ron_core::frontend::pace::pace_dup(&a.progress), t0);
    hb.read_starts(&match input {
        Input::Ndjson(file) => con_ron::render::display_path(file),
        Input::Oleans(req) => req.label(pers, &st),
    });
    // THE BUILT-IN PRELUDE, parsed into that store before anything else.
    // ConRon.Capstone: h2
    let prelude_ix = match prelude::builtin_prelude_e(pers, &mut st) {
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
    // Streaming frontend: the file is read 4 MiB at a time and each buffer is
    // parsed and dropped, so neither a wholesale text buffer nor a scratch
    // file exists.  What comes out is the FILE's records as HANDLES into the
    // store above.  No model is ever read from the input: every inductive
    // block — mutual and nested included — installs through the kernel's
    // uniform installer, unconditionally (task #105).
    // ConRon.Capstone: hreads, h3 (`parse_source` over the file's handle)
    // The `.olean` path ends in the same records (task #142); no capstone
    // premise is about it yet (OVERVIEW.md).
    // An `--olean` run's theorems hold references to their values, which their
    // jobs read (`driver::olean_job`); what that needs comes back beside the
    // records (`OleanRead`), and of it the check keeps only the pins and the
    // values (below, after the preparation).
    let read: std::io::Result<Result<(Vec<IDeclaration>, Option<OleanRead>), (CheckError, u64)>> = match input {
        Input::Ndjson(file) => match driver::parse_export_stream_d(pers, &mut st, file, export_c::CHUNK_SIZE) {
            Err(e) => {
                eprintln!("con-ron: {}: {}", con_ron::render::display_path(file), e);
                return 3;
            }
            Ok((r, _)) => Ok(r.map(|p: ParseResultD| (p.decls, None))),
        },
        Input::Oleans(req) => Ok(con_ron::olean_fs::read_request(pers, &mut st, req, &a.progress)
            .map(|mut rd| (std::mem::take(&mut rd.decls), Some(rd)))),
    };
    let label: String = match input {
        Input::Ndjson(file) => con_ron::render::display_path(file),
        Input::Oleans(req) => req.label(pers, &st),
    };
    let (parsed_decls, olean): (Vec<IDeclaration>, Option<OleanRead>) = match read {
        Err(_) => return 3,
        Ok(Err((e, line))) => match classify(&e) {
            FrontendClass::Declined(what) => {
                eprintln!("con-ron: declined: {} ({})", what, mode_tag);
                return 2;
            }
            // A stream whose inductive block contradicts its own declarations
            // in a REDUNDANT field is rejected at the parse.
            FrontendClass::Invalid(what) => {
                eprintln!("con-ron: invalid: {} ({})", what, mode_tag);
                return 1;
            }
            FrontendClass::Internal(msg) => {
                eprintln!("con-ron: {}:{}: {}", label, line, msg);
                return 3;
            }
        },
        Ok(Ok(r)) => r,
    };
    let file_records = parsed_decls.len();
    // From here on the store is the checker's state: the memo tables and the
    // per-declaration caches join it (`AState`), and every handle the parse
    // produced indexes into it.
    // **PREPARE** (`frontend::prepare`): what the fold runs over is
    // `prepare_prelude` of the file's records — the prelude's declarations
    // first (the stream's own copies where it has them, the rest synthesised),
    // then the stream's, with every pinned `Nat` operation's stream-certified
    // ground hoisted ahead of it.  It takes the whole state since task
    // #97-P4d: step 2 is the real ground hoist, which interns.
    // ConRon.Capstone: h4
    // What a record mentions, for the ground hoist: its expressions say it,
    // except a theorem's read from an `.olean`, whose load read it off the
    // file (con-leche's `usedOf`).
    let prepared = match match &olean {
        None => prepare::prepare_d(pers, &mut st, prelude_ix, parsed_decls, &DeclUsedConsts),
        Some(rd) => prepare::prepare_d(pers, &mut st, prelude_ix, parsed_decls, rd),
    } {
        Ok(p) => p,
        Err(e) => return frontend_exit(&e, mode_tag),
    };
    // **What the check keeps of the read** (con-leche's `checkOleansG` takes
    // `rd.values`): the reader's pins and the values' modules.  The merged
    // constants, whose last reader is the preparation (`OleanRead.thmUses`), go
    // here, before the pool: on Mathlib that is 0.8 M constants and their
    // `uses` (DESIGN, task #145).
    let olean: Option<(OleanPins, Vec<ModRef>)> =
        olean.map(|rd| (rd.pins, rd.values));
    // the ground hoist's receipt
    if !prepared.hoisted.is_empty() {
        let names: Vec<String> = prepared
            .hoisted
            .iter()
            .map(|n| driver::name_of(pers, &st.store, n))
            .collect();
        eprintln!(
            "con-ron: {} declarations hoisted ahead of the pinned Nat operations \
             they ground: {}",
            prepared.hoisted.len(),
            names.join(", ")
        );
    }
    // ConRon.Capstone: hpins (`decode_embedded`; `--pins`/`--no-pins` are
    // outside the theorems)
    let pins = match con_ron::driver::pins_for_run(&a.pins, a.no_pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return 3;
        }
    };
    // What the parse line reports, printed once the index is built.
    hb.file_records = file_records;
    hb.synthesised = prepared.synthesised;
    // **THE STARTUP PIN WALK** (DESIGN.md §8.6 P2d, task #97-P4d): every
    // pinned datum the checker compares a stream record against — the six
    // basis blocks in both forms, the axiom pins, the reserved names and the
    // `Nat`-operation variants — interned ONCE, here, while the scratch tier
    // is still off, so that nothing the fold compares against lives in a tier
    // that is about to vanish.  Its result is the fold's pin parameter.
    // ConRon.Capstone: h5
    let ipins = match checker::intern_all_pins(pers, &mut st, &pins, &a.max_nat_size) {
        Ok(p) => p,
        Err(e) => return frontend_exit(&e, mode_tag),
    };
    // ONE driver, and the heartbeat is printed between its steps
    // (`driver::check_decls_driver`: the index, the frozen tier, and the pool
    // for the check phase).
    let jobs: u64 = match a.jobs {
        Some(n) => n,
        None => con_ron::driver::default_jobs(),
    };
    // ONE lane, whatever the flags: the driver is what builds and freezes the
    // index and the check phase is the pool at every worker count, so a run
    // with no heartbeat is the same computation as a run with one.
    // ConRon.Capstone: the index, the freeze and the pool (the driver's steps,
    // either observer)
    let on = con_ron_core::frontend::pace::pace_on(&a.progress);
    let ds = &prepared.decls;
    let verdict = match (&olean, input) {
        (Some((pk, values)), Input::Oleans(req)) => {
            let sp = &req.search_path;
            let job = |tier: &PersTier, w: &mut AState, c: &mut ValueCache, k: u64| {
                driver::olean_job(tier, w, c, &mode, &ipins, ds, pk, values, sp, None, k)
            };
            if on {
                driver::check_decls_driver_with(pers, &mut st, ds, jobs, &mut hb, value_cache_empty, job)
            } else {
                driver::check_decls_driver_with(pers, &mut st, ds, jobs, &mut driver::Silent, value_cache_empty, job)
            }
        }
        _ => {
            if on {
                driver::check_decls_driver(pers, &mut st, &mode, &ipins, None, ds, jobs, &mut hb)
            } else {
                driver::check_decls_driver(pers, &mut st, &mode, &ipins, None, ds, jobs, &mut driver::Silent)
            }
        }
    };
    // **The headline number is the FILE's declaration-record count**: the
    // records the PARSE produced, which are the file's own.  Nothing the
    // preparation does moves it.
    let stream_records = file_records as u64;
    let code = match &verdict {
        Ok(_) => driver::verdict_accept(stream_records, mode_tag),
        Err((e, i)) => {
            driver::verdict_failure(pers, &st.store, &prepared.decls, e, *i, mode_tag, t0, "")
        }
    };
    exit_after_verdict(code)
}

/// con-leche: ConLeche/Driver/Dispatch.lean:63-88 runReq
/// The run on the checking thread: `check_main`, or a compared run's own driver
/// (`con_ron::compare`), whose verdict path exits as `check_main`'s does.
fn run(a: &Args, r: &Run) -> u8 {
    let mode_tag = if a.verified { "--verified" } else { "--trusted" };
    let mode = if a.verified { CheckMode::Verified } else { CheckMode::Trusted };
    match r {
        Run::Check(input) => check_main(a, input),
        Run::CompareJson(c, s) => exit_after_verdict(con_ron::compare::compare_json(&compare_opts(a, mode, mode_tag), c, s)),
        Run::CompareOleans(q) => exit_after_verdict(con_ron::compare::compare_oleans(&compare_opts(a, mode, mode_tag), q)),
        Run::Module(q, cmp) => exit_after_verdict(con_ron::modular::module_main(&compare_opts(a, mode, mode_tag), q, *cmp)),
        Run::Modular(q, cmp) => exit_after_verdict(con_ron::modular::modular_main(&compare_opts(a, mode, mode_tag), q, *cmp)),
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
/// A compared run's options, off the command line.
fn compare_opts<'a>(a: &'a Args, mode: CheckMode, mode_tag: &'a str) -> con_ron::compare::CompareOpts<'a> {
    con_ron::compare::CompareOpts {
        mode,
        mode_tag,
        max_nat_size: &a.max_nat_size,
        pins: &a.pins,
        no_pins: a.no_pins,
        jobs: match a.jobs {
            Some(n) => n,
            None => con_ron::driver::default_jobs(),
        },
        progress: &a.progress,
    }
}

/// con-leche: Main.lean:32-54 flushStdoutStderr
/// **The flush** before the exit: both streams, so that what the run printed
/// last — the verdict or diagnostic line — is written out, and the exit code:
/// `code`, or 3 if the flush fails (con-leche task #490): a run whose output
/// did not get out has no verdict anyone read.  The message is best-effort.
fn flush_stdout_stderr(code: u8) -> u8 {
    match std::io::stdout().flush().and_then(|()| std::io::stderr().flush()) {
        Ok(()) => code,
        Err(e) => {
            let _ = writeln!(std::io::stderr(), "con-ron: cannot write the output: {}", e);
            3
        }
    }
}

/// con-leche: Main.lean:56-103 main
/// con-leche task #336: **exit
/// right after the verdict, without freeing the heap**.  Returning would drop
/// the store, the parsed and prepared declarations and the environment on the
/// way out of `check_main` and `main` — at Mathlib scale a free cascade of
/// its own — so the verdict path flushes the two streams
/// (`flush_stdout_stderr`, 3 if that fails) and leaves the process here.  The
/// worker pool is joined inside `check_decls_driver`, so nothing is left
/// running.
fn exit_after_verdict(code: u8) -> ! {
    let code = flush_stdout_stderr(code);
    std::process::exit(code as i32)
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
/// con-leche: Main.lean:56-103 main
/// **The plumbing** (DESIGN.md §3.9): the arguments (one that is not UTF-8 is
/// exit 3), the checking thread, its stack `driver::stack_bytes` (1 GiB, or
/// `LEAN_STACK_SIZE_KB`), the instance `std_io::StdIo`, the verified driver's
/// `con_ron_core::driver::cli::run_args`, the flush and the exit — from the
/// checking thread, so that neither the instance nor what it kept is ever
/// dropped (con-leche task #336).  A panic on that thread is exit 3, never a
/// verdict.  The checker runs IN THIS PROCESS (only `--schedule`, a legacy
/// request, starts copies of this binary, its workers).
fn main() -> ! {
    let mut argv: Vec<String> = Vec::new();
    for a in std::env::args_os().skip(1) {
        match a.into_string() {
            Ok(s) => argv.push(s),
            Err(_) => {
                eprintln!("con-ron: an argument is not valid UTF-8");
                exit_after_verdict(3)
            }
        }
    }
    let h = std::thread::Builder::new()
        .stack_size(driver::stack_bytes())
        .spawn(move || -> u8 {
            let cps: Vec<Vec<u32>> = argv.iter().map(|a| con_ron::render::cps(a)).collect();
            let mut io = con_ron::std_io::StdIo::new(con_ron::std_io::StdIoHooks {
                help: print_help,
                synopsis: print_synopsis,
                usage: usage_error,
                legacy: run_main,
            });
            let code = con_ron_core::driver::cli::run_args(&mut io, &cps);
            // the instance (and what it kept) is never dropped: con-leche task #336
            exit_after_verdict(code)
        });
    match h {
        Err(e) => {
            eprintln!("con-ron: cannot spawn the checking thread: {}", e);
            exit_after_verdict(3)
        }
        Ok(h) => match h.join() {
            Ok(code) => exit_after_verdict(code),
            Err(_) => {
                eprintln!("con-ron: the checking thread died");
                exit_after_verdict(3)
            }
        },
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
/// `--help`: the help text on stdout, and the build's allocator; a failed
/// write is exit 3, as con-leche's `--help` on `/dev/full`.
fn print_help() -> u8 {
    // The one build-time choice a run's numbers depend on, printed rather
    // than merely documented (task #89).
    let out = writeln!(
        std::io::stdout(),
        "{}\n{}\n\n{}\nthis build's global allocator: {}",
        HELP_HEAD, SYNOPSIS, HELP_TAIL, con_ron_dump::ALLOCATOR
    );
    match out {
        Ok(()) => 0,
        Err(e) => {
            let _ = writeln!(std::io::stderr(), "con-ron: cannot write the output: {}", e);
            3
        }
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:116-132 synopsis
/// No arguments: the invocation forms, and the pointer to `--help`.
fn print_synopsis() {
    eprintln!("{}", SYNOPSIS);
    eprintln!("{}", TRY_HELP);
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
/// **The legacy driver** (`StdIo`'s `run_legacy`): the run up to its exit code
/// of every request the verified driver does not run (`--olean --schedule`,
/// with or without `--compare`, and `--olean --modular --pins`), from the whole
/// argument list: `--help`, the parse, and con-leche's usage checks in its
/// order.  Every other mode below is the verified driver's
/// (`con_ron_core::driver`), and is reached by no request.
fn run_main(argv: Vec<String>) -> u8 {
    if help_wanted(&argv) {
        // The one build-time choice a run's numbers depend on, printed rather
        // than merely documented (task #89).  A failed write is exit 3, as
        // con-leche's `--help` on `/dev/full`.
        let out = writeln!(
            std::io::stdout(),
            "{}\n{}\n\n{}\nthis build's global allocator: {}",
            HELP_HEAD, SYNOPSIS, HELP_TAIL, con_ron_dump::ALLOCATOR
        );
        return match out {
            Ok(()) => 0,
            Err(e) => {
                let _ = writeln!(std::io::stderr(), "con-ron: cannot write the output: {}", e);
                3
            }
        };
    }
    let a = parse_args(&argv);
    if let Some(msg) = &a.bad {
        return usage_error(msg);
    }
    if a.check_graph {
        return check_graph_usage(&a);
    }
    let input: Run = if a.olean {
        // `--olean`: the arguments are root modules, read with their import
        // closure along the search path, module names as Lean spells them.
        if a.files.is_empty() || (a.search_path.is_empty() && a.trusted_path.is_empty()) {
            return usage_error("--olean takes one or more module names and a --search-path=DIRS");
        }
        let req = match con_ron::olean_fs::OleanRequest::new(&a.search_path, &a.files, &a.constants) {
            Err(msg) => return usage_error(&msg),
            Ok(req) => req,
        };
        if a.compare {
            // `--compare`: a challenge and its solution, alone or as one module
            // of a modular run — con-leche's usage checks, then the mode.
            if req.roots.len() != 2 {
                return usage_error("--compare takes two module names, a challenge and its solution");
            }
            if same_module(&req.roots[0], &req.roots[1]) {
                return usage_error(
                    "--compare takes two different modules, a challenge and its solution",
                );
            }
            if a.module || a.modular || a.scheduled {
                if !a.constants.is_empty()
                    || (a.module && a.scheduled)
                    || (a.modular && (a.module || a.scheduled))
                {
                    return usage_error(
                        "--compare with --module, --modular or --schedule takes one of them, \
                         and no --constant",
                    );
                }
                if a.module || a.modular {
                    let mut rs = req.roots;
                    let s = rs.pop();
                    let c = rs.pop();
                    let q = match (c, s) {
                        (Some(c), Some(s)) => cmp_request(&a, c, Some(s)),
                        _ => return 3,
                    };
                    if a.module {
                        Run::Module(q, true)
                    } else {
                        Run::Modular(q, true)
                    }
                } else {
                let mut rs = req.roots;
                let s = rs.pop();
                let c = rs.pop();
                return match (c, s) {
                    (Some(c), Some(s)) => con_ron::modular::schedule(&schedule_req(&a, c, Some(s))),
                    _ => 3,
                };
                }
            } else {
            let dirs = |v: &Vec<String>| -> Vec<Vec<u32>> { v.iter().map(|d| con_ron::render::cps(d)).collect() };
            let mut roots = req.roots;
            let s = roots.pop();
            let c = roots.pop();
            match (c, s) {
                (Some(c), Some(s)) => Run::CompareOleans(con_ron::compare::CmpRequest {
                    challenge: c,
                    solution: s,
                    trusted: dirs(&a.trusted_path),
                    path: dirs(&a.search_path),
                    constants: req.constants,
                }),
                _ => return usage_error("--compare takes two module names, a challenge and its solution"),
            }
            }
        } else {
        if !a.trusted_path.is_empty() && (!a.module || a.modular || a.scheduled) {
            return usage_error("--trusted-search-path takes --compare or --module");
        }
        if a.scheduled {
            if req.roots.len() != 1 || !a.constants.is_empty() || a.module || a.modular {
                return usage_error(
                    "--schedule takes one module name, and none of --constant, --module and \
                     --modular",
                );
            }
            let mut rs = req.roots;
            return match rs.pop() {
                Some(m) => con_ron::modular::schedule(&schedule_req(&a, m, None)),
                None => 3,
            };
        }
        if a.modular {
            if req.roots.len() != 1 || !a.constants.is_empty() || a.module {
                return usage_error(
                    "--modular takes one module name, and neither --constant nor --module",
                );
            }
            let mut rs = req.roots;
            return match rs.pop() {
                Some(m) => { let q = cmp_request(&a, m, None); run_on_thread(a, Run::Modular(q, false)) }
                None => 3,
            };
        }
        if a.module {
            if req.roots.len() != 1 || !a.constants.is_empty() {
                return usage_error("--module takes one module name and no --constant");
            }
            let mut rs = req.roots;
            return match rs.pop() {
                Some(m) => { let q = cmp_request(&a, m, None); run_on_thread(a, Run::Module(q, false)) }
                None => 3,
            };
        }
        Run::Check(Input::Oleans(req))
        }
    } else {
        if a.compare {
            // `--compare` on two lean4export files: con-leche's usage checks,
            // then the mode.
            if !a.search_path.is_empty()
                || !a.constants.is_empty()
                || a.module
                || a.modular
                || a.scheduled
                || !a.trusted_path.is_empty()
            {
                return usage_error(
                    "--compare on two lean4export files takes none of --search-path, \
                     --trusted-search-path, --constant, --module, --modular and --schedule \
                     (they take --olean)",
                );
            }
            if a.files.len() != 2 {
                return usage_error("--compare takes two files, a challenge and its solution");
            }
            if a.files[0] == a.files[1] {
                return usage_error(
                    "--compare takes two different files, a challenge and its solution",
                );
            }
            Run::CompareJson(a.files[0].clone(), a.files[1].clone())
        } else {
        if !a.search_path.is_empty()
            || !a.constants.is_empty()
            || a.module
            || a.modular
            || a.scheduled
            || !a.trusted_path.is_empty()
        {
            return usage_error(
                "--search-path, --trusted-search-path, --constant, --module, --modular and \
                 --schedule take --olean",
            );
        }
        match a.files.len() {
            1 => (),
            // no arguments: the invocation forms, and the pointer to `--help`
            0 => {
                eprintln!("{}", SYNOPSIS);
                eprintln!("{}", TRY_HELP);
                return 3;
            }
            _ => return usage_error("takes one input file"),
        }
        Run::Check(Input::Ndjson(a.files[0].clone()))
        }
    };
    run_on_thread(a, input)
}

/// con-leche: Main.lean:56-103 main
/// The run on its checking thread, its stack `driver::stack_bytes` (1 GiB by default): a
/// panic on it is exit 3, never a verdict.
fn run_on_thread(a: Args, input: Run) -> u8 {
    let h = std::thread::Builder::new()
        .stack_size(driver::stack_bytes())
        .spawn(move || run(&a, &input));
    match h {
        Err(e) => {
            eprintln!("con-ron: cannot spawn the checking thread: {}", e);
            3
        }
        Ok(h) => match h.join() {
            Ok(code) => code,
            Err(_) => {
                eprintln!("con-ron: the checking thread died");
                3
            }
        },
    }
}
