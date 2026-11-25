//! `con-ron` — con-leche's `Main.lean`: the binary's `main` (DESIGN.md §3.9, task #171).
//!
//! ```text
//! con-ron [OPTIONS] [--] FILE.ndjson
//! con-ron [OPTIONS] --compare [--] CHALLENGE.ndjson SOLUTION.ndjson
//! con-ron [OPTIONS] --olean --search-path=DIRS [--constant=NAME]... [--] MODULE...
//! con-ron [OPTIONS] --check-graph | --olean --module | --olean --modular | --olean --schedule ...
//! con-ron --help
//! ```
//!
//! **`main` is plumbing.**  Every request is the verified driver's,
//! `con_ron_core::driver::cli::run_args`, at the binary's instance of
//! `CheckerIo`, `con_ron::std_io::StdIo`: the argument parse, the usage errors,
//! every mode, the verdict.  What is left here is what con-leche's `Main.lean`
//! does around its `runArgs`: the arguments (one that is not UTF-8 is exit 3),
//! the checking thread and its stack, the flush, and the exit from that thread
//! without freeing the heap (con-leche task #336); and the binary's own text —
//! the synopsis, the help, the usage error's two lines — which `StdIo` renders
//! with (`StdIoHooks`).  `--schedule` is the one mode that is not the driver's
//! own (con-leche's is `liftIO`): `StdIo::run_schedule` runs
//! `con_ron::modular::schedule`, which starts copies of this binary, each a
//! `--module` run.
//!
//! Exit codes are con-leche's (`Driver/CheckMain.lean`'s `exitCode`): 0
//! accepted, 1 rejected, 2 declined, 3 usage, malformed input or an internal
//! failure.  Out of memory is neither (a Rust allocation failure aborts, which
//! a shell reports as 134) and a panic on the checking thread is 3.
//!
//! **No temporary files** (con-leche task #180): the checker writes nothing
//! outside its own stdout and stderr.

use std::io::Write;

use con_ron::driver;

// The global allocator is `con-ron-dump`'s (task #35's mimalloc, declared by
// that crate's lib): a program may declare only one, and this binary links
// that crate anyway — for `natdec`, the decimal rendering the scheduler's
// worker command lines use.  So this
// crate declares none but *chooses*: `crates/con-ron/Cargo.toml` takes
// that crate with `default-features = false` and forwards `mimalloc` (the
// default) and `jemalloc`, exactly as `crates/con-ron` does, so the two
// binaries are measured on the same allocator unless a build says otherwise.
// `--help` prints `con_ron_dump::ALLOCATOR` so a measurement can be
// reproduced.

/// con-leche: ConLeche/Driver/Cli.lean:116-122 synopsis
/// The invocation forms, printed on their own when there are no arguments.
const SYNOPSIS: &str = "\
Usage:
  con-ron [OPTIONS] FILE.ndjson
  con-ron [OPTIONS] --compare CHALLENGE.ndjson SOLUTION.ndjson
  con-ron [OPTIONS] --olean --search-path=DIRS MODULE...
  con-ron [OPTIONS] --olean --search-path=DIRS --compare CHALLENGE SOLUTION";

/// con-leche: ConLeche/Driver/Cli.lean:124-125 tryHelp
/// The line after a usage error.
const TRY_HELP: &str = "Try 'con-ron --help' for more information.";

/// con-leche: ConLeche/Driver/Cli.lean:127-175 helpText
/// The `--help` text: con-leche's, with this binary's name and con-ron's
/// documentation.  DESIGN.md §3.1: message
/// strings need not match.  Short on purpose, as con-leche's: one line per
/// option (two at most), the exit codes and the links; explanations belong
/// in OVERVIEW.md.
const HELP_HEAD: &str = "\
Check Lean declarations from a lean4export file or from .olean modules.
";

/// con-leche: ConLeche/Driver/Cli.lean:127-175 helpText
/// The rest of the `--help` text, after the synopsis.  The scheduler is the
/// simple one (`con_ron::schedule`): the two settings con-ron does not run
/// are listed by name, as usage errors, in place of their descriptions.
const HELP_TAIL: &str = "\
Options:
  --verified          Check in the mode the soundness theorem covers (default)
  --trusted           Skip the checks only the proof needs; outside the theorem
  --jobs=N            Worker threads (default: hardware threads, at most 16)
  --max-nat-size=N    Largest Nat numeral in bytes (default 134217728)
  --progress[=PACE]   Progress on stderr; PACE is N declarations, P% or Ss
  --compare           Check SOLUTION, then CHALLENGE with its axioms and
                      sorry-holes justified by SOLUTION
  --help              Print this help and exit
  --                  End of options

.olean input:
  --olean             Read modules and their imports from .olean files
  --search-path=DIRS  Colon-separated .olean directories; repeatable. In a
                      Lake project: \"$(lake env printenv LEAN_PATH)\"
  --trusted-search-path=DIRS
                      Trusted .olean directories (with --compare or --module)
  --constant=NAME     Check only NAME and what it mentions; repeatable
                      (outside the theorems)
  --check-graph       Check only that the import graph is acyclic
  --module            Check only MODULE's own declarations
  --modular           Check each module of the closure on its own
  --schedule          Check each module in its own --module process

Scheduler options (each --schedule-... option implies --schedule):
  --schedule-timeout=S      Time limit per worker, in seconds
  --schedule-order=ORDER    shuffled (default) or graph
  --schedule-commands       Print the worker commands instead of running them
  --worker-stack-size=SIZE  Thread stack size of the workers (e.g. 8G)
  --schedule-memory=SIZE, --schedule-log=FILE: con-leche's, not run here
                            (a usage error, exit 3)

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

/// con-leche: Main.lean:56-103 main
/// con-leche task #336: **exit
/// right after the verdict, without freeing the heap**.  Returning would drop
/// the store, the parsed and prepared declarations and the environment on the
/// way out of `check_main` and `main` — at Mathlib scale a free cascade of
/// its own — so the verdict path flushes the two streams
/// (`std_io::flush_stdout_stderr`, 3 if that fails) and leaves the process
/// here.  The worker map is joined inside the driver, so nothing is left
/// running.
fn exit_after_verdict(code: u8) -> ! {
    let code = con_ron::std_io::flush_stdout_stderr(code);
    std::process::exit(code as i32)
}

/// con-leche: ConLeche/Driver/Cli.lean:302-521 runArgs
/// con-leche: Main.lean:56-103 main
/// **The plumbing** (DESIGN.md §3.9): the arguments (one that is not UTF-8 is
/// exit 3), the checking thread, its stack `driver::stack_bytes` (1 GiB, or
/// `LEAN_STACK_SIZE_KB`), the instance `std_io::StdIo`, the verified driver's
/// `con_ron_core::driver::cli::run_args`, the flush and the exit — from the
/// checking thread, so that neither the instance nor what it kept is ever
/// dropped (con-leche task #336).  A panic on that thread is exit 3, never a
/// verdict.  The checker runs IN THIS PROCESS (only `--schedule` starts
/// copies of this binary, its workers).
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

/// con-leche: ConLeche/Driver/Cli.lean:302-521 runArgs
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

/// con-leche: ConLeche/Driver/Cli.lean:116-122 synopsis
/// No arguments: the invocation forms, and the pointer to `--help`.
fn print_synopsis() {
    eprintln!("{}", SYNOPSIS);
    eprintln!("{}", TRY_HELP);
}
