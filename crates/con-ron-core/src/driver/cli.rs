//! `driver::cli` — con-leche's `Driver/Cli.lean`: the argument parser, every
//! flag con-ron takes, and `run_args`, the binary's `main` but its plumbing
//! (DESIGN.md §3.9, task #171).
//!
//! The parse is `crates/con-ron/src/bin/con-ron.rs`'s `parse_args`, clause for
//! clause, over code points: the same flags in the same order, the first bad
//! argument the one reported (`Bad`, rendered by the instance in the binary's
//! words).  `run_args` runs `--help`, the usage errors, and the check of one
//! lean4export file (`check_main`); every other request (`--olean`,
//! `--check-graph`, `--compare`) goes, whole, to the instance's `run_legacy`.

use crate::arena::pins::max_nat_size_default;
use crate::driver::check_main;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::nat_decimal;
use crate::frontend::pace::Pace;
use crate::frontend::text::cps_beq;
use crate::frontend::text::cps_starts_with;
use crate::kernel::expr::str_copy;
use crate::kernel::expr::str_copy_from;
use crate::ron::nat::Nat;

/// con-leche: none — the word `--`
const W_END: [u32; 2] = [45, 45];
/// con-leche: none — the word `--help`
const W_HELP: [u32; 6] = [45, 45, 104, 101, 108, 112];
/// con-leche: none — the word `--verified`
const W_VERIFIED: [u32; 10] = [45, 45, 118, 101, 114, 105, 102, 105, 101, 100];
/// con-leche: none — the word `--trusted`
const W_TRUSTED: [u32; 9] = [45, 45, 116, 114, 117, 115, 116, 101, 100];
/// con-leche: none — the word `--progress`
const W_PROGRESS: [u32; 10] = [45, 45, 112, 114, 111, 103, 114, 101, 115, 115];
/// con-leche: none — the word `--no-pins`
const W_NO_PINS: [u32; 9] = [45, 45, 110, 111, 45, 112, 105, 110, 115];
/// con-leche: none — the word `--olean`
const W_OLEAN: [u32; 7] = [45, 45, 111, 108, 101, 97, 110];
/// con-leche: none — the word `--check-graph`
const W_CHECK_GRAPH: [u32; 13] = [45, 45, 99, 104, 101, 99, 107, 45, 103, 114, 97, 112, 104];
/// con-leche: none — the word `--module`
const W_MODULE: [u32; 8] = [45, 45, 109, 111, 100, 117, 108, 101];
/// con-leche: none — the word `--modular`
const W_MODULAR: [u32; 9] = [45, 45, 109, 111, 100, 117, 108, 97, 114];
/// con-leche: none — the word `--compare`
const W_COMPARE: [u32; 9] = [45, 45, 99, 111, 109, 112, 97, 114, 101];
/// con-leche: none — the word `--pins`
const W_PINS: [u32; 6] = [45, 45, 112, 105, 110, 115];
/// con-leche: none — the word `--jobs`
const W_JOBS: [u32; 6] = [45, 45, 106, 111, 98, 115];
/// con-leche: none — the prefix `--progress=`
const W_PROGRESS_EQ: [u32; 11] = [45, 45, 112, 114, 111, 103, 114, 101, 115, 115, 61];
/// con-leche: none — the prefix `--jobs=`
const W_JOBS_EQ: [u32; 7] = [45, 45, 106, 111, 98, 115, 61];
/// con-leche: none — the prefix `--max-nat-size=`
const W_MAX_NAT_SIZE_EQ: [u32; 15] = [45, 45, 109, 97, 120, 45, 110, 97, 116, 45, 115, 105, 122, 101, 61];
/// con-leche: none — the prefix `--pins=`
const W_PINS_EQ: [u32; 7] = [45, 45, 112, 105, 110, 115, 61];
/// con-leche: none — the prefix `--constant=`
const W_CONSTANT_EQ: [u32; 11] = [45, 45, 99, 111, 110, 115, 116, 97, 110, 116, 61];
/// con-leche: none — the prefix `--search-path=`
const W_SEARCH_PATH_EQ: [u32; 14] = [45, 45, 115, 101, 97, 114, 99, 104, 45, 112, 97, 116, 104, 61];
/// con-leche: none — the prefix `--trusted-search-path=`
const W_TRUSTED_SEARCH_PATH_EQ: [u32; 22] =
    [45, 45, 116, 114, 117, 115, 116, 101, 100, 45, 115, 101, 97, 114, 99, 104, 45, 112, 97, 116, 104, 61];
/// con-leche: none — the prefix `--schedule`
const W_SCHEDULE: [u32; 10] = [45, 45, 115, 99, 104, 101, 100, 117, 108, 101];
/// con-leche: none — the prefix `--worker-stack-size=`
const W_WORKER_STACK_SIZE_EQ: [u32; 20] =
    [45, 45, 119, 111, 114, 107, 101, 114, 45, 115, 116, 97, 99, 107, 45, 115, 105, 122, 101, 61];

/// con-leche: ConLeche/Driver/Cli.lean:262-303 Args
/// **A usage error**, as a structured event: which one, and the argument it is
/// about.  The instance renders each in the binary's words (`StdIo::usage`).
pub enum Bad {
    /// `--pins` with no argument after it
    PinsNoFile,
    /// the bare `--jobs`
    JobsBare,
    /// a `--progress=` value of no form
    ProgressValue(Vec<u32>),
    /// `--jobs=0`
    JobsZero,
    /// a `--jobs=` value that is no numeral
    JobsValue(Vec<u32>),
    /// a `--max-nat-size=` value that is no numeral
    MaxNatValue(Vec<u32>),
    /// a `--worker-stack-size=` value that is no size
    WorkerStackValue(Vec<u32>),
    /// a `-`-leading word that is no flag
    UnknownOption(Vec<u32>),
    /// `--worker-stack-size` without `--schedule`
    WorkerStackNoSchedule,
    /// a lean4export check with a flag of `--olean`'s
    TakeOlean,
    /// a lean4export check with more than one file
    OneInputFile,
}

/// con-leche: ConLeche/Driver/Cli.lean:262-303 Args
/// What the command line asked for: the binary's `Args`, the fields the
/// verified driver reads or routes on.  The values only an unverified mode
/// reads (`--schedule`'s options, `--worker-stack-size`'s size) are read again
/// by that mode's own parse.
pub struct Args {
    /// the positional arguments
    pub files: Vec<Vec<u32>>,
    /// `--verified` (the default) or `--trusted`
    pub verified: bool,
    /// the heartbeat's pace (`--progress`)
    pub progress: Pace,
    /// `--jobs=<n>`
    pub jobs: Option<u64>,
    /// `--max-nat-size=<n>`
    pub max_nat_size: Nat,
    /// `--pins FILE`
    pub pins: Option<Vec<u32>>,
    /// `--no-pins`
    pub no_pins: bool,
    /// `--olean`
    pub olean: bool,
    /// `--search-path=DIR:DIR...`, the nonempty directories
    pub search_path: Vec<Vec<u32>>,
    /// `--constant=NAME`
    pub constants: Vec<Vec<u32>>,
    /// `--check-graph`
    pub check_graph: bool,
    /// `--module`
    pub module: bool,
    /// `--modular`
    pub modular: bool,
    /// some `--schedule` flag was given
    pub scheduled: bool,
    /// `--compare`
    pub compare: bool,
    /// `--trusted-search-path=DIR:DIR...`, the nonempty directories
    pub trusted_path: Vec<Vec<u32>>,
    /// `--worker-stack-size=SIZE` was given, with a valid size
    pub worker_stack: bool,
    /// the first bad argument
    pub bad: Option<Bad>,
}

/// con-leche: ConLeche/Driver/Cli.lean:262-303 Args
/// The arguments before any is read: every default.
pub fn args_default() -> Args {
    Args {
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
        scheduled: false,
        compare: false,
        trusted_path: Vec::new(),
        worker_stack: false,
        bad: None,
    }
}

/// con-leche: none — Rust's `u64::from_str` on code points `s[from..to]`
/// The value of a decimal numeral as the binary's `str::parse::<u64>` reads
/// one: an optional `+`, then at least one ASCII digit and nothing else, at
/// most `u64::MAX`.
pub fn parse_u64(s: &Vec<u32>, from: usize, to: usize) -> Option<u64> {
    let mut i = from;
    if i < to && s[i] == 43 {
        i += 1;
    }
    if i >= to {
        return None;
    }
    let mut acc: u64 = 0;
    loop {
        if i >= to {
            return Some(acc);
        }
        let c = s[i];
        if c < 48 || c > 57 {
            return None;
        }
        let d = (c - 48) as u64;
        if acc > 1844674407370955161 || (acc == 1844674407370955161 && d > 5) {
            return None;
        }
        acc = acc * 10 + d;
        i += 1;
    }
}

/// con-leche: none — Lean core's `String.Slice.isNat`, which `String.toNat?` tests first
/// Whether `s[from..to]` is a decimal numeral as Lean's `String.toNat?` takes
/// one: not empty, ASCII digits, each `_` right after a digit, ending in a
/// digit.
pub fn is_nat(s: &Vec<u32>, from: usize, to: usize) -> bool {
    let mut last_was_digit = false;
    let mut i = from;
    loop {
        if i >= to {
            return last_was_digit;
        }
        let c = s[i];
        if c == 95 {
            if !last_was_digit {
                return false;
            }
            last_was_digit = false;
        } else if c >= 48 && c <= 57 {
            last_was_digit = true;
        } else {
            return false;
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:62-93 progressPace
/// The heartbeat's pace off a `--progress=` value: `N` declarations, `P%`
/// (1 to 100) of a phase, or `Ss` seconds; a zero or any other form is a usage
/// error.
pub fn progress_pace(v: &Vec<u32>) -> Result<Pace, Bad> {
    let n = v.len();
    if n > 0 && v[n - 1] == 37 {
        match parse_u64(v, 0, n - 1) {
            Some(p) => {
                if p >= 1 && p <= 100 {
                    Ok(Pace::Percent(p))
                } else {
                    Err(Bad::ProgressValue(str_copy(v)))
                }
            }
            None => Err(Bad::ProgressValue(str_copy(v))),
        }
    } else if n > 0 && v[n - 1] == 115 {
        match parse_u64(v, 0, n - 1) {
            Some(s) => {
                if s == 0 {
                    Err(Bad::ProgressValue(str_copy(v)))
                } else {
                    Ok(Pace::Seconds(s))
                }
            }
            None => Err(Bad::ProgressValue(str_copy(v))),
        }
    } else {
        match parse_u64(v, 0, n) {
            Some(k) => {
                if k == 0 {
                    Err(Bad::ProgressValue(str_copy(v)))
                } else {
                    Ok(Pace::Every(k))
                }
            }
            None => Err(Bad::ProgressValue(str_copy(v))),
        }
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:95-108 jobsCount
/// The worker count off a `--jobs=` value: a numeral of at least 1.
pub fn jobs_count(v: &Vec<u32>) -> Result<u64, Bad> {
    match parse_u64(v, 0, v.len()) {
        Some(k) => {
            if k == 0 {
                Err(Bad::JobsZero)
            } else {
                Ok(k)
            }
        }
        None => Err(Bad::JobsValue(str_copy(v))),
    }
}

/// con-leche: none — the digits of an `is_nat` numeral, its `_`s dropped
fn nat_digits(v: &Vec<u32>) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::new();
    let mut i = 0usize;
    while i < v.len() {
        let c = v[i];
        if c >= 48 && c <= 57 {
            out.push(c as u8);
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Cli.lean:110-115 maxNatSizeArg
/// The maximum `Nat` size off a `--max-nat-size=` value: a numeral as
/// `String.toNat?` reads it (`is_nat`).
pub fn max_nat_size_arg(v: &Vec<u32>) -> Result<Nat, Bad> {
    if !is_nat(v, 0, v.len()) {
        return Err(Bad::MaxNatValue(str_copy(v)));
    }
    match nat_decimal::from_decimal(&nat_digits(v)) {
        Some(n) => Ok(n),
        None => Err(Bad::MaxNatValue(str_copy(v))),
    }
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:81-93 parseSize
/// Whether `v` is a `--worker-stack-size=` value: a POSITIVE size with a unit,
/// `K`, `M`, `G` or `T` (either case), the number before it as `is_nat` reads
/// one.
pub fn size_positive(v: &Vec<u32>) -> bool {
    let n = v.len();
    if n == 0 {
        return false;
    }
    let u = v[n - 1];
    // `K`, `k`, `M`, `m`, `G`, `g`, `T`, `t`: a `match`, since Aeneas types the last
    // comparison of an `||` chain bound by `let` as a `Prop` (task #171)
    let has_unit = match u {
        75 | 107 | 77 | 109 | 71 | 103 | 84 | 116 => true,
        _ => false,
    };
    if !has_unit || !is_nat(v, 0, n - 1) {
        return false;
    }
    let mut i = 0usize;
    loop {
        if i >= n - 1 {
            return false;
        }
        if v[i] != 48 && v[i] != 95 {
            return true;
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:305-308 helpWanted
/// `--help` before any `--`: after a `--` every argument is a file.
pub fn help_wanted(argv: &Vec<Vec<u32>>) -> bool {
    let mut i = 0usize;
    loop {
        if i >= argv.len() {
            return false;
        }
        if cps_beq(&argv[i], &W_END) {
            return false;
        }
        if cps_beq(&argv[i], &W_HELP) {
            return true;
        }
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:316-319 searchPathOf
/// The nonempty `:`-separated directories of `v` from `from`, after `out`.
pub fn push_dirs(out: Vec<Vec<u32>>, v: &Vec<u32>, from: usize) -> Vec<Vec<u32>> {
    let mut out = out;
    let mut cur: Vec<u32> = Vec::new();
    let mut i = from;
    while i < v.len() {
        if v[i] == 58 {
            if cur.len() > 0 {
                out.push(cur);
            }
            cur = Vec::new();
        } else {
            cur.push(v[i]);
        }
        i += 1;
    }
    if cur.len() > 0 {
        out.push(cur);
    }
    out
}

/// con-leche: ConLeche/Driver/Cli.lean:326-378 parseArgs
/// Every argument of `argv` from `i`, as files, after `out`.
pub fn push_files(out: Vec<Vec<u32>>, argv: &Vec<Vec<u32>>, i: usize) -> Vec<Vec<u32>> {
    let mut out = out;
    let mut i = i;
    while i < argv.len() {
        out.push(str_copy(&argv[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Cli.lean:326-378 parseArgs
/// The first bad argument is the one reported.
pub fn with_bad(a: Args, b: Bad) -> Args {
    let mut a = a;
    match &a.bad {
        Some(_) => (),
        None => a.bad = Some(b),
    }
    a
}

/// con-leche: ConLeche/Driver/Cli.lean:321-324 Args.closed
/// The arguments once all are read: `--worker-stack-size` without
/// `--schedule` is a usage error (no other run starts a worker).
pub fn closed(a: Args) -> Args {
    if a.worker_stack && !a.scheduled {
        with_bad(a, Bad::WorkerStackNoSchedule)
    } else {
        a
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:326-378 parseArgs
/// A word with a value after a prefix (`--jobs=8`): the `=`-carrying flags, in
/// the binary's order, then an unknown `-`-leading word, then a file.
pub fn parse_valued(a: Args, s: &Vec<u32>) -> Args {
    let mut a = a;
    if cps_starts_with(s, &W_PROGRESS_EQ) {
        match progress_pace(&str_copy_from(s, 11, Vec::new())) {
            Ok(p) => a.progress = p,
            Err(b) => a = with_bad(a, b),
        }
    } else if cps_starts_with(s, &W_JOBS_EQ) {
        match jobs_count(&str_copy_from(s, 7, Vec::new())) {
            Ok(n) => a.jobs = Some(n),
            Err(b) => a = with_bad(a, b),
        }
    } else if cps_starts_with(s, &W_MAX_NAT_SIZE_EQ) {
        match max_nat_size_arg(&str_copy_from(s, 15, Vec::new())) {
            Ok(n) => a.max_nat_size = n,
            Err(b) => a = with_bad(a, b),
        }
    } else if cps_starts_with(s, &W_PINS_EQ) {
        a.pins = Some(str_copy_from(s, 7, Vec::new()));
    } else if cps_starts_with(s, &W_CONSTANT_EQ) {
        a.constants.push(str_copy_from(s, 11, Vec::new()));
    } else if cps_starts_with(s, &W_SEARCH_PATH_EQ) {
        a.search_path = push_dirs(a.search_path, s, 14);
    } else if cps_starts_with(s, &W_TRUSTED_SEARCH_PATH_EQ) {
        a.trusted_path = push_dirs(a.trusted_path, s, 22);
    } else if cps_starts_with(s, &W_SCHEDULE) {
        a.scheduled = true;
    } else if cps_starts_with(s, &W_WORKER_STACK_SIZE_EQ) {
        let v = str_copy_from(s, 20, Vec::new());
        if size_positive(&v) {
            a.worker_stack = true;
        } else {
            a = with_bad(a, Bad::WorkerStackValue(v));
        }
    } else if s.len() > 0 && s[0] == 45 {
        a = with_bad(a, Bad::UnknownOption(str_copy(s)));
    } else {
        a.files.push(str_copy(s));
    }
    a
}

/// con-leche: ConLeche/Driver/Cli.lean:326-378 parseArgs
/// One argument at `argv[i]` (not `--`), and the position of the last one it
/// read: `--pins` reads the next as its file.
pub fn parse_one(a: Args, argv: &Vec<Vec<u32>>, i: usize) -> (Args, usize) {
    let mut a = a;
    let s = &argv[i];
    if cps_beq(s, &W_VERIFIED) {
        a.verified = true;
    } else if cps_beq(s, &W_TRUSTED) {
        a.verified = false;
    } else if cps_beq(s, &W_PROGRESS) {
        a.progress = Pace::Every(1);
    } else if cps_beq(s, &W_NO_PINS) {
        a.no_pins = true;
    } else if cps_beq(s, &W_OLEAN) {
        a.olean = true;
    } else if cps_beq(s, &W_CHECK_GRAPH) {
        a.check_graph = true;
    } else if cps_beq(s, &W_MODULE) {
        a.module = true;
    } else if cps_beq(s, &W_MODULAR) {
        a.modular = true;
    } else if cps_beq(s, &W_COMPARE) {
        a.compare = true;
    } else if cps_beq(s, &W_PINS) {
        if i + 1 >= argv.len() {
            a = with_bad(a, Bad::PinsNoFile);
        } else {
            a.pins = Some(str_copy(&argv[i + 1]));
        }
        return (a, i + 1);
    } else if cps_beq(s, &W_JOBS) {
        a = with_bad(a, Bad::JobsBare);
    } else {
        a = parse_valued(a, s);
    }
    (a, i)
}

/// con-leche: ConLeche/Driver/Cli.lean:326-378 parseArgs
/// **The argument parse**, clause for clause as the binary's: the mode flags in
/// either order with the heartbeat, `=`-carrying spellings after the bare
/// ones, an unknown `-`-leading word a usage error, everything else a file,
/// and every argument after `--` a file.
pub fn parse_args(argv: &Vec<Vec<u32>>) -> Args {
    let mut a = args_default();
    let mut i = 0usize;
    loop {
        if i >= argv.len() {
            return closed(a);
        }
        if cps_beq(&argv[i], &W_END) {
            a.files = push_files(a.files, argv, i + 1);
            return closed(a);
        }
        let (a1, j) = parse_one(a, argv, i);
        a = a1;
        i = j + 1;
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **The run of an argument list, to its exit code**: `--help`, the parse and
/// its usage error, then the request.  A lean4export file is checked here
/// (`check_main`), after the binary's usage checks of that mode; `--olean`,
/// `--check-graph` and `--compare` are the legacy driver's
/// (`CheckerIo::run_legacy`).
pub fn run_args<I: CheckerIo>(io: &mut I, argv: &Vec<Vec<u32>>) -> u8 {
    if help_wanted(argv) {
        return io.print_help();
    }
    let a = parse_args(argv);
    match &a.bad {
        Some(b) => {
            io.usage(b);
            return 3;
        }
        None => (),
    }
    if a.check_graph || a.olean || a.compare {
        return io.run_legacy(argv);
    }
    if a.search_path.len() > 0
        || a.constants.len() > 0
        || a.module
        || a.modular
        || a.scheduled
        || a.trusted_path.len() > 0
    {
        io.usage(&Bad::TakeOlean);
        return 3;
    }
    if a.files.len() == 0 {
        io.note(&check_main::Note::Synopsis);
        return 3;
    }
    if a.files.len() != 1 {
        io.usage(&Bad::OneInputFile);
        return 3;
    }
    check_main::check_main(io, &a, &a.files[0])
}
