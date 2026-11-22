//! `driver::cli` — con-leche's `Driver/Cli.lean`: the argument parser, every
//! flag con-ron takes, and `run_args`, the binary's `main` but its plumbing
//! (DESIGN.md §3.9, task #171).
//!
//! The parse is `crates/con-ron/src/bin/con-ron.rs`'s `parse_args`, clause for
//! clause, over code points: the same flags in the same order, the first bad
//! argument the one reported (`Bad`, rendered by the instance in the binary's
//! words).  `run_args` runs `--help`, the usage errors, the check of one
//! lean4export file (`check_main`), the comparison of two (`compare_json`),
//! `--check-graph` (`graph`, with `--compare` `compare_module`), and `--olean`
//! on a closure, `--module` and `--modular` (`check_main::check_oleans`,
//! `worker`, `modular`), each also with `--compare` (`compare`,
//! `compare_module`, `modular`); `--schedule`, after its usage checks, is the
//! instance's scheduler (`CheckerIo::run_schedule`, con-leche's `liftIO`).

use crate::arena::pins::max_nat_size_default;
use crate::driver::check_main;
use crate::driver::compare;
use crate::driver::compare_json;
use crate::driver::compare_module;
use crate::driver::graph;
use crate::driver::modular;
use crate::driver::worker;
use crate::frontend::olean::files;
use crate::frontend::olean::files::Roots;
use crate::kernel::name::Name;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::nat_decimal;
use crate::frontend::pace::Pace;
use crate::frontend::text::cps_beq;
use crate::frontend::text::cps_starts_with;
use crate::kernel::name;
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
/// con-leche: none — the word `--jobs`
const W_JOBS: [u32; 6] = [45, 45, 106, 111, 98, 115];
/// con-leche: none — the prefix `--progress=`
const W_PROGRESS_EQ: [u32; 11] = [45, 45, 112, 114, 111, 103, 114, 101, 115, 115, 61];
/// con-leche: none — the prefix `--jobs=`
const W_JOBS_EQ: [u32; 7] = [45, 45, 106, 111, 98, 115, 61];
/// con-leche: none — the prefix `--max-nat-size=`
const W_MAX_NAT_SIZE_EQ: [u32; 15] = [45, 45, 109, 97, 120, 45, 110, 97, 116, 45, 115, 105, 122, 101, 61];
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
    /// `--compare` on lean4export files with a flag of `--olean`'s
    CompareTakeOlean,
    /// `--compare` on lean4export files without exactly two
    CompareTwoFiles,
    /// `--compare` on one lean4export file twice
    CompareSameFile,
    /// `--check-graph` with a flag it does not take
    CheckGraphFlags,
    /// `--check-graph` without its module names or a lookup
    CheckGraphArgs,
    /// a module name that does not parse
    NotModuleName(Vec<u32>),
    /// `--olean` without its module names or a lookup
    OleanArgs,
    /// a constant's name that does not parse
    NotConstName(Vec<u32>),
    /// `--trusted-search-path` without `--compare` or `--module`
    TrustedTakes,
    /// `--modular` with other than one module, or a flag it does not take
    ModularArgs,
    /// `--module` with other than one module, or a constant
    ModuleArgs,
    /// `--check-graph --compare` without exactly two module names
    CheckGraphCompareTwo,
    /// `--olean --compare` without exactly two module names
    CompareTwoModules,
    /// `--compare` on one module twice
    CompareSameModule,
    /// `--compare` with more than one of `--module`, `--modular` and
    /// `--schedule`, or a constant
    CompareModeArgs,
    /// `--schedule` with other than one module, or a flag it does not take
    ScheduleArgs,
}

/// con-leche: ConLeche/Driver/Cli.lean:262-303 Args
/// What the command line asked for: the binary's `Args`, field for field.  The
/// values only the scheduler reads (`--schedule`'s settings,
/// `--worker-stack-size`'s size) are kept as given, for it to read.
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
    /// the values after `--schedule` of every `--schedule[-OPT=VALUE]` flag,
    /// empty for the bare flag
    pub schedule: Vec<Vec<u32>>,
    /// some `--schedule` flag was given
    pub scheduled: bool,
    /// `--compare`
    pub compare: bool,
    /// `--trusted-search-path=DIR:DIR...`, the nonempty directories
    pub trusted_path: Vec<Vec<u32>>,
    /// `--worker-stack-size=SIZE`, a valid size, as given
    pub worker_stack: Option<Vec<u32>>,
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
        worker_stack: None,
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
    if a.worker_stack.is_some() && !a.scheduled {
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
    } else if cps_starts_with(s, &W_CONSTANT_EQ) {
        a.constants.push(str_copy_from(s, 11, Vec::new()));
    } else if cps_starts_with(s, &W_SEARCH_PATH_EQ) {
        a.search_path = push_dirs(a.search_path, s, 14);
    } else if cps_starts_with(s, &W_TRUSTED_SEARCH_PATH_EQ) {
        a.trusted_path = push_dirs(a.trusted_path, s, 22);
    } else if cps_starts_with(s, &W_SCHEDULE) {
        a.schedule.push(str_copy_from(s, 10, Vec::new()));
        a.scheduled = true;
    } else if cps_starts_with(s, &W_WORKER_STACK_SIZE_EQ) {
        let v = str_copy_from(s, 20, Vec::new());
        if size_positive(&v) {
            a.worker_stack = Some(v);
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
/// One argument, `argv[i]` (not `--`).
pub fn parse_one(a: Args, argv: &Vec<Vec<u32>>, i: usize) -> Args {
    let mut a = a;
    let s = &argv[i];
    if cps_beq(s, &W_VERIFIED) {
        a.verified = true;
    } else if cps_beq(s, &W_TRUSTED) {
        a.verified = false;
    } else if cps_beq(s, &W_PROGRESS) {
        a.progress = Pace::Every(1);
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
    } else if cps_beq(s, &W_JOBS) {
        a = with_bad(a, Bad::JobsBare);
    } else {
        a = parse_valued(a, s);
    }
    a
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
        a = parse_one(a, argv, i);
        i += 1;
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// The module names of the command line, parsed (`parseModName`); the first
/// that does not parse.
pub fn parse_mod_names(fs: &Vec<Vec<u32>>) -> Result<Vec<Name>, Vec<u32>> {
    let mut out: Vec<Name> = Vec::new();
    let mut i = 0usize;
    while i < fs.len() {
        match files::parse_mod_name(&fs[i]) {
            None => return Err(str_copy(&fs[i])),
            Some(n) => out.push(n),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Cli.lean:383-385 Args.rootConstants
/// The constants' names of the command line, parsed (`parseConstName`); the
/// first that does not parse.
pub fn parse_const_names(cs: &Vec<Vec<u32>>) -> Result<Vec<Name>, Vec<u32>> {
    let mut out: Vec<Name> = Vec::new();
    let mut i = 0usize;
    while i < cs.len() {
        match files::parse_const_name(&cs[i]) {
            None => return Err(str_copy(&cs[i])),
            Some(n) => out.push(n),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Compare.lean:82-84 CmpReq.solRoots
/// **A worker's lookup**: the trusted path first, then the search path; the
/// search path alone where no trusted path is given.
pub fn sol_roots(a: &Args) -> Roots {
    if a.trusted_path.len() == 0 {
        files::roots_of_path(push_files(Vec::new(), &a.search_path, 0))
    } else {
        Roots { path: push_files(Vec::new(), &a.trusted_path, 0), fallback: push_files(Vec::new(), &a.search_path, 0) }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:78-80 CmpReq.chalRoots
/// **The challenge's lookup**: the trusted path, never anything else; the
/// search path where no trusted path is given.
pub fn chal_roots(a: &Args) -> Roots {
    if a.trusted_path.len() == 0 {
        files::roots_of_path(push_files(Vec::new(), &a.search_path, 0))
    } else {
        files::roots_of_path(push_files(Vec::new(), &a.trusted_path, 0))
    }
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// `--check-graph` with a flag it does not take: `--olean`, `--module`, a
/// `--constant`, or `--trusted-search-path` without `--compare`.
pub fn check_graph_flags_bad(a: &Args) -> bool {
    if a.olean {
        return true;
    }
    if a.module {
        return true;
    }
    if a.constants.len() > 0 {
        return true;
    }
    if a.trusted_path.len() > 0 && !a.compare {
        return true;
    }
    false
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// No module name, or no lookup (neither `--search-path` nor
/// `--trusted-search-path`).
pub fn no_roots_or_path(a: &Args) -> bool {
    if a.files.len() == 0 {
        return true;
    }
    if a.search_path.len() > 0 {
        return false;
    }
    a.trusted_path.len() == 0
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// `--trusted-search-path` where it is not taken: without `--module`, or with
/// `--modular` or `--schedule`.
pub fn trusted_misplaced(a: &Args) -> bool {
    if a.trusted_path.len() == 0 {
        return false;
    }
    if !a.module {
        return true;
    }
    if a.modular {
        return true;
    }
    a.scheduled
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// `--compare` with a mode of its modular run: `--module`, `--modular` or
/// `--schedule`.
pub fn cmp_mode(a: &Args) -> bool {
    if a.module {
        return true;
    }
    if a.modular {
        return true;
    }
    a.scheduled
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// `--compare` with a mode it does not take with the others: a `--constant`,
/// or more than one of `--module`, `--modular` and `--schedule`.
pub fn cmp_mode_bad(a: &Args, cs: &Vec<Name>) -> bool {
    if cs.len() > 0 {
        return true;
    }
    if a.module && a.scheduled {
        return true;
    }
    if a.modular {
        if a.module {
            return true;
        }
        return a.scheduled;
    }
    false
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--check-graph`** (without `--compare`): con-leche's usage checks in its
/// order, then the graph check of the roots along the search path.
pub fn check_graph_args<I: CheckerIo>(io: &mut I, a: &Args) -> u8 {
    if check_graph_flags_bad(a) {
        io.usage(&Bad::CheckGraphFlags);
        return 3;
    }
    if no_roots_or_path(a) {
        io.usage(&Bad::CheckGraphArgs);
        return 3;
    }
    let roots = match parse_mod_names(&a.files) {
        Err(f) => {
            io.usage(&Bad::NotModuleName(f));
            return 3;
        }
        Ok(rs) => rs,
    };
    if a.compare {
        return check_graph_cmp_args(io, a, &roots);
    }
    let sp = files::roots_of_path(push_files(Vec::new(), &a.search_path, 0));
    graph::check_graph(io, &sp, &roots)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--check-graph --compare`**: two module names, two different ones; then
/// the compared graph check.
pub fn check_graph_cmp_args<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>) -> u8 {
    if roots.len() != 2 {
        io.usage(&Bad::CheckGraphCompareTwo);
        return 3;
    }
    if name::beq(&roots[0], &roots[1]) {
        io.usage(&Bad::CompareSameModule);
        return 3;
    }
    compare_module::check_graph_cmp(io, a, &roots[0], &roots[1])
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--olean --compare`**: two module names, two different ones; with
/// `--module`, `--modular` or `--schedule` one of them and no `--constant`;
/// then the compare worker, the one-process modular comparison, the
/// scheduler, or the compared run.
pub fn compare_olean_args<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, cs: &Vec<Name>) -> u8 {
    if roots.len() != 2 {
        io.usage(&Bad::CompareTwoModules);
        return 3;
    }
    if name::beq(&roots[0], &roots[1]) {
        io.usage(&Bad::CompareSameModule);
        return 3;
    }
    if cmp_mode(a) {
        if cmp_mode_bad(a, cs) {
            io.usage(&Bad::CompareModeArgs);
            return 3;
        }
        if a.module {
            return compare_module::check_cmp_module(io, a, &roots[0], &roots[1]);
        }
        if a.modular {
            let sp = sol_roots(a);
            let mut rs: Vec<Name> = Vec::new();
            rs.push(name::dup(&roots[0]));
            return modular::check_modular(io, a, &rs, &sp, Some(&roots[1]));
        }
        return io.run_schedule(a, &roots[0], Some(&roots[1]));
    }
    compare::compare_oleans(io, a, &roots[0], &roots[1], cs)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--olean`**: con-leche's usage checks in its order, then `--compare`,
/// `--schedule`, `--modular`, `--module`, or the check of the roots' closure.
pub fn olean_args<I: CheckerIo>(io: &mut I, a: &Args) -> u8 {
    if no_roots_or_path(a) {
        io.usage(&Bad::OleanArgs);
        return 3;
    }
    let roots = match parse_mod_names(&a.files) {
        Err(f) => {
            io.usage(&Bad::NotModuleName(f));
            return 3;
        }
        Ok(rs) => rs,
    };
    let cs = match parse_const_names(&a.constants) {
        Err(c) => {
            io.usage(&Bad::NotConstName(c));
            return 3;
        }
        Ok(cs) => cs,
    };
    if a.compare {
        return compare_olean_args(io, a, &roots, &cs);
    }
    if trusted_misplaced(a) {
        io.usage(&Bad::TrustedTakes);
        return 3;
    }
    if a.scheduled {
        return schedule_args(io, a, &roots, &cs);
    }
    if a.modular {
        return modular_args(io, a, &roots, &cs);
    }
    if a.module {
        return module_args(io, a, &roots, &cs);
    }
    let sp = files::roots_of_path(push_files(Vec::new(), &a.search_path, 0));
    check_main::check_oleans(io, a, &roots, &cs, &sp)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--olean --schedule`**: one module name, no `--constant`, neither
/// `--module` nor `--modular`; then the scheduler (`CheckerIo::run_schedule`).
pub fn schedule_args<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, cs: &Vec<Name>) -> u8 {
    if roots.len() != 1 || cs.len() > 0 || a.module || a.modular {
        io.usage(&Bad::ScheduleArgs);
        return 3;
    }
    io.run_schedule(a, &roots[0], None)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--olean --modular`**: one module name, no `--constant`, no `--module`;
/// then the one-process mode.
pub fn modular_args<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, cs: &Vec<Name>) -> u8 {
    if roots.len() != 1 || cs.len() > 0 || a.module {
        io.usage(&Bad::ModularArgs);
        return 3;
    }
    let sp = sol_roots(a);
    modular::check_modular(io, a, roots, &sp, None)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **`--olean --module`**: one module name, no `--constant`; then its worker.
pub fn module_args<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, cs: &Vec<Name>) -> u8 {
    if roots.len() != 1 || cs.len() > 0 {
        io.usage(&Bad::ModuleArgs);
        return 3;
    }
    let sp = sol_roots(a);
    worker::check_module(io, a, &sp, &roots[0], None)
}

/// con-leche: ConLeche/Driver/Cli.lean:409-608 runArgs
/// **The run of an argument list, to its exit code**: `--help`, the parse and
/// its usage error, then the request: `--check-graph`, `--olean` (whose
/// `--schedule` is the instance's scheduler), two lean4export files with
/// `--compare` (`compare_json`), or one, after the binary's usage checks of
/// that mode (`check_main`).
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
    if a.check_graph {
        return check_graph_args(io, &a);
    }
    if a.olean {
        return olean_args(io, &a);
    }
    if a.compare {
        return compare_json::compare_args(io, &a);
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
