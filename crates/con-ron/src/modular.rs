//! The modular modes (task #166): con-leche's `Driver/Graph.lean` `checkGraphG`,
//! `Driver/CompareModule.lean`, `Driver/Modular.lean`, the worker's driver
//! `Driver/Worker.lean` `checkModuleG`, and of the scheduler (`Driver/Schedule.lean`)
//! the part that starts nothing: `--schedule-commands`.
//!
//! ```text
//! con-ron [OPTIONS] --check-graph --search-path=DIRS [--] MODULE...
//! con-ron [OPTIONS] --check-graph --compare [--trusted-search-path=DIRS]
//!         --search-path=DIRS [--] CHALLENGE SOLUTION
//! con-ron [OPTIONS] --olean --schedule-commands [--schedule-order=graph]
//!         [--worker-stack-size=SIZE] --search-path=DIRS [--] MODULE
//! ```
//!
//! **The graph check** is the verified core's `modular::graph::graph_of` over the
//! files (`olean_fs::StdFs`): the roots' closure, its import graph acyclic, every
//! import resolved, the ranks one-to-one and decreasing along every edge.  Its
//! lines are upstream's: `graph: acyclic: N modules, E import edges` on stdout, or
//! `graph: <error>` on stderr, and the error's exit code.
//!
//! **`--schedule-commands`** prints the commands that check the closure, one per
//! line, shell-quoted as upstream's: the graph check of the root, then one
//! `--olean --module` run per module of the closure, in the scheduler's start
//! order.  Nothing is started.  The scheduler itself (`--schedule` without
//! `-commands`) is not ported: a usage error, exit 3.
//!
//! The calls of the verified core are marked `ConRon.Capstone: <premise>`.

use con_ron_core::arena::env as ienv;
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::monad;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::pins::intern_reserved_pins;
use con_ron_core::arena::store::PersTier;
use con_ron_core::frontend::modular::graph;
use con_ron_core::frontend::olean::files;
use con_ron_core::frontend::olean::spec;
use con_ron_core::frontend::olean::spec::{ImportRec, OleanPins};
use con_ron_core::frontend::pace::Pace;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::ron::hashmap::Dup;

use crate::compare;
use crate::compare::CmpRequest;
use crate::driver;
use crate::olean_fs;
use crate::render;

/// con-leche: none — the start of a graph walk: the reserved-name pins, the
/// reader's pins
/// The state a graph walk starts from: the reserved-name pins interned into a
/// fresh store (as every run's first step), the reader's known handles.
fn graph_start(pers: &PersTier, st: &mut AState) -> Result<OleanPins, u8> {
    // ConRon.Capstone: h1
    match intern_reserved_pins(pers, st) {
        Ok(()) => (),
        Err(e) => {
            eprintln!("con-ron: the reserved-name pins do not intern ({})", driver::message(&e));
            return Err(3);
        }
    }
    // ConRon.Capstone: hpk (`olean_pins`)
    match spec::olean_pins(pers, &mut st.store) {
        Ok(pk) => Ok(pk),
        Err(e) => {
            eprintln!("con-ron: graph: {}", driver::error_text(&e));
            Err(driver::exit_code(&e))
        }
    }
}

/// con-leche: none — `filterMap parseModName`, over handles
/// The command line's module names, as handles.
fn intern_all(pers: &PersTier, st: &mut AState, ns: &[Name]) -> Result<Vec<NIdx>, CheckError> {
    let mut v: Vec<NIdx> = Vec::with_capacity(ns.len());
    for n in ns {
        v.push(monad::intern_name(pers, st, n)?);
    }
    Ok(v)
}

/// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
/// The accept line of a graph: its modules and its import edges.
fn graph_accepted(c: &Vec<(NIdx, Vec<ImportRec>)>) -> u8 {
    let edges: usize = c.iter().map(|e| e.1.len()).sum();
    println!("con-ron: graph: acyclic: {} modules, {} import edges", c.len(), edges);
    0
}

/// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
/// A graph walk's failure: its line, and its exit code.
fn graph_failed(e: &CheckError) -> u8 {
    eprintln!("con-ron: graph: {}", driver::error_text(e));
    driver::exit_code(e)
}

/// con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk
/// **The challenge's closure through the trusted path alone**
/// (`--trusted-search-path`, its verdict only): where a module of it is not there,
/// why (invalid where the search path holds it, as in `--olean --compare`); none
/// where the walk succeeds or no trusted path is given.
pub fn chal_walk(pers: &PersTier, st: &mut AState, pk: &OleanPins, r: &CmpRequest, c: &NIdx) -> Option<CheckError> {
    if r.trusted.is_empty() {
        return None;
    }
    let cr = compare::chal_roots(r);
    // ConRon.Capstone: hchal (`graph_of` at the challenge's lookup)
    match graph::graph_of(&olean_fs::StdFs, pk, pers, &mut st.store, &cr, &vec![c.dup2()], &None) {
        Ok(_) => None,
        Err(e) => match compare::fallback_only(pers, st, r, c) {
            Some(why) => Some(core_types::invalid(render::cps(&why))),
            None => Some(e),
        },
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
/// **The graph check** (`--check-graph`): the roots' closure along the search
/// path, its graph checked (`graph_of`); the accept line or the error's.
pub fn check_graph(sp: &files::Roots, roots: &[Name]) -> u8 {
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    let pk = match graph_start(pers, &mut st) {
        Ok(pk) => pk,
        Err(code) => return code,
    };
    // ConRon.Capstone: hroots (`intern_name` of each root)
    let rs = match intern_all(pers, &mut st, roots) {
        Ok(v) => v,
        Err(e) => return graph_failed(&e),
    };
    // ConRon.Capstone: hgraph (`graph_of`, no import added)
    match graph::graph_of(&olean_fs::StdFs, &pk, pers, &mut st.store, sp, &rs, &None) {
        Ok(c) => graph_accepted(&c),
        Err(e) => graph_failed(&e),
    }
}

/// con-leche: ConLeche/Driver/CompareModule.lean:61-71 checkGraphCmpG
/// **The graph check of a compared run** (`--check-graph --compare`): with a
/// trusted path, the challenge's closure first, through the challenge's lookup
/// alone (`chal_walk`); then the graph of both closures through the solution's
/// lookup, the solution added to the challenge's header (`cmp_extra`).
pub fn check_graph_cmp(r: &CmpRequest) -> u8 {
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    let pk = match graph_start(pers, &mut st) {
        Ok(pk) => pk,
        Err(code) => return code,
    };
    // ConRon.Capstone: hroots
    let cs = match intern_all(pers, &mut st, &[name::dup(&r.challenge), name::dup(&r.solution)]) {
        Ok(v) => v,
        Err(e) => return graph_failed(&e),
    };
    let (c, s) = (cs[0].dup2(), cs[1].dup2());
    if let Some(e) = chal_walk(pers, &mut st, &pk, r, &c) {
        return graph_failed(&e);
    }
    let sr = compare::sol_roots(r);
    // ConRon.Capstone: hgraph (`graph_of`, the solution added to the challenge's header)
    match graph::graph_of(&olean_fs::StdFs, &pk, pers, &mut st.store, &sr, &vec![c.dup2()], &Some((c, s))) {
        Ok(c) => graph_accepted(&c),
        Err(e) => graph_failed(&e),
    }
}

// ---------------------------------------------------------------------------
// `--schedule-commands`: the commands that check a closure

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:38-44 spell
/// A module's name as the command line spells it, each component escaped.
pub fn spell(m: &Name) -> String {
    let mut comps: Vec<String> = Vec::new();
    let mut n = m;
    loop {
        match &n.0.kind {
            NameKind::Anonymous => break,
            NameKind::Str(p, s) => {
                comps.push(s.iter().filter_map(|c| char::from_u32(*c)).collect());
                n = p;
            }
            NameKind::Num(p, k) => {
                comps.push(k.to_string());
                n = p;
            }
        }
    }
    comps.reverse();
    comps.iter().map(|c| format!("«{}»", c)).collect::<Vec<_>>().join(".")
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:51-55 pathArgs
/// **The flags of a lookup**: `--search-path=D`, or with trusted directories
/// `T`, `--trusted-search-path=T --search-path=D` (each colon-separated).
pub fn path_args(trusted: &str, dirs: &str) -> Vec<String> {
    if trusted.is_empty() {
        vec![format!("--search-path={}", dirs)]
    } else {
        vec![format!("--trusted-search-path={}", trusted), format!("--search-path={}", dirs)]
    }
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:57-63 workerArgs
/// **A worker's arguments** at module `m`: `--olean --module`, `--jobs=T` where
/// `jobs` is `Some(T)`, the mode, the numeral bound, the lookup's flags `paths`
/// (`path_args`), then `--` and `spell m` last.
pub fn worker_args(mode_tag: &str, max_nat_size: &str, paths: &[String], jobs: Option<u64>, m: &Name) -> Vec<String> {
    let mut v: Vec<String> = vec!["--olean".to_string(), "--module".to_string()];
    if let Some(t) = jobs {
        v.push(format!("--jobs={}", t));
    }
    v.push(mode_tag.to_string());
    v.push(format!("--max-nat-size={}", max_nat_size));
    v.extend(paths.iter().cloned());
    v.push("--".to_string());
    v.push(spell(m));
    v
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:65-71 cmpWorkerArgs
/// **The compare worker's arguments** at challenge `c` and solution `s`:
/// `--olean --module --compare`, as `worker_args`, then `--`, `spell c` and
/// `spell s`.
pub fn cmp_worker_args(mode_tag: &str, max_nat_size: &str, paths: &[String], jobs: Option<u64>, c: &Name, s: &Name) -> Vec<String> {
    let mut v: Vec<String> = vec!["--olean".to_string(), "--module".to_string(), "--compare".to_string()];
    if let Some(t) = jobs {
        v.push(format!("--jobs={}", t));
    }
    v.push(mode_tag.to_string());
    v.push(format!("--max-nat-size={}", max_nat_size));
    v.extend(paths.iter().cloned());
    v.push("--".to_string());
    v.push(spell(c));
    v.push(spell(s));
    v
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:73-79 shellQuote
/// A word as a POSIX shell reads it back: as it is where it is not empty and
/// holds only letters, digits and `_-./=:,+@%`, else in single quotes, a `'` in
/// it as `'\''`.
pub fn shell_quote(s: &str) -> String {
    let plain = |c: char| c.is_ascii_alphanumeric() || "_-./=:,+@%".contains(c);
    if !s.is_empty() && s.chars().all(plain) {
        s.to_string()
    } else {
        format!("'{}'", s.split('\'').collect::<Vec<_>>().join("'\\''"))
    }
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:81-93 parseSize
/// A memory size in KiB: a number with a unit, `K`, `M`, `G` or `T` (KiB, MiB,
/// GiB, TiB; the lower-case letters too).  No unit is no size.
pub fn parse_size(v: &str) -> Option<u64> {
    let unit: u64 = match v.chars().last() {
        Some('K' | 'k') => 1,
        Some('M' | 'm') => 1024,
        Some('G' | 'g') => 1024 * 1024,
        Some('T' | 't') => 1024 * 1024 * 1024,
        _ => return None,
    };
    let n = to_nat(&v[..v.len() - 1])?;
    n.checked_mul(unit)
}

/// con-leche: none — Lean core's `String.toNat?`
/// A decimal numeral as Lean's `String.toNat?` reads it (`driver::is_nat`, `_`
/// separators allowed), as a `u64`.
fn to_nat(v: &str) -> Option<u64> {
    if !driver::is_nat(v) {
        return None;
    }
    v.chars().filter(|c| *c != '_').collect::<String>().parse::<u64>().ok()
}

/// con-leche: ConLeche/Driver/Schedule/Worker.lean:113-129 commandLines
/// **The commands that check a closure**, one line each, shell-quoted: the graph
/// check of `root` (`app --check-graph PATHS -- root`), then one worker per
/// module of `mods`, in the order given (`args` at each), each prefixed with
/// `LEAN_STACK_SIZE_KB=K ` where the workers' stack size `stack_kb` is given.
pub fn command_lines(app: &str, paths: &[String], root: &Name, cmp: &Option<Name>, mods: &[Name], args: &dyn Fn(&Name) -> Vec<String>, stack_kb: Option<u64>) -> Vec<String> {
    let line = |ws: &[String]| ws.iter().map(|w| shell_quote(w)).collect::<Vec<_>>().join(" ");
    let env = match stack_kb {
        Some(k) => format!("LEAN_STACK_SIZE_KB={} ", k),
        None => String::new(),
    };
    let mut first: Vec<String> = vec![app.to_string(), "--check-graph".to_string()];
    if cmp.is_some() {
        first.push("--compare".to_string());
    }
    first.extend(paths.iter().cloned());
    first.push("--".to_string());
    first.push(spell(root));
    if let Some(s) = cmp {
        first.push(spell(s));
    }
    let mut out: Vec<String> = vec![line(&first)];
    for m in mods {
        let mut ws: Vec<String> = vec![app.to_string()];
        ws.extend(args(m));
        out.push(format!("{}{}", env, line(&ws)));
    }
    out
}

/// con-leche: ConLeche/Driver/Schedule/Engine.lean:77-80 fnv1a
/// The 64-bit FNV-1a hash of a string's bytes: fixed across runs and machines.
pub fn fnv1a(s: &str) -> u64 {
    s.bytes().fold(14695981039346656037u64, |h, b| (h ^ b as u64).wrapping_mul(1099511628211))
}

/// con-leche: ConLeche/Driver/Schedule/Engine.lean:82-88 shuffle
/// The modules in a fixed pseudo-random order: by the hash of each one's
/// spelling, the spelling itself breaking ties.
pub fn shuffle(ms: Vec<Name>) -> Vec<Name> {
    let mut v: Vec<(u64, String, Name)> = ms.into_iter().map(|m| { let k = spell(&m); (fnv1a(&k), k, m) }).collect();
    v.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
    v.into_iter().map(|x| x.2).collect()
}

/// con-leche: ConLeche/Driver/Schedule/Run.lean:52-68 Opts
/// **The scheduler's settings** that `--schedule-commands` reads (the log, the
/// memory limit and the time limit are validated and ignored).
pub struct Opts {
    pub shuffled: bool,
    pub commands: bool,
}

/// con-leche: ConLeche/Driver/Schedule/Run.lean:70-95 Opts.parse
/// The settings, from the values of the `--schedule[-OPT=VALUE]` flags (`""` for
/// the bare flag, `-log=FILE`, `-memory=SIZE`, `-timeout=S`,
/// `-order=shuffled|graph`, `-commands`), or upstream's message.
pub fn opts_parse(vs: &[String]) -> Result<Opts, String> {
    let mut o = Opts { shuffled: true, commands: false };
    for v in vs {
        let num = |pre: &str, ok: bool, what: &str| -> Result<(), String> {
            if ok {
                Ok(())
            } else {
                Err(format!(
                    "--schedule{} takes {}, got \"{}\"",
                    &pre[..pre.len() - 1],
                    what,
                    &v[pre.len()..]
                ))
            }
        };
        if v.is_empty() || v.starts_with("-log=") {
        } else if let Some(x) = v.strip_prefix("-memory=") {
            num("-memory=", parse_size(x).is_some(), "a size with a unit, K, M, G or T (e.g. 512M, 40G)")?;
        } else if let Some(x) = v.strip_prefix("-timeout=") {
            num("-timeout=", to_nat(x).is_some(), "a number")?;
        } else if v == "-order=shuffled" {
            o.shuffled = true;
        } else if v == "-order=graph" {
            o.shuffled = false;
        } else if let Some(x) = v.strip_prefix("-order=") {
            return Err(format!("--schedule-order takes shuffled or graph, got \"{}\"", x));
        } else if v == "-commands" {
            o.commands = true;
        } else {
            return Err(format!("unknown option --schedule{}", v));
        }
    }
    Ok(o)
}

/// con-leche: ConLeche/Driver/Dispatch.lean:26-61 Req
/// **A `--schedule` request**: the lookup (as the command line gave it), the
/// root, the solution of a compared run, the `--schedule` values, and what the
/// printed workers are run with.
pub struct ScheduleReq<'a> {
    pub trusted: &'a [String],
    pub path: &'a [String],
    pub root: Name,
    pub cmp: Option<Name>,
    pub opts: &'a [String],
    pub mode_tag: &'a str,
    pub max_nat_size: String,
    pub pace: &'a Pace,
    pub jobs: Option<u64>,
    pub stack_kb: Option<u64>,
}

/// con-leche: ConLeche/Driver/Schedule.lean:56-111 scheduleG
/// con-leche: ConLeche/Driver/Schedule/Run.lean:637-647 printCommands
/// **`--schedule[-OPT=V]`**: the settings read; without `--schedule-commands`
/// the scheduler, which con-ron does not run (a usage error, exit 3); with it the
/// root's closure by the graph check (through the solution's lookup at a compared
/// run, then the challenge's closure through the trusted path alone), and the
/// commands that check it on stdout, the modules in the start order.
pub fn schedule(q: &ScheduleReq) -> u8 {
    let beat_ok = !matches!(q.pace, Pace::Percent(_));
    if !beat_ok {
        eprintln!("con-ron: --schedule takes --progress=N (milliseconds) or --progress=Ss, not a percentage");
        return 3;
    }
    let o = match opts_parse(q.opts) {
        Ok(o) => o,
        Err(msg) => {
            eprintln!("con-ron: {}", msg);
            return 3;
        }
    };
    if !o.commands {
        let mode = if q.cmp.is_some() { "--olean --schedule --compare" } else { "--olean --schedule" };
        eprintln!("con-ron: {} is not supported by con-ron yet", mode);
        eprintln!("Try 'con-ron --help' for more information.");
        return 3;
    }
    let cps_all = |v: &[String]| -> Vec<Vec<u32>> { v.iter().map(|d| render::cps(d)).collect() };
    let r = CmpRequest {
        challenge: name::dup(&q.root),
        solution: match &q.cmp {
            Some(s) => name::dup(s),
            None => name::dup(&q.root),
        },
        trusted: cps_all(q.trusted),
        path: cps_all(q.path),
        constants: Vec::new(),
    };
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    let pk = match graph_start(pers, &mut st) {
        Ok(pk) => pk,
        Err(code) => return code,
    };
    let root = match monad::intern_name(pers, &mut st, &q.root) {
        Ok(h) => h,
        Err(e) => return graph_failed(&e),
    };
    let cmp: Option<(NIdx, NIdx)> = match &q.cmp {
        None => None,
        Some(s) => match monad::intern_name(pers, &mut st, s) {
            Ok(h) => Some((root.dup2(), h)),
            Err(e) => return graph_failed(&e),
        },
    };
    let sr = compare::sol_roots(&r);
    // ConRon.Capstone: hgraph (`graph_of` through the solution's lookup)
    let c = match graph::graph_of(&olean_fs::StdFs, &pk, pers, &mut st.store, &sr, &vec![root.dup2()], &cmp) {
        Ok(c) => c,
        Err(e) => return graph_failed(&e),
    };
    if q.cmp.is_some() {
        if let Some(e) = chal_walk(pers, &mut st, &pk, &r, &root) {
            return graph_failed(&e);
        }
    }
    let mut mods: Vec<Name> = Vec::with_capacity(c.len());
    for e in &c {
        match ienv::read_name(pers, &st.store, &e.0) {
            Ok(n) => mods.push(n),
            Err(e) => return graph_failed(&e),
        }
    }
    let dirs = q.path.join(":");
    let tdirs = q.trusted.join(":");
    let paths: Vec<String> = if q.cmp.is_some() {
        vec![format!("--trusted-search-path={}", tdirs), format!("--search-path={}", dirs)]
    } else {
        path_args("", &dirs)
    };
    let root_c = render::name_str(&q.root);
    let args = |m: &Name| -> Vec<String> {
        match &q.cmp {
            Some(s) if render::name_str(m) == root_c => cmp_worker_args(q.mode_tag, &q.max_nat_size, &paths, q.jobs, &q.root, s),
            _ => worker_args(q.mode_tag, &q.max_nat_size, &paths, q.jobs, m),
        }
    };
    let app = match std::env::current_exe() {
        Ok(p) => p.to_string_lossy().into_owned(),
        Err(e) => {
            eprintln!("con-ron: cannot find the binary's own path: {}", e);
            return 3;
        }
    };
    let order = if o.shuffled { shuffle(mods) } else { mods };
    for l in command_lines(&app, &paths, &q.root, &q.cmp, &order, &args, q.stack_kb) {
        println!("{}", l);
    }
    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::frontend::olean::files::parse_mod_name;

    #[test]
    fn quoting() {
        assert_eq!(shell_quote("--search-path=/a/b:c"), "--search-path=/a/b:c");
        assert_eq!(shell_quote(""), "''");
        assert_eq!(shell_quote("«A».«B»"), "'«A».«B»'");
        assert_eq!(shell_quote("it's"), "'it'\\''s'");
    }

    #[test]
    fn spelling() {
        let n = parse_mod_name(&render::cps("Init.Data.«Nat»")).unwrap();
        assert_eq!(spell(&n), "«Init».«Data».«Nat»");
    }

    #[test]
    fn sizes_and_opts() {
        assert_eq!(parse_size("8G"), Some(8 * 1024 * 1024));
        assert_eq!(parse_size("6000"), None);
        assert!(opts_parse(&["-frobnicate".to_string()]).is_err());
        assert!(opts_parse(&["-commands".to_string(), "-order=graph".to_string()]).map(|o| o.commands && !o.shuffled).unwrap());
        assert_eq!(fnv1a(""), 14695981039346656037);
    }
}
