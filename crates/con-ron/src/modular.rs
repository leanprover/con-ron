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
use con_ron_core::frontend::modular::compare_module;
use con_ron_core::frontend::modular::graph;
use con_ron_core::frontend::modular::reach;
use con_ron_core::frontend::modular::worker;
use con_ron_core::frontend::modular::worker::WorkerRead;
use con_ron_core::frontend::olean::index;
use con_ron_core::frontend::olean::progress;
use con_ron_core::frontend::compare as fcompare;
use con_ron_core::frontend::olean::records::{value_cache_empty, ValueCache};
use con_ron_core::frontend::pace::{pace_dup, pace_on};
use con_ron_core::arena::checker;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::ron::hashmap2::HashMap2;
use std::time::Instant;
use crate::compare::CompareOpts;
use crate::driver::{Heartbeat, Silent};
use con_ron_core::frontend::olean::files;
use con_ron_core::frontend::olean::spec;
use con_ron_core::frontend::olean::spec::{ImportRec, OleanPins};
use con_ron_core::frontend::pace::Pace;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;
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
    // ConRon.Capstone: hchal (`chal_walk`, the graph at the challenge's lookup)
    match compare_module::chal_walk(&olean_fs::StdFs, pk, pers, &mut st.store, &cr, c) {
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

// ---------------------------------------------------------------------------
// `--module` and `--modular`: the worker

/// con-leche: ConLeche/Driver/Worker.lean:345-355 tagKind
/// A stored constant's kind, by its tag (`CKindF.tag`), for the messages.
pub fn tag_kind(t: u64) -> &'static str {
    match t {
        0 => "axiom",
        1 => "definition",
        2 => "theorem",
        3 => "opaque constant",
        4 => "quotient constant",
        5 => "inductive type",
        6 => "constructor",
        7 => "recursor",
        _ => "constant",
    }
}

/// con-leche: none — a code-point message as a Rust `String`
fn text(s: &[u32]) -> String {
    s.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: ConLeche/Driver/Worker.lean:357-368 copyLine
/// **A copy, for the report** (`--compare`'s worker): a hole and the kind of what
/// justifies it, or a constant the challenge restates, with the module it is read
/// from.
fn copy_line(pers: &PersTier, st: &mut AState, w: &WorkerRead, owner: &HashMap2<NIdx, u64>, d: &IDeclaration) -> Result<String, CheckError> {
    let n = match fcompare::rec_key(d) {
        Some(n) => n,
        None => return Ok(String::new()),
    };
    let nt = driver::name_of(pers, &st.store, &n);
    let h = match owner.get(&n) {
        Some(k) => match w.reach.homes.get(*k as usize) {
            Some(h) => driver::name_of(pers, &st.store, h),
            None => "[anonymous]".to_string(),
        },
        None => "[anonymous]".to_string(),
    };
    let tag = match w.reads.index.first.get(&n) {
        Some(c) => match index::name_index_at(&w.reads.index, c) {
            Some(p) => p.tag,
            None => 8,
        },
        None => 8,
    };
    let kind = tag_kind(tag);
    let rk = text(&fcompare::rec_kind(d));
    let uses = worker::own_uses_of(&w.home.constants);
    if worker::is_hole_rec(&uses, pers, st, d)? {
        let label = match d {
            IDeclaration::AxiomDecl(_) => "axiom".to_string(),
            _ => format!("{} := sorry", rk),
        };
        Ok(format!("hole {} ({}) justified by {}'s {}", nt, label, h, kind))
    } else {
        Ok(format!("{} {}: {}'s {}", rk, nt, h, kind))
    }
}

/// con-leche: ConLeche/Driver/Worker.lean:370-412 checkModuleG
/// **The worker at module `m`**, from fresh start values: phases 1-4
/// (`worker::worker_read`, every read through `sp`), then the own records' jobs
/// over the index of the context and the own records, and the verdict.  `alone`:
/// the process's one check (`--module`); else one module of `--modular`, whose
/// lines name it.  `cmp`: the solution a compared challenge loads whole (`import
/// all S` added to its header); its accept then lists the copies.
pub fn check_module(o: &CompareOpts, sp: &files::Roots, m_name: &Name, cmp: Option<&Name>, alone: bool) -> u8 {
    let t0 = Instant::now();
    let m_text = render::name_str(m_name);
    let who = if alone { String::new() } else { format!("module {}: ", m_text) };
    let fail = |e: &CheckError| -> u8 {
        eprintln!("con-ron: module {}: {} ({})", m_text, driver::error_text(e), o.mode_tag);
        driver::exit_code(e)
    };
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    // ConRon.Capstone: h1
    if let Err(e) = intern_reserved_pins(pers, &mut st) {
        return fail(&e);
    }
    let mut hb = Heartbeat::new(pace_dup(o.progress), t0);
    if alone {
        hb.read_starts(&format!("module {}", m_text));
    }
    // ConRon.Capstone: hroots (`intern_name` of M; under --compare also of S)
    let m = match monad::intern_name(pers, &mut st, m_name) {
        Ok(h) => h,
        Err(e) => return fail(&e),
    };
    let x: Vec<ImportRec> = match cmp {
        None => Vec::new(),
        Some(s) => match monad::intern_name(pers, &mut st, s) {
            Ok(h) => vec![graph::solution_import(&h)],
            Err(e) => return fail(&e),
        },
    };
    // ConRon.Capstone: hpins (`decode_embedded`; `--pins`/`--no-pins` outside the theorems)
    let pins = match driver::pins_for_run(o.pins, o.no_pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return 3;
        }
    };
    // ConRon.Capstone: h5 (before the worker: the pin ground reads the interned variants)
    let ipins = match checker::intern_all_pins(pers, &mut st, &pins, o.max_nat_size) {
        Ok(p) => p,
        Err(e) => return fail(&e),
    };
    // ConRon.Capstone: hwork (phases 1-4, one call)
    let w: WorkerRead = match worker::worker_read(&olean_fs::StdFs, pers, &mut st, sp, &ipins, &m, &x) {
        Ok(w) => w,
        Err((e, _)) => return fail(&e),
    };
    if pace_on(o.progress) {
        let say = |line: String| {
            let ms = t0.elapsed().as_millis() as u64;
            let t = progress::read_line_text(&render::cps(&line), ms, &olean_fs::resident_set());
            eprintln!("con-ron: {}", text(&t));
        };
        say(format!("the home of {}: {} constants, views checked", m_text, w.home.constants.len()));
        say(format!(
            "loads {} modules, {} names; {} names held twice, merged",
            w.reads.loads.order.len(),
            w.reads.index.first.len(),
            w.reads.clashes.len()
        ));
        let mut homes: HashMap2<NIdx, bool> = HashMap2::new();
        for h in &w.reach.homes {
            homes.insert(h.dup2(), true);
        }
        say(format!(
            "reach: {} records from {} modules, {} completed, {} flags inferred",
            w.reach.ctx.len(),
            homes.len(),
            w.reach.completed.len(),
            w.reach.inferred
        ));
    }
    if !w.hoisted.is_empty() {
        let names: Vec<String> = w.hoisted.iter().map(|n| driver::name_of(pers, &st.store, n)).collect();
        eprintln!(
            "con-ron: {}{} declarations hoisted ahead of the pinned Nat operations they ground: {}",
            who,
            w.hoisted.len(),
            names.join(", ")
        );
    }
    // the jobs' records: the context, then the own records
    let ds: Vec<IDeclaration> = worker::worker_decls(&w);
    let start = w.start as usize;
    let job = |tier: &PersTier, ws: &mut AState, c: &mut ValueCache, k: u64| {
        driver::olean_job(tier, ws, c, &o.mode, &ipins, &ds, &w.pins, &w.values, sp, None, k)
    };
    // ConRon.Capstone: h6, h7, hinfer, h8 (the index over ctx ++ own, the freeze, the
    // reach's inferred flags on the frozen tier, the pool over the own jobs from `start`)
    let infer = |tier: &PersTier, ws: &mut AState| reach::infer_flags(tier, ws, &w.reach.ctx, &w.reach.pending);
    let verdict = if pace_on(o.progress) && alone {
        driver::check_decls_driver_from(pers, &mut st, &ds, start, o.jobs, &mut hb, infer, value_cache_empty, job)
    } else {
        driver::check_decls_driver_from(pers, &mut st, &ds, start, o.jobs, &mut Silent, infer, value_cache_empty, job)
    };
    match verdict {
        Err((e, i)) => driver::verdict_failure(pers, &st.store, &ds, &e, i, o.mode_tag, t0, &who),
        Ok(_) => {
            println!("con-ron: {}accepted {} declarations ({})", who, w.own.len(), o.mode_tag);
            if !x.is_empty() {
                let cs = match worker::copy_recs(pers, &mut st, &x, &w.reads.index, &w.emitted) {
                    Ok(cs) => cs,
                    Err(e) => return fail(&e),
                };
                let owner = match reach::owner_map(pers, &mut st, &w.reach.ctx) {
                    Ok(ow) => ow,
                    Err(e) => return fail(&e),
                };
                let mut lines: Vec<String> = Vec::with_capacity(cs.len() + 1);
                lines.push(format!("con-ron: {}{} declarations of {} are the loaded constants of their names", who, cs.len(), m_text));
                for d in &cs {
                    match copy_line(pers, &mut st, &w, &owner, d) {
                        Ok(l) => lines.push(format!("con-ron: {}", l)),
                        Err(e) => return fail(&e),
                    }
                }
                println!("{}", lines.join("\n"));
            }
            0
        }
    }
}

/// con-leche: ConLeche/Driver/CompareModule.lean:49-59 checkCmpModuleG
/// con-leche: ConLeche/Driver/Dispatch.lean:63-87 runReq
/// **`--olean --module [--compare]`**: the worker of `r.challenge` alone, every
/// module read through the solution's lookup (the trusted path, then the search
/// path); with `cmp`, the challenge's closure first walked through the trusted
/// path alone (`chal_walk`), then the compare worker (`import all` of
/// `r.solution` added to the header).
pub fn module_main(o: &CompareOpts, r: &CmpRequest, cmp: bool) -> u8 {
    if cmp {
        let mut st = AState::empty();
        let pers: &PersTier = &PersTier::empty();
        let pk = match graph_start(pers, &mut st) {
            Ok(pk) => pk,
            Err(code) => return code,
        };
        let c = match monad::intern_name(pers, &mut st, &r.challenge) {
            Ok(h) => h,
            Err(e) => return graph_failed(&e),
        };
        if let Some(e) = chal_walk(pers, &mut st, &pk, r, &c) {
            return graph_failed(&e);
        }
    }
    let sr = compare::sol_roots(r);
    check_module(o, &sr, &r.challenge, if cmp { Some(&r.solution) } else { None }, true)
}

/// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
/// con-leche: ConLeche/Driver/Modular.lean:64-72 stepCode
/// **The one-process mode** (`--olean --modular [--compare]`): the root's closure
/// by the graph check (through the solution's lookup, the solution added to the
/// challenge's header at a compared run, whose challenge closure is then walked
/// through the trusted path alone), then every module of it, each its worker from
/// fresh start values (`check_module`), the challenge's the compare worker; the
/// modules on up to `--jobs` threads (fewer where no more can be started), each
/// worker on one; then the run's verdict:
/// exit 0 exactly when every module's is, else the code of the first module, in
/// the graph's order, that is not.
pub fn modular_main(o: &CompareOpts, r: &CmpRequest, cmp: bool) -> u8 {
    let sr = compare::sol_roots(r);
    let mods: Vec<Name> = {
        let mut st = AState::empty();
        let pers: &PersTier = &PersTier::empty();
        let pk = match graph_start(pers, &mut st) {
            Ok(pk) => pk,
            Err(code) => return code,
        };
        let root = match monad::intern_name(pers, &mut st, &r.challenge) {
            Ok(h) => h,
            Err(e) => return graph_failed(&e),
        };
        let extra: Option<(NIdx, NIdx)> = if cmp {
            match monad::intern_name(pers, &mut st, &r.solution) {
                Ok(s) => Some((root.dup2(), s)),
                Err(e) => return graph_failed(&e),
            }
        } else {
            None
        };
        // ConRon.Capstone: hgraph (`graph_of` through the solution's lookup)
        let c = match graph::graph_of(&olean_fs::StdFs, &pk, pers, &mut st.store, &sr, &vec![root.dup2()], &extra) {
            Ok(c) => c,
            Err(e) => return graph_failed(&e),
        };
        if cmp {
            if let Some(e) = chal_walk(pers, &mut st, &pk, r, &root) {
                eprintln!("con-ron: graph: {} ({})", driver::error_text(&e), o.mode_tag);
                return driver::exit_code(&e);
            }
        }
        let mut v: Vec<Name> = Vec::with_capacity(c.len());
        for e in &c {
            match ienv::read_name(pers, &st.store, &e.0) {
                Ok(n) => v.push(n),
                Err(e) => return graph_failed(&e),
            }
        }
        v
    };
    if pace_on(o.progress) {
        eprintln!("con-ron: modular: graph: acyclic, {} modules", mods.len());
    }
    let n = mods.len();
    let threads = driver::workers_for(o.jobs, n);
    let inner = CompareOpts {
        mode: match o.mode { CheckMode::Verified => CheckMode::Verified, CheckMode::Trusted => CheckMode::Trusted },
        mode_tag: o.mode_tag,
        max_nat_size: o.max_nat_size,
        pins: o.pins,
        no_pins: o.no_pins,
        jobs: 1,
        progress: &Pace::Off,
    };
    let root_text = render::name_str(&r.challenge);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let codes: Vec<std::sync::Mutex<Option<u8>>> = (0..n).map(|_| std::sync::Mutex::new(None)).collect();
    let step = |k: usize| -> u8 {
        let m = &mods[k];
        let is_chal = cmp && render::name_str(m) == root_text;
        check_module(&inner, &sr, m, if is_chal { Some(&r.solution) } else { None }, false)
    };
    let spawned = std::thread::scope(|sc| -> Result<(), String> {
        let mut hs = Vec::with_capacity(threads);
        for _ in 0..threads {
            let h = std::thread::Builder::new().stack_size(driver::STACK_BYTES).spawn_scoped(sc, || loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                if k >= n {
                    break;
                }
                let c = step(k);
                if let Ok(mut g) = codes[k].lock() {
                    *g = Some(c);
                }
            });
            // a thread that cannot be started (the 1 GiB stacks against `ulimit -v`)
            // leaves the modules to the threads that did start
            match h {
                Ok(h) => hs.push(h),
                Err(e) => {
                    if hs.is_empty() {
                        return Err(e.to_string());
                    }
                    break;
                }
            }
        }
        for h in hs {
            if h.join().is_err() {
                return Err("a module's thread died".to_string());
            }
        }
        Ok(())
    });
    if let Err(e) = spawned {
        eprintln!("con-ron: modular: {}", e);
        return 3;
    }
    let mut failed: Vec<(usize, u8)> = Vec::new();
    for (k, c) in codes.iter().enumerate() {
        let c = match c.lock() {
            Ok(g) => g.unwrap_or(3),
            Err(_) => 3,
        };
        if c != 0 {
            failed.push((k, c));
        }
    }
    if pace_on(o.progress) {
        eprintln!("con-ron: modular: done");
    }
    match failed.first() {
        None => {
            println!("con-ron: accepted {} modules ({})", n, o.mode_tag);
            0
        }
        Some((k, c)) => {
            eprintln!(
                "con-ron: {} of {} modules not accepted; the first in the graph's order: {} ({})",
                failed.len(),
                n,
                render::name_str(&mods[*k]),
                o.mode_tag
            );
            *c
        }
    }
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
