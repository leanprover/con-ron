//! `olean-compare` — the `.olean` reader against lean4export (task #142), upstream's
//! `OleanCompare.lean` over the arena.
//!
//! ```text
//! olean-compare [--constant=NAME]... EXPORT.ndjson SEARCHPATH MODULE...
//! olean-compare --views SEARCHPATH MODULE...
//! olean-compare --home SEARCHPATH MODULE...
//! olean-compare --reads [--jobs=N] [--loads] [--levels] SEARCHPATH MODULE
//! olean-compare --reach [--jobs=N] [--list] SEARCHPATH MODULE
//! ```
//!
//! Parses a lean4export stream of `MODULE...` and the same modules' import closure
//! into ONE store, and compares the two record arrays as maps from a record's first
//! declared name.  Over one hash-consed store a handle IS the term, so the comparison
//! needs no walk of a term, where upstream's needs `Expr.beq`'s memo.  Two orders
//! lean4export takes from hash-map iteration are normalised: the record order (hence
//! the map) and the order of the recursors inside a block.
//!
//! `--views` reads every module of the closure at its home (`read_all_views`) and
//! compares each view with `read_view`'s; exit 0, or the first failure's exit code.
//! `--home` is each module's home read alone (`worker::home_of`); `--reads` a
//! worker's reads at one module (`index::worker_reads`; with `--levels` only the
//! header fixpoint and the public-import closures); `--reach` a worker's context at
//! one module (`reach::reach` from its records' reads and its constants' uses).  Each
//! prints one summary line, or the failure with its exit code.  The reads are
//! sequential, so `--jobs` has no effect.
//!
//! A development tool, outside the theorems, like `crate::driver`.

use std::collections::HashMap;
use std::process::ExitCode;

use con_ron::driver;
use con_ron::olean_fs::StdFs;

use con_ron_core::arena::canon;
use con_ron_core::arena::env::{IConstantInfo, IDeclaration};
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::PersTier;
use con_ron_core::frontend::checker_io::FileChunks;
use con_ron_core::frontend::export_c;
use con_ron_core::arena::{checker, install};
use con_ron_core::frontend::modular::{reach, worker};
use con_ron_core::frontend::olean::{closure, emit, files, group, index, lazy, levels, module, records, spec, view};
use con_ron_core::frontend::olean::view::OLeanLevel;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env as cenv;

/// con-leche: ConLeche/Driver/CheckMain.lean:55-62 Input
/// What the command line asked for, the names parsed: a usage error is reported
/// before anything is read.
struct OleanRequest {
    search_path: files::Roots,
    roots: Vec<con_ron_core::kernel::name::Name>,
    constants: Vec<con_ron_core::kernel::name::Name>,
}

/// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
impl OleanRequest {
    /// con-leche: ConLeche/Driver/Cli.lean:387-606 runArgs
    /// The names of the command line, or the usage error.
    fn new(search_path: &[String], modules: &[String], constants: &[String]) -> Result<OleanRequest, String> {
        let mut roots = Vec::new();
        for m in modules {
            match files::parse_mod_name(&con_ron::render::cps(m)) {
                Some(n) => roots.push(n),
                None => return Err(format!("not a module name: {}", con_ron::render::display_str(m))),
            }
        }
        let mut cs = Vec::new();
        for c in constants {
            match files::parse_const_name(&con_ron::render::cps(c)) {
                Some(n) => cs.push(n),
                None => return Err(format!("not a constant's name: {}", con_ron::render::display_str(c))),
            }
        }
        Ok(OleanRequest {
            search_path: files::roots_of_path(search_path.iter().map(|d| con_ron::render::cps(d)).collect()),
            roots,
            constants: cs,
        })
    }

    /// con-leche: none — `a.rootConstants`, and `filterMap parseModName`, over handles
    /// The names, as handles.
    fn intern(&self, pers: &PersTier, st: &mut AState) -> Result<(Vec<NIdx>, Option<Vec<NIdx>>), CheckError> {
        let mut roots: Vec<NIdx> = Vec::with_capacity(self.roots.len());
        for n in &self.roots {
            roots.push(con_ron_core::arena::monad::intern_name(pers, st, n)?);
        }
        if self.constants.is_empty() {
            return Ok((roots, None));
        }
        let mut cs: Vec<NIdx> = Vec::with_capacity(self.constants.len());
        for n in &self.constants {
            cs.push(con_ron_core::arena::monad::intern_name(pers, st, n)?);
        }
        Ok((roots, Some(cs)))
    }
}

/// con-leche: OleanCompare.lean:57-64 normalize
/// The first declared name of a record, as text; the recursors of a block sorted by
/// name, as a list of positions.
fn rec_order(pers: &PersTier, st: &AState, block: &[IConstantInfo]) -> Vec<usize> {
    let is_rec = |c: &IConstantInfo| matches!(c, IConstantInfo::RecInfo(..));
    let mut rest: Vec<usize> = (0..block.len()).filter(|i| !is_rec(&block[*i])).collect();
    let mut recs: Vec<usize> = (0..block.len()).filter(|i| is_rec(&block[*i])).collect();
    recs.sort_by_key(|i| driver::name_of(pers, &st.store, &con_ron_core::arena::env::i_constant_info_name(&block[*i])));
    rest.append(&mut recs);
    rest
}

/// con-leche: OleanCompare.lean:98-105 declEq
/// Two records, field by field, by handle.
fn decl_eq(pers: &PersTier, st: &AState, a: &IDeclaration, b: &IDeclaration) -> bool {
    use con_ron_core::ron::hashmap::Eq2;
    use IDeclaration::*;
    match (a, b) {
        (AxiomDecl(v), AxiomDecl(w)) => canon::i_constant_val_beq(v, w),
        (DefnDecl(v, e, h), DefnDecl(w, e2, h2)) => {
            canon::i_constant_val_beq(v, w) && e.eq2(e2) && cenv::reducibility_hint_beq(h, h2)
        }
        (ThmDecl(v, e), ThmDecl(w, e2)) => canon::i_constant_val_beq(v, w) && e.eq2(e2),
        (OpaqueDecl(v, e), OpaqueDecl(w, e2)) => canon::i_constant_val_beq(v, w) && e.eq2(e2),
        (IndDecl(x, n), IndDecl(y, m)) => {
            let ox = rec_order(pers, st, x);
            let oy = rec_order(pers, st, y);
            n == m
                && x.len() == y.len()
                && ox.iter().zip(oy.iter()).all(|(i, j)| canon::i_constant_info_beq(&x[*i], &y[*j]))
        }
        (QuotDecl(k, v), QuotDecl(k2, w)) => {
            std::mem::discriminant(k) == std::mem::discriminant(k2) && canon::i_constant_val_beq(v, w)
        }
        _ => false,
    }
}

/// con-leche: OleanCompare.lean:134-137 toMap
/// The records by first name, and how many shared one.
fn to_map(ds: &[IDeclaration]) -> (HashMap<u32, usize>, usize) {
    let mut m: HashMap<u32, usize> = HashMap::new();
    let mut dup = 0usize;
    for (i, d) in ds.iter().enumerate() {
        let names: Vec<NIdx> = con_ron_core::arena::env::i_declaration_names(d);
        let k = match names.first() {
            Some(n) => n.word,
            None => u32::MAX,
        };
        if m.contains_key(&k) {
            dup += 1;
        } else {
            m.insert(k, i);
        }
    }
    (m, dup)
}

/// con-leche: OleanCompare.lean:139-142 viewsEq
/// A view's constants by the checker's equality.
fn views_eq(a: &spec::ModDecoded, b: &spec::ModDecoded) -> bool {
    a.is_module == b.is_module
        && spec::imports_beq(&a.imports, &b.imports)
        && a.constants.len() == b.constants.len()
        && a.constants.iter().zip(b.constants.iter()).all(|(x, y)| module::entry_same(x, y))
}

/// con-leche: none — the rendering of a failure's exit, `driver::exit_code` as a process code
fn fail_with(e: &CheckError) -> u8 {
    eprintln!("{}", driver::message(e));
    driver::exit_code(e)
}

/// con-leche: none — `tests/ConLecheTests/OleanTests.lean`'s `agree`, at a module's
/// home: every read of a part of a view is its part, so that `--views` runs the
/// reads no checking path takes.
fn agree(pk: &spec::OleanPins, pers: &PersTier, st: &mut AState, f: &view::ModFiles, d: &spec::ModDecoded, level: &OLeanLevel) -> bool {
    use con_ron_core::ron::hashmap::Eq2;
    let l = match view::read_name_positions(pk, pers, &mut st.store, f, level) {
        Ok(l) => l,
        Err(_) => return false,
    };
    if !spec::imports_beq(&l.header.imports, &d.imports) || l.consts.len() != d.constants.len() {
        return false;
    }
    for (x, y) in l.consts.iter().zip(d.constants.iter()) {
        if !x.name.eq2(&y.name) {
            return false;
        }
        match view::read_entry(pk, pers, &mut st.store, f, level, x.loc) {
            Ok(en) if module::entry_same(&en, y) => {}
            _ => return false,
        }
    }
    let locs: Vec<u64> = l.consts.iter().map(|p| p.loc).collect();
    let ss = match view::read_stmts(pk, pers, &mut st.store, f, level, &locs) {
        Ok(ss) => ss,
        Err(_) => return false,
    };
    ss.len() == d.constants.len()
        && ss.iter().zip(d.constants.iter()).all(|(s, c)| {
            let w = spec::c_entry_stmt(c);
            s.name.eq2(&w.name) && s.ty.eq2(&w.ty) && module::nidx_list_eq(&s.level_params, &w.level_params)
        })
}

/// con-leche: OleanCompare.lean:145-162 runViews
/// `--views`: every module of the closure.
fn run_views(sp: &[String], mods: &[String]) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let req = match OleanRequest::new(sp, mods, &[]) {
        Ok(r) => r,
        Err(m) => {
            eprintln!("{}", m);
            return 3;
        }
    };
    let (roots, _) = match req.intern(pers, &mut st) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let order = match closure::closure_order(&StdFs, &pk, pers, &mut st.store, &req.search_path, &roots) {
        Ok(o) => o,
        Err(e) => return fail_with(&e),
    };
    for m in &order {
        let (v, _) = match files::read_all_views(&StdFs, &pk, pers, &mut st.store, &req.search_path, m) {
            Ok(x) => x,
            Err(e) => return fail_with(&e),
        };
        for level in [OLeanLevel::Exported, OLeanLevel::Server, OLeanLevel::Private] {
            let d = match files::read_view(&StdFs, &pk, pers, &mut st.store, &req.search_path, m, &level) {
                Ok(d) => d,
                Err(e) => return fail_with(&e),
            };
            let shown = String::from_utf8_lossy(&view::level_repr(&level).iter().map(|c| *c as u8).collect::<Vec<u8>>()).to_string();
            if !views_eq(&d, view::all_views_at(&v, &level)) {
                eprintln!(
                    "module {}: the {} view differs from the home's",
                    driver::name_of(pers, &st.store, m),
                    shown
                );
                return 3;
            }
            match files::read_files(&StdFs, pers, &st.store, &req.search_path, m, &OLeanLevel::Private) {
                Err(e) => return fail_with(&e),
                Ok(f) => {
                    if !agree(&pk, pers, &mut st, &f, &d, &level) {
                        eprintln!("module {}: the {} reads of a part differ from the view", driver::name_of(pers, &st.store, m), shown);
                        return 3;
                    }
                    // an importer holding the files up to the view reads the home's
                    let up = view::mod_files_up_to(f, &level);
                    match view::parse_view(&pk, pers, &mut st.store, &up, &level) {
                        Ok(d2) if views_eq(&d2, &d) => {}
                        _ => {
                            eprintln!("module {}: the {} view of its files up to the view differs", driver::name_of(pers, &st.store, m), shown);
                            return 3;
                        }
                    }
                }
            }
        }
    }
    println!("{} modules: every view read, one memo, agrees", order.len());
    0
}

/// con-leche: none — the command line's search path and one module, interned, with
/// the pins: what `--home`, `--reads` and `--reach` start from.  The reserved-name
/// pins are interned first, as the driver's are before any check (the reach reads
/// them; upstream's are Lean constants)
fn setup(sp: &[String], mods: &[String], pers: &PersTier, st: &mut AState) -> Result<(OleanRequest, Vec<NIdx>, spec::OleanPins), u8> {
    let req = match OleanRequest::new(sp, mods, &[]) {
        Ok(r) => r,
        Err(m) => {
            eprintln!("{}", m);
            return Err(3);
        }
    };
    if let Err(e) = con_ron_core::arena::pins::intern_reserved_pins(pers, st) {
        return Err(fail_with(&e));
    }
    let (roots, _) = match req.intern(pers, st) {
        Ok(p) => p,
        Err(e) => return Err(fail_with(&e)),
    };
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Ok(p) => p,
        Err(e) => return Err(fail_with(&e)),
    };
    Ok((req, roots, pk))
}

/// con-leche: OleanCompare.lean:165-174 runHome
/// `--home`: each module's home read.
fn run_home(sp: &[String], mods: &[String]) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let (req, roots, pk) = match setup(sp, mods, pers, &mut st) {
        Ok(x) => x,
        Err(c) => return c,
    };
    for m in &roots {
        let h = match files::read_files(&StdFs, pers, &st.store, &req.search_path, m, &OLeanLevel::Private) {
            Err(e) => Err(e),
            Ok(f) => worker::home_of(&pk, pers, &mut st.store, m, &f),
        };
        match h {
            Err(e) => return fail_with(&e),
            Ok((l, expo)) => {
                let n = |x: fn(&module::Expo) -> bool| expo.iter().filter(|e| x(e)).count();
                println!(
                    "{}: {} constants, exported {} same, {} hidden, {} absent",
                    driver::name_of(pers, &st.store, m),
                    l.constants.len(),
                    n(|e| matches!(e, module::Expo::Same)),
                    n(|e| matches!(e, module::Expo::Hidden)),
                    n(|e| matches!(e, module::Expo::Absent))
                );
            }
        }
    }
    0
}

/// con-leche: ConLeche/Frontend/Olean/Levels.lean:175-176 ModSet.card
/// The number of positions in the set.
fn mod_set_card(s: &[u8]) -> usize {
    s.iter().map(|b| b.count_ones() as usize).sum()
}

/// con-leche: OleanCompare.lean:177-206 runReads
/// `--reads`: a worker's reads at one module.  The reads are sequential here, so
/// `--jobs` is accepted and has no effect.
fn run_reads(sp: &[String], m: &str, dump: bool, levels_only: bool) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let (req, roots, pk) = match setup(sp, &[m.to_string()], pers, &mut st) {
        Ok(x) => x,
        Err(c) => return c,
    };
    let m = &roots[0];
    let shown = driver::name_of(pers, &st.store, m);
    if levels_only {
        let own = match files::read_part_names(&StdFs, &pk, pers, &mut st.store, &req.search_path, m, &OLeanLevel::Private) {
            Err(e) => return fail_with(&e),
            Ok(o) => o,
        };
        let ld = match levels::header_fixpoint(&StdFs, &pk, pers, &mut st.store, &req.search_path, own.header.is_module, &own.header.imports) {
            Err(e) => return fail_with(&e),
            Ok(ld) => ld,
        };
        let pub_ = levels::pub_closures(&ld);
        println!("{}: loads {} modules; {} public-import closures", shown, ld.order.len(), pub_.len());
        return 0;
    }
    let w = match index::worker_reads(&StdFs, &pk, pers, &mut st.store, &req.search_path, m, &Vec::new()) {
        Err(e) => return fail_with(&e),
        Ok(w) => w,
    };
    let ld = &w.loads;
    if dump {
        for (n, fl) in ld.order.iter().zip(ld.flags.iter()) {
            println!("load {} {} {}", driver::name_of(pers, &st.store, n), fl.import_all, fl.is_exported);
        }
    }
    let priv_ = ld.flags.iter().filter(|f| f.import_all).count();
    let names = w.index.first.len();
    let pub_avg = if ld.order.is_empty() {
        0
    } else {
        w.pub_.iter().map(|s| mod_set_card(s)).sum::<usize>() / ld.order.len()
    };
    let merged: usize = w.clashes.iter().map(|c| c.copies.len()).sum();
    println!(
        "{}: own {} constants; loads {} modules ({} private, {} exported); {} names, {} later copies; {} names held twice ({} copies), merged; public-import closure {} modules on average",
        shown,
        w.own.consts.len(),
        ld.order.len(),
        priv_,
        ld.order.len() - priv_,
        names,
        w.index.more.len(),
        w.clashes.len(),
        merged,
        pub_avg
    );
    0
}

/// con-leche: OleanCompare.lean:209-244 runReach
/// `--reach`: a worker's context at one module.  `--jobs` as in `run_reads`.
fn run_reach(sp: &[String], m: &str, list: bool) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let (req, roots, pk) = match setup(sp, &[m.to_string()], pers, &mut st) {
        Ok(x) => x,
        Err(c) => return c,
    };
    let m = &roots[0];
    let w = match index::worker_reads(&StdFs, &pk, pers, &mut st.store, &req.search_path, m, &Vec::new()) {
        Err(e) => return fail_with(&e),
        Ok(w) => w,
    };
    let f = match files::read_files(&StdFs, pers, &st.store, &req.search_path, m, &OLeanLevel::Private) {
        Err(e) => return fail_with(&e),
        Ok(f) => f,
    };
    let l = match lazy::load_view(&pk, pers, &mut st.store, 0, m, &f) {
        Err(e) => return fail_with(&e),
        Ok(l) => l,
    };
    let own = worker::own_names(&l.constants);
    let cs = worker::unskipped(&l.constants);
    let mg = group::merged_of_list(&pk, &cs);
    let names: Vec<NIdx> = cs.iter().map(|c| NIdx::of_word(c.c.name.word)).collect();
    let ds = match emit::emit_all(&pk, &mg, &names) {
        Err(e) => return fail_with(&e),
        Ok(em) => match records::decls_of(pers, &st.store, em) {
            Err((e, _)) => return fail_with(&e),
            Ok(p) => p.decls,
        },
    };
    let mut rs: Vec<NIdx> = Vec::new();
    for d in &ds {
        match reach::record_reads(pers, &mut st, d) {
            Err(e) => return fail_with(&e),
            Ok(xs) => rs.extend(xs),
        }
    }
    for c in &cs {
        rs.extend(c.uses.iter().map(|n| NIdx::of_word(n.word)));
    }
    let r = match reach::reach(&StdFs, &pk, pers, &mut st, &req.search_path, m, &w, &own, &rs) {
        Err(e) => return fail_with(&e),
        Ok(r) => r,
    };
    // upstream's `reach` infers the pending flags itself; here they run after the
    // freeze, as the driver's `module_phase` runs them (reach.rs's module note)
    let ix = match con_ron_core::arena::stream_index::build_index(pers, &mut st, con_ron_core::arena::stream_index::stream_index_empty(), &r.ctx, 0) {
        Err((e, _)) => return fail_with(&e),
        Ok(ix) => ix,
    };
    let tier: PersTier = checker::freeze_tier(&mut st.store, ix);
    let mut fws: AState = checker::worker_state(&st.pins);
    let inferred = reach::infer_flags(&tier, &mut fws, &r.ctx, &r.pending);
    let _ = checker::thaw_tier(&mut st.store, tier);
    if let Err(e) = inferred {
        return fail_with(&e);
    }
    let mut consts = 0usize;
    for d in &r.ctx {
        match install::decl_constants(pers, &mut st, d) {
            Err(e) => return fail_with(&e),
            Ok(xs) => consts += xs.len(),
        }
    }
    let groups = r.ctx.iter().filter(|d| matches!(d, IDeclaration::IndDecl(..))).count();
    let mods = r.homes.iter().map(|h| h.word).collect::<std::collections::HashSet<u32>>().len();
    if list {
        for (d, h) in r.ctx.iter().zip(r.homes.iter()) {
            let n = match con_ron_core::arena::env::i_declaration_names(d).first() {
                Some(n) => driver::name_of(pers, &st.store, n),
                None => "[anonymous]".to_string(),
            };
            println!("ctx {} {}", n, driver::name_of(pers, &st.store, h));
        }
        for (y, h) in &r.completed {
            println!("completed {} in the view of {}", driver::name_of(pers, &st.store, y), driver::name_of(pers, &st.store, h));
        }
    }
    println!(
        "{}: own {} records; loads {} modules, {} names; reach {} records ({} constants, {} groups) from {} modules; {} completed; {} searches; {} flags inferred",
        driver::name_of(pers, &st.store, m),
        ds.len(),
        w.loads.order.len(),
        w.index.first.len(),
        r.ctx.len(),
        consts,
        groups,
        mods,
        r.completed.len(),
        r.searches,
        r.inferred
    );
    0
}

/// con-leche: OleanCompare.lean:246-251 internalName
/// Lean's `Name.isInternal`: lean4export's default roots leave out the constants so
/// named, which the reader starts from, so a record only the reader has must be so
/// named.
fn internal_name(pers: &PersTier, st: &AState, n: u32) -> bool {
    let shown = driver::name_of(pers, &st.store, &NIdx::of_word(n));
    shown.split('.').any(|c| c.starts_with('_') || c.starts_with("\u{ab}_"))
}

/// con-leche: OleanCompare.lean:253-329 main
/// The record for record comparison.
fn run_compare(file: &str, sp: &[String], mods: &[String], constants: &[String]) -> u8 {
    let pers: &PersTier = &PersTier::empty();
    let mut st = AState::empty();
    let t0 = std::time::Instant::now();
    let path = con_ron::render::cps(file);
    let (read, err) = {
        let mut src = FileChunks { fs: &StdFs, path: &path, off: 0, reads: 0, err: None };
        let read = export_c::parse_source(pers, &mut st, &mut src);
        (read, src.err)
    };
    let js = match (err, read) {
        (Some(m), _) => {
            eprintln!("stream: {}", con_ron::olean_fs::path_of(&m));
            return 3;
        }
        (None, Err((e, l))) => {
            eprintln!("stream: {} at line {}", driver::message(&e), l);
            return 3;
        }
        (None, Ok(r)) => r.decls,
    };
    let t1 = t0.elapsed().as_millis();
    let req = match OleanRequest::new(sp, mods, constants) {
        Ok(r) => r,
        Err(m) => {
            eprintln!("{}", m);
            return 3;
        }
    };
    let (roots, cs) = match req.intern(pers, &mut st) {
        Ok(p) => p,
        Err(e) => return fail_with(&e),
    };
    let os = match records::read_oleans_full(&StdFs, pers, &mut st.store, &req.search_path, &roots, &cs) {
        Err((e, l)) => {
            eprintln!("oleans: {} at record {}", driver::message(&e), l);
            return 3;
        }
        Ok(ds) => ds,
    };
    let t2 = t0.elapsed().as_millis();
    println!("stream: {} records ({} ms); oleans: {} records ({} ms)", js.len(), t1, os.len(), t2 - t1);
    let (jm, jd) = to_map(&js);
    let (om, od) = to_map(&os);
    println!("duplicate keys: stream {}, oleans {}", jd, od);
    let mut bad = 0usize;
    let mut shown = 0usize;
    for (k, i) in &jm {
        match om.get(k) {
            None => {
                bad += 1;
                if shown < 20 {
                    println!("only in the stream: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                    shown += 1;
                }
            }
            Some(j) => {
                if !decl_eq(pers, &st, &js[*i], &os[*j]) {
                    bad += 1;
                    if shown < 20 {
                        println!("differs: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                        shown += 1;
                    }
                }
            }
        }
    }
    let mut extra = 0usize;
    for k in om.keys() {
        if !jm.contains_key(k) {
            if constants.is_empty() && internal_name(pers, &st, *k) {
                extra += 1;
            } else {
                bad += 1;
                if shown < 40 {
                    println!("only in the oleans: {}", driver::name_of(pers, &st.store, &NIdx::of_word(*k)));
                    shown += 1;
                }
            }
        }
    }
    let count_diff = js.len() + extra != os.len();
    println!("{} records under internal names, which the export's default leaves out", extra);
    println!(
        "{} stream keys, {} olean keys, {} differences, {} duplicate keys, {} / {} records",
        jm.len(),
        om.len(),
        bad,
        jd + od,
        js.len(),
        os.len()
    );
    if bad == 0 && jd == 0 && od == 0 && !count_diff {
        0
    } else {
        1
    }
}

/// con-leche: OleanCompare.lean:253-329 main
/// The entry point: one thread with the checker's stack, as the binary's.
fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let h = std::thread::Builder::new().stack_size(driver::STACK_BYTES).spawn(move || {
        let (flags, args): (Vec<String>, Vec<String>) =
            argv.into_iter().partition(|s| s.starts_with("--constant="));
        let constants: Vec<String> =
            flags.iter().map(|s| s["--constant=".len()..].to_string()).collect();
        let split = |sp: &str| -> Vec<String> {
            sp.split(':').filter(|d| !d.is_empty()).map(|d| d.to_string()).collect()
        };
        // `--reads`/`--reach`: the options are the arguments starting with `--`
        let opts_rest = |a: &[String]| -> (Vec<String>, Vec<String>) { a.iter().cloned().partition(|s| s.starts_with("--")) };
        if args.len() >= 3 && args[0] == "--views" {
            run_views(&split(&args[1]), &args[2..])
        } else if args.len() >= 3 && args[0] == "--home" {
            run_home(&split(&args[1]), &args[2..])
        } else if !args.is_empty() && args[0] == "--reads" {
            let (opts, rest) = opts_rest(&args[1..]);
            if rest.len() == 2 {
                run_reads(&split(&rest[0]), &rest[1], opts.iter().any(|o| o == "--loads"), opts.iter().any(|o| o == "--levels"))
            } else {
                eprintln!("usage: olean-compare --reads [--jobs=N] [--loads] [--levels] SEARCHPATH MODULE");
                3
            }
        } else if !args.is_empty() && args[0] == "--reach" {
            let (opts, rest) = opts_rest(&args[1..]);
            if rest.len() == 2 {
                run_reach(&split(&rest[0]), &rest[1], opts.iter().any(|o| o == "--list"))
            } else {
                eprintln!("usage: olean-compare --reach [--jobs=N] [--list] SEARCHPATH MODULE");
                3
            }
        } else if args.len() >= 3 {
            run_compare(&args[0], &split(&args[1]), &args[2..], &constants)
        } else {
            eprintln!("usage: olean-compare EXPORT.ndjson SEARCHPATH MODULE...");
            3
        }
    });
    match h {
        Ok(t) => match t.join() {
            Ok(code) => {
                // no free cascade on the way out
                std::process::exit(code as i32)
            }
            Err(_) => ExitCode::from(3),
        },
        Err(_) => ExitCode::from(3),
    }
}
