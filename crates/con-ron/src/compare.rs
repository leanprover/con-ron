//! `--compare`: a challenge checked with its axioms justified by a solution
//! (con-leche's `Driver/CompareJson.lean` and `Driver/Compare.lean`).
//!
//! ```text
//! con-ron [OPTIONS] --compare [--] CHALLENGE.ndjson SOLUTION.ndjson
//! con-ron [OPTIONS] --olean --compare [--trusted-search-path=DIRS] --search-path=DIRS
//!         [--constant=NAME]... [--] CHALLENGE SOLUTION
//! ```
//!
//! **The run.**  The solution is checked as any input is; then the challenge is
//! checked as any input is, with the solution's index as its **solution**: the
//! challenge's axioms other than the built-in ones, and its records whose value
//! uses `sorryAx` (each read as the axiom of its statement), take the
//! justification route (`con_ron_core::arena::justify`): the solution holds a
//! constant of the same name and type, up to the names of its level
//! parameters, and everything that type reads is the same constant in both.
//!
//! **One store.**  Both inputs are read and prepared into the ONE store of the
//! run, so a name, a level and an expression of the challenge and of the
//! solution are equal exactly when their handles are (hash-consing).  The
//! solution's check phase is the flat driver's (`driver::check_decls_driver`):
//! its index built, frozen, the pool, thawed; the thawed index is kept and is
//! the solution (`justify::solution_of`).  The challenge's index is built after
//! the thaw, on the same store, which only grows, so the solution's handles stay
//! valid.  Then the challenge's check phase, every job with `Some(&sol)`.
//!
//! The calls, in order, each a verified core function (marked
//! `ConRon.Capstone:` at its call): `intern_reserved_pins`,
//! `builtin_prelude_e`, the two reads, `prelude_ix_dup`, `prepare_d` (the
//! solution's), `intern_all_pins`, the solution's check phase, `prepare_d` (the
//! challenge's; on `--olean` it runs before the solution's read, with
//! `hole_records` after it), `side_records`, `solution_of`, the challenge's check
//! phase, and for the accept line `justifiable` of each checked record.
//!
//! **The verdict**: a failed read is the read's (`read_failed`); the solution's
//! failed check is reported as the solution's (`the solution S: `); the
//! challenge's as any check's, an axiom the solution does not justify with the
//! reason (exit 1); on the accept the success line and one line per justified
//! record, labelled as the challenge declares it.

use std::time::Instant;

use con_ron_core::arena::checker;
use con_ron_core::arena::env as ienv;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::justify;
use con_ron_core::arena::monad;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
use con_ron_core::arena::pins::intern_reserved_pins;
use con_ron_core::arena::store::PersTier;
use con_ron_core::arena::stream_index::IStreamIndex;
use con_ron_core::frontend::compare as fcompare;
use con_ron_core::frontend::export_c;
use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
use con_ron_core::frontend::olean::closure;
use con_ron_core::frontend::olean::files;
use con_ron_core::frontend::olean::files::RootAt;
use con_ron_core::frontend::olean::records;
use con_ron_core::frontend::olean::records::{value_cache_empty, ModRef, ValueCache};
use con_ron_core::frontend::olean::spec;
use con_ron_core::frontend::olean::spec::OleanPins;
use con_ron_core::frontend::pace::{pace_dup, pace_on, Pace};
use con_ron_core::frontend::prelude;
use con_ron_core::frontend::prepare;
use con_ron_core::frontend::prepare::{Prepared, PreludeIx};
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::name::Name;
use con_ron_core::ron::hashmap::{Dup, Eq2};
use con_ron_core::ron::nat::Nat;

use crate::driver;
use crate::driver::{Heartbeat, Silent};
use crate::olean_fs;
use crate::render;

/// con-leche: ConLeche/Driver/Dispatch.lean:26-62 Req
/// What a compared run is run with, besides its inputs: the mode, the `Nat`
/// size limit, the pin list's source, the worker count and the heartbeat.
pub struct CompareOpts<'a> {
    pub mode: CheckMode,
    pub mode_tag: &'a str,
    pub max_nat_size: &'a Nat,
    pub pins: &'a Option<String>,
    pub no_pins: bool,
    pub jobs: u64,
    pub progress: &'a Pace,
}

/// con-leche: ConLeche/Driver/CmpReq.lean:18-25 CmpReq
/// **A compared `--olean` run's request**: the challenge and solution modules,
/// the trusted directories (none given: the search path is trusted), the search
/// path, and the `--constant` names (none: every constant).
pub struct CmpRequest {
    pub challenge: Name,
    pub solution: Name,
    pub trusted: Vec<Vec<u32>>,
    pub path: Vec<Vec<u32>>,
    pub constants: Vec<Name>,
}

/// con-leche: ConLeche/Driver/Compare.lean:78-80 CmpReq.chalRoots
/// **The challenge's lookup**: the trusted path, never anything else.
pub fn chal_roots(r: &CmpRequest) -> files::Roots {
    if r.trusted.is_empty() {
        files::roots_of_path(r.path.clone())
    } else {
        files::roots_of_path(r.trusted.clone())
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:82-84 CmpReq.solRoots
/// **The solution's lookup**: the trusted path first, then the search path.
pub fn sol_roots(r: &CmpRequest) -> files::Roots {
    if r.trusted.is_empty() {
        files::roots_of_path(r.path.clone())
    } else {
        files::Roots { path: r.trusted.clone(), fallback: r.path.clone() }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:119-130 readFailed
/// **The verdict of a failed read**: its line and exit code.  The port's
/// `Native` is a decline, as everywhere in this crate (`driver::exit_code`).
fn read_failed(mode_tag: &str, label: &str, e: &(CheckError, u64)) -> u8 {
    match &e.0 {
        CheckError::NotImplemented(_) | CheckError::Native(_) => {
            eprintln!("con-ron: declined: {} ({})", driver::message(&e.0), mode_tag);
            2
        }
        CheckError::Invalid(_) => {
            eprintln!("con-ron: invalid: {} ({})", driver::message(&e.0), mode_tag);
            1
        }
        CheckError::Internal(_) => {
            eprintln!("con-ron: {}:{}: {}", label, e.1, driver::message(&e.0));
            3
        }
    }
}

/// con-leche: none — a step after the reads that fails (the preparation, the pin
/// walk, `side_records`): con-leche's are total, the port's can stop.  The
/// decline, the reject and the internal error, as `con-ron`'s frontend exits.
fn step_failed(e: &CheckError, mode_tag: &str) -> u8 {
    let m = driver::message(e);
    match e {
        CheckError::NotImplemented(_) | CheckError::Native(_) => {
            eprintln!("con-ron: declined: {} ({})", m, mode_tag);
            2
        }
        CheckError::Invalid(_) => {
            eprintln!("con-ron: invalid: {} ({})", m, mode_tag);
            1
        }
        CheckError::Internal(_) => {
            eprintln!("con-ron: {} ({})", m, mode_tag);
            3
        }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:112-117 hoistedNote
/// The receipt of the records hoisted ahead of the pinned `Nat` operations they
/// ground.
fn hoisted_note(pers: &PersTier, st: &AState, hoisted: &Vec<NIdx>) {
    if !hoisted.is_empty() {
        let names: Vec<String> = hoisted.iter().map(|n| driver::name_of(pers, &st.store, n)).collect();
        eprintln!(
            "con-ron: {} declarations hoisted ahead of the pinned Nat operations they ground: {}",
            hoisted.len(),
            names.join(", ")
        );
    }
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// The run's start: the reserved-name pins and the built-in prelude, into the
/// run's one store (`check_main`'s first two steps), or the exit code.
fn start(pers: &PersTier, st: &mut AState, mode_tag: &str) -> Result<PreludeIx, u8> {
    // ConRon.Capstone: h1
    match intern_reserved_pins(pers, st) {
        Ok(()) => (),
        Err(e) => {
            eprintln!(
                "con-ron: the reserved-name pins do not intern ({}) ({})",
                driver::message(&e),
                mode_tag
            );
            return Err(3);
        }
    }
    // ConRon.Capstone: h2
    match prelude::builtin_prelude_e(pers, st) {
        Ok(p) => Ok(p),
        Err((e, line)) => {
            eprintln!(
                "con-ron: the built-in prelude does not parse (line {}: {}); regenerate it with \
                 `lake exe natop-pins-export` ({})",
                line,
                driver::message(&e),
                mode_tag
            );
            Err(3)
        }
    }
}

/// con-leche: ConLeche/Driver/Run.lean:74-99 checkDeclsIO
/// The pin list and its walk, once, before the first check phase (`check_main`'s
/// `hpins` and `h5`), or the exit code.
fn pins_walk(o: &CompareOpts, pers: &PersTier, st: &mut AState) -> Result<Vec<INatOpPinSet>, u8> {
    // ConRon.Capstone: hpins
    let pins = match driver::pins_for_run(o.pins, o.no_pins) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("con-ron: {}", e);
            return Err(3);
        }
    };
    // ConRon.Capstone: h5
    match checker::intern_all_pins(pers, st, &pins, o.max_nat_size) {
        Ok(p) => Ok(p),
        Err(e) => Err(step_failed(&e, o.mode_tag)),
    }
}

/// con-leche: ConLeche/Driver/Run.lean:74-99 checkDeclsIO
/// One input's check phase on a lean4export run: `driver::check_decls_driver`
/// (the index, the freeze, the pool over `run_job` with `sol`, the thaw), with
/// the heartbeat when it is on.
fn check_phase(
    o: &CompareOpts,
    pers: &PersTier,
    st: &mut AState,
    hb: &mut Heartbeat,
    ipins: &Vec<INatOpPinSet>,
    sol: Option<&justify::Solution>,
    ds: &Vec<IDeclaration>,
) -> Result<IStreamIndex, (CheckError, u64)> {
    if pace_on(o.progress) {
        driver::check_decls_driver(pers, st, &o.mode, ipins, sol, ds, o.jobs, hb)
    } else {
        driver::check_decls_driver(pers, st, &o.mode, ipins, sol, ds, o.jobs, &mut Silent)
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:154-177 checkOleansG
/// One closure's check phase on an `--olean` run: `driver::check_decls_driver_with`
/// over `driver::olean_job` (a theorem's value read from its file in its job),
/// at the read's pins, values and lookup, with `sol`.
#[allow(clippy::too_many_arguments)]
fn check_phase_oleans(
    o: &CompareOpts,
    pers: &PersTier,
    st: &mut AState,
    hb: &mut Heartbeat,
    ipins: &Vec<INatOpPinSet>,
    sol: Option<&justify::Solution>,
    pk: &OleanPins,
    values: &Vec<ModRef>,
    sp: &files::Roots,
    ds: &Vec<IDeclaration>,
) -> Result<IStreamIndex, (CheckError, u64)> {
    let mode = &o.mode;
    let job = |tier: &PersTier, w: &mut AState, c: &mut ValueCache, k: u64| {
        driver::olean_job(tier, w, c, mode, ipins, ds, pk, values, sp, sol, k)
    };
    if pace_on(o.progress) {
        driver::check_decls_driver_with(pers, st, ds, o.jobs, hb, value_cache_empty, job)
    } else {
        driver::check_decls_driver_with(pers, st, ds, o.jobs, &mut Silent, value_cache_empty, job)
    }
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// **The accept**: the challenge's records the solution justified, labelled as
/// the challenge declares them (`prepared`, before `hole_records` and
/// `side_records`): the record `checked[i]` offers a statement
/// (`justify::justifiable`), so `prepared[i]` took the justification route.
fn accepted(
    pers: &PersTier,
    st: &mut AState,
    prepared: &Vec<IDeclaration>,
    checked: &Vec<IDeclaration>,
    records_c: usize,
    solution: &str,
    records_s: usize,
    mode_tag: &str,
) -> u8 {
    let mut holes: Vec<String> = Vec::new();
    let mut i = 0usize;
    while i < checked.len() && i < prepared.len() {
        // ConRon.Capstone: the accept line's labels (`justifiable`, outside the theorems)
        match justify::justifiable(st, &checked[i]) {
            Ok(Some(_)) => holes.push(driver::decl_label(pers, &st.store, &prepared[i])),
            Ok(None) => (),
            Err(e) => return step_failed(&e, mode_tag),
        }
        i += 1;
    }
    println!(
        "con-ron: accepted {} declarations, {} axioms justified by the solution {} ({} \
         declarations accepted) ({})",
        records_c,
        holes.len(),
        solution,
        records_s,
        mode_tag
    );
    for h in &holes {
        println!("con-ron: {} justified by the solution", h);
    }
    0
}

/// con-leche: ConLeche/Driver/CompareJson.lean:38-90 compareJsonG
/// **`--compare` on two lean4export files** (module note): the challenge's file
/// and the solution's parsed into one store, the solution prepared and checked,
/// then the challenge prepared, its records read with the solution
/// (`side_records`) and checked with it.
pub fn compare_json(o: &CompareOpts, challenge: &str, solution: &str) -> u8 {
    let t0 = Instant::now();
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    let pre: PreludeIx = match start(pers, &mut st, o.mode_tag) {
        Ok(p) => p,
        Err(code) => return code,
    };
    let mut hb = Heartbeat::new(pace_dup(o.progress), t0);
    // THE CHALLENGE'S FILE, then the solution's, into the one store.
    // ConRon.Capstone: h3 (the challenge's `parse_source`)
    hb.read_starts(&render::display_path(challenge));
    let rc = match driver::parse_export_stream_d(pers, &mut st, challenge, export_c::CHUNK_SIZE) {
        Err(e) => {
            eprintln!("con-ron: {}: {}", render::display_path(challenge), e);
            return 3;
        }
        Ok((Err(e), _)) => return read_failed(o.mode_tag, &render::display_path(challenge), &e),
        Ok((Ok(r), _)) => r,
    };
    // ConRon.Capstone: h3S (the solution's `parse_source`)
    hb.read_starts(&render::display_path(solution));
    let rs = match driver::parse_export_stream_d(pers, &mut st, solution, export_c::CHUNK_SIZE) {
        Err(e) => {
            eprintln!("con-ron: {}: {}", render::display_path(solution), e);
            return 3;
        }
        Ok((Err(e), _)) => return read_failed(o.mode_tag, &render::display_path(solution), &e),
        Ok((Ok(r), _)) => r,
    };
    let records_c = rc.decls.len();
    let records_s = rs.decls.len();
    // THE SOLUTION, checked as any input.
    // ConRon.Capstone: hdup (`prelude_ix_dup`: the challenge's copy of the prelude)
    let pre_c: PreludeIx = prepare::prelude_ix_dup(&pre);
    // ConRon.Capstone: h4S
    let prep_s: Prepared = match prepare::prepare_d(pers, &mut st, pre, rs.decls, &DeclUsedConsts) {
        Ok(p) => p,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    hoisted_note(pers, &st, &prep_s.hoisted);
    let ipins = match pins_walk(o, pers, &mut st) {
        Ok(p) => p,
        Err(code) => return code,
    };
    hb.file_records = records_s;
    hb.synthesised = prep_s.synthesised;
    // ConRon.Capstone: h6S, h7S, h8S (the solution's index, freeze, pool and thaw)
    let ix_s: IStreamIndex = match check_phase(o, pers, &mut st, &mut hb, &ipins, None, &prep_s.decls) {
        Ok(ix) => ix,
        Err((e, i)) => {
            let who = format!("the solution {}: ", solution);
            return driver::verdict_failure(pers, &st.store, &prep_s.decls, &e, i, o.mode_tag, t0, &who);
        }
    };
    // THE CHALLENGE, checked with the solution.
    // ConRon.Capstone: h4
    let prep_c: Prepared = match prepare::prepare_d(pers, &mut st, pre_c, rc.decls, &DeclUsedConsts) {
        Ok(p) => p,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    hoisted_note(pers, &st, &prep_c.hoisted);
    // ConRon.Capstone: hside (`side_records`)
    let recs_c: Vec<IDeclaration> = match justify::side_records(pers, &mut st, &prep_c.decls, 0, Vec::new()) {
        Ok(v) => v,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    // ConRon.Capstone: hsol (`solution_of`)
    let sol: justify::Solution = justify::solution_of(ix_s, &recs_c);
    hb.file_records = records_c;
    hb.synthesised = prep_c.synthesised;
    // ConRon.Capstone: h6, h7, h8 (the challenge's index, freeze, pool and thaw)
    match check_phase(o, pers, &mut st, &mut hb, &ipins, Some(&sol), &recs_c) {
        Err((e, i)) => driver::verdict_failure(pers, &st.store, &recs_c, &e, i, o.mode_tag, t0, ""),
        Ok(_) => accepted(pers, &mut st, &prep_c.decls, &recs_c, records_c, solution, records_s, o.mode_tag),
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// **Why a challenge module is not on the trusted path**, where it is on the
/// search path: the challenge's closure walked through the solution's lookup,
/// and the first module whose root only the search path holds.  Only after the
/// challenge's read failed, and only for the message.
fn fallback_only(pers: &PersTier, st: &mut AState, r: &CmpRequest, c: &NIdx) -> Option<String> {
    if r.trusted.is_empty() {
        return None;
    }
    let fs = olean_fs::StdFs;
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Ok(p) => p,
        Err(_) => return None,
    };
    let sr = sol_roots(r);
    let order = match closure::closure_order(&fs, &pk, pers, &mut st.store, &sr, &vec![c.dup2()]) {
        Ok(o) => o,
        Err(_) => return None,
    };
    for m in &order {
        let n = match ienv::read_name(pers, &st.store, m) {
            Ok(n) => n,
            Err(_) => return None,
        };
        let root = files::name_root(&n);
        if let RootAt::Missing = files::root_at(&fs, &r.trusted, &root) {
            if let RootAt::Dir(d) = files::look_at(&fs, &sr.path, &sr.fallback, &root) {
                let shown: Vec<String> = r.trusted.iter().map(|d| olean_fs::path_of(d)).collect();
                return Some(format!(
                    "the challenge's module {} is not on the trusted path ({}); it is in {}, on the \
                     search path, which only the solution reads",
                    render::name_str(&n),
                    shown.join(":"),
                    olean_fs::path_of(&d)
                ));
            }
        }
    }
    None
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// **`--olean --compare`** (module note): the challenge's closure read through
/// the trusted lookup alone, its homes with it, `--constant` names checked to be
/// its own, prepared and its theorem holes read as axioms (`hole_records`); the
/// solution's closure read through the solution's lookup (from the constants the
/// challenge's records install, under `--constant`), prepared and checked; then
/// the challenge's records read with the solution (`side_records`) and checked
/// with it.
pub fn compare_oleans(o: &CompareOpts, r: &CmpRequest) -> u8 {
    let t0 = Instant::now();
    // ConRon.Capstone: `startState`
    let mut st = AState::empty();
    // ConRon.Capstone: `emptyTier`
    let pers: &PersTier = &PersTier::empty();
    let pre: PreludeIx = match start(pers, &mut st, o.mode_tag) {
        Ok(p) => p,
        Err(code) => return code,
    };
    let mut hb = Heartbeat::new(pace_dup(o.progress), t0);
    let c_text = render::name_str(&r.challenge);
    let s_text = render::name_str(&r.solution);
    // The request's names, as handles.
    // ConRon.Capstone: hnames (`intern_name` of each)
    let c: NIdx = match monad::intern_name(pers, &mut st, &r.challenge) {
        Ok(h) => h,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    let s: NIdx = match monad::intern_name(pers, &mut st, &r.solution) {
        Ok(h) => h,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    let cs: Option<Vec<NIdx>> = if r.constants.is_empty() {
        None
    } else {
        let mut v: Vec<NIdx> = Vec::with_capacity(r.constants.len());
        for n in &r.constants {
            match monad::intern_name(pers, &mut st, n) {
                Ok(h) => v.push(h),
                Err(e) => return step_failed(&e, o.mode_tag),
            }
        }
        Some(v)
    };
    let cr = chal_roots(r);
    let sr = sol_roots(r);
    // THE CHALLENGE'S CLOSURE, through the trusted lookup alone, its homes with it.
    hb.read_starts(&c_text);
    // ConRon.Capstone: h3 (`read_oleans` at the challenge's lookup, lenient, homes)
    let mut rd_c = match records::read_oleans(&olean_fs::read_notes_new(o.progress), pers, &mut st.store, &cr, &vec![c.dup2()], &cs, true, true) {
        Ok(rd) => rd,
        Err(e) => {
            if let Some(why) = fallback_only(pers, &mut st, r, &c) {
                eprintln!("con-ron: {} ({})", why, o.mode_tag);
                return 1;
            }
            return read_failed(o.mode_tag, &c_text, &e);
        }
    };
    // `--constant`: declarations of the challenge module itself
    if let Some(why) = fcompare::foreign_constant(pers, &st.store, &cs, &c, &rd_c.homes) {
        eprintln!("con-ron: {} ({})", olean_fs::path_of(&why), o.mode_tag);
        return 1;
    }
    let records_c = rd_c.decls.len();
    let decls_c: Vec<IDeclaration> = std::mem::take(&mut rd_c.decls);
    // ConRon.Capstone: hdup (`prelude_ix_dup`: the challenge's copy of the prelude)
    let pre_c: PreludeIx = prepare::prelude_ix_dup(&pre);
    // ConRon.Capstone: h4 (the challenge's `prepare_d`, what a record mentions read off its load)
    let prep_c: Prepared = match prepare::prepare_d(pers, &mut st, pre_c, decls_c, &rd_c) {
        Ok(p) => p,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    // ConRon.Capstone: hhole (`hole_records`: the theorems its file marks as holes, axioms)
    let holed_c: Vec<IDeclaration> = match fcompare::hole_records(&rd_c, pers, &mut st, &prep_c.decls, 0, Vec::new()) {
        Ok(v) => v,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    // What the challenge's check keeps of its read: the pins and the values (the
    // merged constants' last readers were the preparation and `hole_records`).
    let pk_c: OleanPins = rd_c.pins;
    let values_c: Vec<ModRef> = rd_c.values;
    drop(rd_c.merged);
    drop(rd_c.homes);
    // THE SOLUTION'S CLOSURE, from the constants the challenge's records install, or
    // all of it.
    let need: Option<Vec<NIdx>> = match &cs {
        None => None,
        Some(_) => Some(prep_c.decls.iter().filter_map(fcompare::rec_key).collect()),
    };
    hb.read_starts(&s_text);
    // ConRon.Capstone: h3S (`read_oleans` at the solution's lookup, lenient)
    let mut rd_s = match records::read_oleans(&olean_fs::read_notes_new(o.progress), pers, &mut st.store, &sr, &vec![s.dup2()], &need, true, false) {
        Ok(rd) => rd,
        Err(e) => return read_failed(o.mode_tag, &s_text, &e),
    };
    // a solution importing its challenge is no solution
    if rd_s.values.iter().any(|m| m.name.eq2(&c)) {
        eprintln!(
            "con-ron: {} does not solve {}: the solution's closure holds the challenge ({})",
            s_text, c_text, o.mode_tag
        );
        return 1;
    }
    let records_s = rd_s.decls.len();
    let decls_s: Vec<IDeclaration> = std::mem::take(&mut rd_s.decls);
    // ConRon.Capstone: h4S
    let prep_s: Prepared = match prepare::prepare_d(pers, &mut st, pre, decls_s, &rd_s) {
        Ok(p) => p,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    let pk_s: OleanPins = rd_s.pins;
    let values_s: Vec<ModRef> = rd_s.values;
    drop(rd_s.merged);
    hoisted_note(pers, &st, &prep_s.hoisted);
    let ipins = match pins_walk(o, pers, &mut st) {
        Ok(p) => p,
        Err(code) => return code,
    };
    hb.file_records = records_s;
    hb.synthesised = prep_s.synthesised;
    // ConRon.Capstone: h6S, h7S, h8S (the solution's index, freeze, pool and thaw)
    let ix_s: IStreamIndex = match check_phase_oleans(o, pers, &mut st, &mut hb, &ipins, None, &pk_s, &values_s, &sr, &prep_s.decls) {
        Ok(ix) => ix,
        Err((e, i)) => {
            let who = format!("the solution {}: ", s_text);
            return driver::verdict_failure(pers, &st.store, &prep_s.decls, &e, i, o.mode_tag, t0, &who);
        }
    };
    // THE CHALLENGE'S CLOSURE, checked with the solution.
    hoisted_note(pers, &st, &prep_c.hoisted);
    // ConRon.Capstone: hside (`side_records`)
    let recs_c: Vec<IDeclaration> = match justify::side_records(pers, &mut st, &holed_c, 0, Vec::new()) {
        Ok(v) => v,
        Err(e) => return step_failed(&e, o.mode_tag),
    };
    // ConRon.Capstone: hsol (`solution_of`)
    let sol: justify::Solution = justify::solution_of(ix_s, &recs_c);
    hb.file_records = records_c;
    hb.synthesised = prep_c.synthesised;
    // ConRon.Capstone: h6, h7, h8 (the challenge's index, freeze, pool and thaw)
    match check_phase_oleans(o, pers, &mut st, &mut hb, &ipins, Some(&sol), &pk_c, &values_c, &cr, &recs_c) {
        Err((e, i)) => driver::verdict_failure(pers, &st.store, &recs_c, &e, i, o.mode_tag, t0, ""),
        Ok(_) => accepted(pers, &mut st, &prep_c.decls, &recs_c, records_c, &s_text, records_s, o.mode_tag),
    }
}
