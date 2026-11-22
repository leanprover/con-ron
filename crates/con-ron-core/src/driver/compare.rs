//! `driver::compare` — con-leche's `Driver/Compare.lean`: `--olean --compare
//! [--trusted-search-path=DIRS] --search-path=DIRS -- C S` over `CheckerIo`
//! (DESIGN.md §3.9, task #171).
//!
//! The challenge module `C`'s closure is read through the TRUSTED lookup alone
//! (`cli::chal_roots`), its homes with it; the solution `S`'s closure through
//! the trusted path first, then the search path (`cli::sol_roots`).  Both are
//! read and prepared into the ONE store of the run.  The solution's closure is
//! checked as an `--olean` run checks one; its thawed index is the solution
//! (`justify::solution_of`) of the challenge's check, in which the challenge's
//! holes (its theorems whose file marks a `sorryAx`, `hole_records`; its axioms
//! and its definitions using `sorryAx`, `side_records`) take the justification
//! route.
//!
//! ```text
//! intern_reserved_pins → builtin_prelude_e → intern_name (C, S)
//!   → read_oleans (C, the challenge's lookup, lenient, homes) → prelude_ix_dup
//!   → prepare_d (C) → hole_records → read_oleans (S, the solution's lookup)
//!   → prepare_d (S) → decode_embedded → intern_all_pins
//!   → check_phase_olean (S, no solution) → side_records → solution_of
//!   → check_phase_olean (C, with the solution)
//! ```
//!
//! — one call per step premise of `ConRon.Capstone.rust_stages_oleans_compare`,
//! in that order, on one `AState::empty()` and one `PersTier::empty()`.  The
//! verdict is `compare_json`'s (`compare_verdict`, `solution_failed`), the
//! solution named by its module.

use crate::arena::checker;
use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::arena::justify;
use crate::arena::justify::Solution;
use crate::arena::monad;
use crate::arena::monad::AState;
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::driver::check_main;
use crate::driver::check_main::Note;
use crate::driver::cli;
use crate::driver::cli::Args;
use crate::driver::compare_json;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::compare as fcompare;
use crate::frontend::olean::closure;
use crate::frontend::olean::files;
use crate::frontend::olean::files::RootAt;
use crate::frontend::olean::files::Roots;
use crate::frontend::olean::records;
use crate::frontend::olean::records::ModRef;
use crate::frontend::olean::records::OleanRead;
use crate::frontend::olean::spec;
use crate::frontend::prelude;
use crate::frontend::prepare;
use crate::frontend::text;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;

/// con-leche: ConLeche/Driver/Compare.lean:49-52 recKey
/// The names the records are found under (`recKey`), those that have one.
pub fn rec_keys(ds: &Vec<IDeclaration>) -> Vec<NIdx> {
    let mut out: Vec<NIdx> = Vec::new();
    let mut i = 0usize;
    while i < ds.len() {
        match fcompare::rec_key(&ds[i]) {
            None => (),
            Some(n) => out.push(n),
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Compare.lean:82-84 CmpReq.solRoots
/// **The solution's lookup** of the directories: the trusted path first, then
/// the search path; the search path alone where no trusted path is given.
pub fn sol_roots_of(trusted: &Vec<Vec<u32>>, path: &Vec<Vec<u32>>) -> Roots {
    if trusted.len() == 0 {
        files::roots_of_path(cli::push_files(Vec::new(), path, 0))
    } else {
        Roots { path: cli::push_files(Vec::new(), trusted, 0), fallback: cli::push_files(Vec::new(), path, 0) }
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// The directories of a path, `:`-separated, as the message shows them.
pub fn dirs_text(ds: &Vec<Vec<u32>>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < ds.len() {
        if i > 0 {
            out.push(58);
        }
        out = text::cat(out, &ds[i]);
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// The message: the module `n`, the trusted path, the directory `d` of the
/// search path that holds it.
pub fn fallback_text(n: &Name, trusted: &Vec<Vec<u32>>, d: &Vec<u32>) -> Vec<u32> {
    let t = text::cat3({ const M: [u32; 23] = [116, 104, 101, 32, 99, 104, 97, 108, 108, 101, 110, 103, 101, 39, 115, 32, 109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &name::render(n), &{ const M: [u32; 29] = [32, 105, 115, 32, 110, 111, 116, 32, 111, 110, 32, 116, 104, 101, 32, 116, 114, 117, 115, 116, 101, 100, 32, 112, 97, 116, 104, 32, 40]; crate::kernel::core_types::code_points(&M) });
    let t = text::cat3(t, &dirs_text(trusted), &{ const M: [u32; 12] = [41, 59, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
    text::cat3(t, d, &{ const M: [u32; 51] = [44, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 44, 32, 119, 104, 105, 99, 104, 32, 111, 110, 108, 121, 32, 116, 104, 101, 32, 115, 111, 108, 117, 116, 105, 111, 110, 32, 114, 101, 97, 100, 115]; crate::kernel::core_types::code_points(&M) })
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// One module of the walk: the message where only the search path holds its
/// root, none where the trusted path does (or neither).
pub fn fallback_at<F: CheckerFs>(
    fs: &F,
    pers: &PersTier,
    st: &AState,
    trusted: &Vec<Vec<u32>>,
    sr: &Roots,
    m: &NIdx,
) -> Result<Option<Vec<u32>>, CheckError> {
    let n = match monad::read_name(pers, st, m) {
        Err(e) => return Err(e),
        Ok(n) => n,
    };
    let root = files::name_root(&n);
    match files::root_at(fs, trusted, &root) {
        RootAt::Missing => match files::look_at(fs, &sr.path, &sr.fallback, &root) {
            RootAt::Dir(d) => Ok(Some(fallback_text(&n, trusted, &d))),
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// **Why a challenge module is not on the trusted path**, where it is on the
/// search path: the challenge's closure walked through the solution's lookup,
/// and the first module whose root only the search path holds.  Only after the
/// challenge's read failed, and only for the message: the challenge's read
/// itself never looks at the search path.
pub fn fallback_only<F: CheckerFs>(
    fs: &F,
    pers: &PersTier,
    st: &mut AState,
    trusted: &Vec<Vec<u32>>,
    path: &Vec<Vec<u32>>,
    c: &NIdx,
) -> Option<Vec<u32>> {
    if trusted.len() == 0 {
        return None;
    }
    let pk = match spec::olean_pins(pers, &mut st.store) {
        Err(_) => return None,
        Ok(p) => p,
    };
    let sr = sol_roots_of(trusted, path);
    let roots: Vec<NIdx> = one_root(c);
    let order = match closure::closure_order(fs, &pk, pers, &mut st.store, &sr, &roots) {
        Err(_) => return None,
        Ok(o) => o,
    };
    fallback_scan(fs, pers, st, trusted, &sr, &order)
}

/// con-leche: ConLeche/Driver/Compare.lean:86-101 fallbackOnly
/// The walk's modules in order, to the first whose root only the search path
/// holds; none at a failed read of a name.  (A loop without an early return:
/// the scan goes on, doing nothing, past the module it stopped at.)
pub fn fallback_scan<F: CheckerFs>(
    fs: &F,
    pers: &PersTier,
    st: &AState,
    trusted: &Vec<Vec<u32>>,
    sr: &Roots,
    order: &Vec<NIdx>,
) -> Option<Vec<u32>> {
    let mut found: Option<Vec<u32>> = None;
    let mut stop = false;
    let mut i = 0usize;
    while i < order.len() {
        if !stop {
            match fallback_at(fs, pers, st, trusted, sr, &order[i]) {
                Err(_) => stop = true,
                Ok(Some(t)) => {
                    found = Some(t);
                    stop = true;
                }
                Ok(None) => (),
            }
        }
        i += 1;
    }
    found
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// A step after the reads failed (the preparation, the pin walk, the holes,
/// `side_records`): its line and its exit code.
pub fn step_failed<I: CheckerIo>(io: &mut I, e: CheckError, verified: bool) -> u8 {
    let c = check_main::exit_code(&e);
    io.note(&Note::Frontend(e, verified));
    c
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// **Whether a closure's modules hold `c`**: a solution importing its
/// challenge is no solution.
pub fn holds_module(values: &Vec<ModRef>, c: &NIdx) -> bool {
    let mut i = 0usize;
    while i < values.len() {
        if values[i].name.eq2(c) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// One name, as the list of roots a read and its lines take.
pub fn one_root(h: &NIdx) -> Vec<NIdx> {
    let mut v: Vec<NIdx> = Vec::new();
    v.push(h.dup2());
    v
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// One module's name, as the list of roots a read's lines name.
pub fn one_name(n: &Name) -> Vec<Name> {
    let mut v: Vec<Name> = Vec::new();
    v.push(name::dup(n));
    v
}

/// con-leche: ConLeche/Driver/Compare.lean:141-208 compareG
/// **The compared run** (module note): the challenge's closure read through
/// the trusted lookup alone, its homes with it, `--constant` names checked to be
/// its own, prepared and its theorem holes read as axioms (`hole_records`); the
/// solution's closure read through the solution's lookup (from the constants
/// the challenge's records install, under `--constant`), prepared and checked;
/// then the challenge's records read with the solution (`side_records`) and
/// checked with it; the exit code.
pub fn compare_oleans<I: CheckerIo>(io: &mut I, a: &Args, c_name: &Name, s_name: &Name, cs: &Vec<Name>) -> u8 {
    let verified = a.verified;
    let mode = if verified { CheckMode::Verified } else { CheckMode::Trusted };
    let mut st = AState::empty();
    let pers = PersTier::empty();
    // ConRon.Capstone: h1
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => {
            io.note(&Note::ReservedPins(e, verified));
            return 3;
        }
        Ok(()) => (),
    }
    // ConRon.Capstone: h2
    let pre = match prelude::builtin_prelude_e(&pers, &mut st) {
        Err((e, line)) => {
            io.note(&Note::Prelude(e, line, verified));
            return 3;
        }
        Ok(p) => p,
    };
    // ConRon.Capstone: hnC
    let c: NIdx = match monad::intern_name(&pers, &mut st, c_name) {
        Err(e) => return step_failed(io, e, verified),
        Ok(h) => h,
    };
    // ConRon.Capstone: hnS
    let s: NIdx = match monad::intern_name(&pers, &mut st, s_name) {
        Err(e) => return step_failed(io, e, verified),
        Ok(h) => h,
    };
    let consts: Option<Vec<NIdx>> = match check_main::intern_consts(&pers, &mut st, cs) {
        Err(e) => return step_failed(io, e, verified),
        Ok(v) => v,
    };
    let cr = cli::chal_roots(a);
    let sr = cli::sol_roots(a);
    // THE CHALLENGE'S CLOSURE, through the trusted lookup alone, its homes with it.
    let c_label: Vec<Name> = one_name(c_name);
    io.oleans_read_starts(&a.progress, &c_label);
    let roots_c: Vec<NIdx> = one_root(&c);
    // ConRon.Capstone: h3
    io.read_notes_begin(&a.progress);
    let read_c = records::read_oleans(&*io, &pers, &mut st.store, &cr, &roots_c, &consts, true, true);
    io.read_notes_end();
    let mut rd_c: OleanRead = match read_c {
        Err((e, line)) => match fallback_only(&*io, &pers, &mut st, &a.trusted_path, &a.search_path, &c) {
            Some(why) => {
                io.note(&Note::CompareWhy(why, verified));
                return 1;
            }
            None => return check_main::oleans_failed(io, e, line, &c_label, verified),
        },
        Ok(rd) => rd,
    };
    // `--constant`: declarations of the challenge module itself
    match fcompare::foreign_constant(&pers, &st.store, &consts, &c, &rd_c.homes) {
        Some(why) => {
            io.note(&Note::CompareWhy(why, verified));
            return 1;
        }
        None => (),
    }
    let records_c = rd_c.decls.len();
    let decls_c = core::mem::replace(&mut rd_c.decls, Vec::new());
    // ConRon.Capstone: hdup
    let pre_c = prepare::prelude_ix_dup(&pre);
    // ConRon.Capstone: h4 (what a record mentions, off the read)
    let prep_c = match prepare::prepare_d(&pers, &mut st, pre_c, decls_c, &rd_c) {
        Err(e) => return step_failed(io, e, verified),
        Ok(p) => p,
    };
    // ConRon.Capstone: hhole
    let holed_c: Vec<IDeclaration> = match fcompare::hole_records(&rd_c, &pers, &mut st, &prep_c.decls, 0, Vec::new()) {
        Err(e) => return step_failed(io, e, verified),
        Ok(v) => v,
    };
    // what the challenge's check keeps of its read: the reader's pins and the values' modules
    let OleanRead { decls: _, values: values_c, merged: _, homes: _, pins: pk_c } = rd_c;
    // THE SOLUTION'S CLOSURE, from the constants the challenge's records install, or all of it.
    let need: Option<Vec<NIdx>> = match &consts {
        None => None,
        Some(_) => Some(rec_keys(&prep_c.decls)),
    };
    let s_label: Vec<Name> = one_name(s_name);
    io.oleans_read_starts(&a.progress, &s_label);
    let roots_s: Vec<NIdx> = one_root(&s);
    // ConRon.Capstone: h3S
    io.read_notes_begin(&a.progress);
    let read_s = records::read_oleans(&*io, &pers, &mut st.store, &sr, &roots_s, &need, true, false);
    io.read_notes_end();
    let mut rd_s: OleanRead = match read_s {
        Err((e, line)) => return check_main::oleans_failed(io, e, line, &s_label, verified),
        Ok(rd) => rd,
    };
    // a solution importing its challenge is no solution
    if holds_module(&rd_s.values, &c) {
        io.note(&Note::NotSolution(name::dup(s_name), name::dup(c_name), verified));
        return 1;
    }
    let records_s = rd_s.decls.len();
    let decls_s = core::mem::replace(&mut rd_s.decls, Vec::new());
    // ConRon.Capstone: h4S
    let prep_s = match prepare::prepare_d(&pers, &mut st, pre, decls_s, &rd_s) {
        Err(e) => return step_failed(io, e, verified),
        Ok(p) => p,
    };
    let OleanRead { decls: _, values: values_s, merged: _, homes: _, pins: pk_s } = rd_s;
    if prep_s.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prep_s.hoisted);
    }
    // ConRon.Capstone: hpins (`--pins`/`--no-pins` are outside the theorems)
    let pins: Vec<NatOpPinSet> = match check_main::pins_for_run(io, a) {
        None => return 3,
        Some(ps) => ps,
    };
    // ConRon.Capstone: h5
    let ipins = match checker::intern_all_pins(&pers, &mut st, &pins, &a.max_nat_size) {
        Err(e) => return step_failed(io, e, verified),
        Ok(p) => p,
    };
    let jobs: u64 = check_main::jobs_for_run(io, a);
    let s_text: Vec<u32> = name::render(s_name);
    // ConRon.Capstone: h6S, h7S, h8S
    let ix_s = match check_main::check_phase_olean(io, &pers, &mut st, &mode, &ipins, &prep_s.decls, &pk_s, &values_s, &sr, None, jobs, records_s, prep_s.synthesised) {
        Err((e, i)) => return compare_json::solution_failed(io, &pers, st, prep_s.decls, e, i, &s_text, verified),
        Ok(ix) => ix,
    };
    // THE CHALLENGE'S CLOSURE, checked with the solution.
    if prep_c.hoisted.len() > 0 {
        io.hoisted(&pers, &st.store, &prep_c.hoisted);
    }
    // ConRon.Capstone: hside
    let recs_c: Vec<IDeclaration> = match justify::side_records(&pers, &mut st, &holed_c, 0, Vec::new()) {
        Err(e) => return step_failed(io, e, verified),
        Ok(v) => v,
    };
    // ConRon.Capstone: hsol
    let sol: Solution = justify::solution_of(ix_s, &recs_c);
    // ConRon.Capstone: h6, h7, h8
    let verdict = check_main::check_phase_olean(io, &pers, &mut st, &mode, &ipins, &recs_c, &pk_c, &values_c, &cr, Some(&sol), jobs, records_c, prep_c.synthesised);
    compare_json::compare_verdict(io, &pers, st, prep_s.decls, prep_c.decls, recs_c, sol, verdict, records_c, &s_text, records_s, verified)
}
