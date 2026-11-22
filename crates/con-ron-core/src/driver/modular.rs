//! `driver::modular` — con-leche's `Driver/Modular.lean`: `--olean --modular`,
//! every module of a closure checked as its worker checks it, in one process
//! (DESIGN.md §3.9, task #171), over `CheckerIo`.
//!
//! The graph (`graph::graph_of`, as `--check-graph`), then every module of it
//! its worker from fresh start values (`worker::check_module_in`) on the
//! instance's code map, every module run; the run's verdict: exit 0 exactly
//! when every module's is, else the code of the first module, in the graph's
//! order, that is not.

use crate::arena::monad;
use crate::arena::monad::AState;
use crate::arena::store::PersTier;
use crate::driver::check_main;
use crate::driver::check_main::Note;
use crate::driver::cli::Args;
use crate::driver::graph;
use crate::driver::worker;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::checker_io::CodeStep;
use crate::frontend::checker_io::WorkerNotes;
use crate::frontend::modular::graph as mgraph;
use crate::frontend::olean::files::Roots;
use crate::frontend::olean::spec::ImportRec;
use crate::frontend::pace::pace_on;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::nat::Nat;
use crate::arena::handle::NIdx;

/// con-leche: ConLeche/Driver/Modular.lean:74-80 modularStep
/// **A module of the run**: the worker at the module at a position of the
/// graph's order.
pub struct ModularStep<'a> {
    /// the graph's modules, in its order
    pub names: &'a Vec<Name>,
    /// the lookup every module is read through
    pub sp: &'a Roots,
    /// `--verified`
    pub verified: bool,
    /// `--max-nat-size`
    pub max_nat_size: &'a Nat,
    /// `--no-pins`
    pub no_pins: bool,
}

/// con-leche: ConLeche/Driver/Modular.lean:74-80 modularStep
impl<'a, F: CheckerFs + WorkerNotes> CodeStep<F> for ModularStep<'a> {
    /// con-leche: ConLeche/Driver/Modular.lean:64-73 stepCode
    /// The module's worker, to its exit code.
    fn code(&self, fs: &F, k: usize) -> u8 {
        if k < self.names.len() {
            worker::check_module_in(fs, self.sp, &self.names[k], self.verified, self.max_nat_size, self.no_pins)
        } else {
            3
        }
    }
}

/// con-leche: none — the graph's modules, by name
/// **The modules of a graph**, read back to names, in its order.
pub fn graph_names(pers: &PersTier, st: &AState, c: &Vec<(NIdx, Vec<ImportRec>)>) -> Result<Vec<Name>, crate::kernel::core_types::CheckError> {
    let mut out: Vec<Name> = Vec::new();
    let mut i = 0usize;
    while i < c.len() {
        match monad::read_name(pers, st, &c[i].0) {
            Err(e) => return Err(e),
            Ok(n) => out.push(n),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
/// The first module, in the graph's order, whose code is not 0.
pub fn first_failure(codes: &Vec<u8>) -> Option<usize> {
    let mut k = 0usize;
    while k < codes.len() {
        if codes[k] != 0 {
            return Some(k);
        }
        k += 1;
    }
    None
}

/// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
/// How many modules' codes are not 0.
pub fn failures(codes: &Vec<u8>) -> u64 {
    let mut n: u64 = 0;
    let mut k = 0usize;
    while k < codes.len() {
        if codes[k] != 0 {
            n += 1;
        }
        k += 1;
    }
    n
}

/// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
/// **The run's verdict** off the modules' codes: the accept line and 0 when every
/// one is 0, else the failure line and the code of the first in the graph's
/// order that is not.
pub fn modular_verdict<I: CheckerIo>(io: &mut I, codes: &Vec<u8>, names: &Vec<Name>, verified: bool) -> u8 {
    match first_failure(codes) {
        None => {
            io.note(&Note::ModularAccepted(codes.len() as u64, verified));
            0
        }
        Some(k) => {
            io.note(&Note::ModularFailed(failures(codes), codes.len() as u64, name::dup(&names[k]), verified));
            codes[k]
        }
    }
}

/// con-leche: ConLeche/Driver/Modular.lean:90-137 checkModularG
/// **The one-process mode** (`--olean --modular`): the root's closure by the
/// graph check through `sp`, then every module of it on the instance's code
/// map, up to `--jobs` at a time (fewer where no more can be started), each its
/// worker on one thread; the run's verdict.
pub fn check_modular<I: CheckerIo>(io: &mut I, a: &Args, roots: &Vec<Name>, sp: &Roots) -> u8 {
    let names: Vec<Name> = {
        let mut st = AState::empty();
        let pers = PersTier::empty();
        let pk = match graph::graph_start(io, &pers, &mut st) {
            Err(c) => return c,
            Ok(pk) => pk,
        };
        // ConRon.Capstone: hroots
        let rs = match check_main::intern_names(&pers, &mut st, roots) {
            Err(e) => return graph::graph_failed(io, e),
            Ok(rs) => rs,
        };
        // ConRon.Capstone: hgraph
        let c = match mgraph::graph_of(&*io, &pk, &pers, &mut st.store, sp, &rs, &None) {
            Err(e) => return graph::graph_failed(io, e),
            Ok(c) => c,
        };
        match graph_names(&pers, &st, &c) {
            Err(e) => return graph::graph_failed(io, e),
            Ok(ns) => ns,
        }
    };
    let n = names.len();
    if pace_on(&a.progress) {
        io.note(&Note::ModularGraph(n as u64));
    }
    let jobs: u64 = check_main::jobs_for_run(io, a);
    let threads = check_main::workers_for(jobs, n);
    let r = {
        let step = ModularStep { names: &names, sp, verified: a.verified, max_nat_size: &a.max_nat_size, no_pins: a.no_pins };
        io.par_map_codes(&step, n, threads)
    };
    let codes = match r {
        Err(m) => {
            io.note(&Note::ModularThreads(m));
            return 3;
        }
        Ok(cs) => cs,
    };
    if pace_on(&a.progress) {
        io.note(&Note::ModularDone);
    }
    modular_verdict(io, &codes, &names, a.verified)
}
