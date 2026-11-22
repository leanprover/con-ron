//! `driver::compare_module` — con-leche's `Driver/CompareModule.lean`: the
//! compare worker (`--olean --module --compare`), a challenge as one more
//! module of a modular run, and the graph check of a compared run
//! (`--check-graph --compare`), over `CheckerIo` (DESIGN.md §3.9, task #171).
//!
//! The compare worker is the worker of the challenge `C` (`worker::check_module`)
//! with `import all S` added to its header, every module read through the
//! solution's lookup (the trusted path, then the search path).  Before it, and
//! before the compared graph check, with a trusted path the challenge's closure
//! is walked through the trusted path alone (`chal_walk`): a module of it only
//! the search path holds is invalid input.  The walk is its verdict only, so it
//! runs on a store of its own; the run's store is the capstone's, untouched by
//! it.

use crate::arena::handle::NIdx;
use crate::arena::monad;
use crate::arena::monad::AState;
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::driver::cli;
use crate::driver::cli::Args;
use crate::driver::compare;
use crate::driver::graph;
use crate::frontend::checker_io::CheckerFs;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::modular::compare_module as mcompare;
use crate::frontend::modular::graph as mgraph;
use crate::frontend::olean::files;
use crate::frontend::olean::spec;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name::Name;

/// con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk
/// **The challenge's closure through the trusted path alone**
/// (`--trusted-search-path`, its verdict only), on a store of its own: where a
/// module of it is not there, why (invalid where the search path holds it, as
/// in `--olean --compare`); none where the walk succeeds or no trusted path is
/// given.
pub fn chal_walk<F: CheckerFs>(fs: &F, trusted: &Vec<Vec<u32>>, path: &Vec<Vec<u32>>, c_name: &Name) -> Option<CheckError> {
    if trusted.len() == 0 {
        return None;
    }
    let mut st = AState::empty();
    let pers = PersTier::empty();
    match pins::intern_reserved_pins(&pers, &mut st) {
        Err(e) => return Some(e),
        Ok(()) => (),
    }
    let pk = match spec::olean_pins(&pers, &mut st.store) {
        Err(e) => return Some(e),
        Ok(p) => p,
    };
    let c: NIdx = match monad::intern_name(&pers, &mut st, c_name) {
        Err(e) => return Some(e),
        Ok(h) => h,
    };
    let cr = files::roots_of_path(cli::push_files(Vec::new(), trusted, 0));
    match mcompare::chal_walk(fs, &pk, &pers, &mut st.store, &cr, &c) {
        Ok(()) => None,
        Err(e) => match compare::fallback_only(fs, &pers, &mut st, trusted, path, &c) {
            Some(why) => Some(core_types::invalid(why)),
            None => Some(e),
        },
    }
}

/// con-leche: ConLeche/Driver/CompareModule.lean:49-59 checkCmpModuleG
/// **The compare worker** (`--olean --module --compare`): the challenge's
/// closure walked through the trusted path alone (`chal_walk`), then the worker
/// of `c_name` with the solution `s_name` added to its header, every module read
/// through the solution's lookup; the exit code.
pub fn check_cmp_module<I: CheckerIo>(io: &mut I, a: &Args, c_name: &Name, s_name: &Name) -> u8 {
    match chal_walk(&*io, &a.trusted_path, &a.search_path, c_name) {
        Some(e) => return graph::graph_failed(io, e),
        None => (),
    }
    let sp = cli::sol_roots(a);
    crate::driver::worker::check_module(io, a, &sp, c_name, Some(s_name))
}

/// con-leche: ConLeche/Driver/CompareModule.lean:61-71 checkGraphCmpG
/// **The graph check of a compared run** (`--check-graph --compare`): with a
/// trusted path, the challenge's closure first, through the challenge's lookup
/// alone (`chal_walk`); then the graph of both closures through the solution's
/// lookup, the solution added to the challenge's header; the accept line or the
/// error's.
pub fn check_graph_cmp<I: CheckerIo>(io: &mut I, a: &Args, c_name: &Name, s_name: &Name) -> u8 {
    match chal_walk(&*io, &a.trusted_path, &a.search_path, c_name) {
        Some(e) => return graph::graph_failed(io, e),
        None => (),
    }
    let mut st = AState::empty();
    let pers = PersTier::empty();
    let pk = match graph::graph_start(io, &pers, &mut st) {
        Err(c) => return c,
        Ok(pk) => pk,
    };
    // ConRon.MainTheorem.Stages: hroots
    let c: NIdx = match monad::intern_name(&pers, &mut st, c_name) {
        Err(e) => return graph::graph_failed(io, e),
        Ok(h) => h,
    };
    let s: NIdx = match monad::intern_name(&pers, &mut st, s_name) {
        Err(e) => return graph::graph_failed(io, e),
        Ok(h) => h,
    };
    let roots: Vec<NIdx> = compare::one_root(&c);
    let sp = cli::sol_roots(a);
    // ConRon.MainTheorem.Stages: hgraph
    match mgraph::graph_of(&*io, &pk, &pers, &mut st.store, &sp, &roots, &Some((c, s))) {
        Err(e) => graph::graph_failed(io, e),
        Ok(cg) => {
            io.graph_accepted(&cg);
            0
        }
    }
}
