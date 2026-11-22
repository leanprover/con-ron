//! `driver::graph` — con-leche's `Driver/Graph.lean` driver: `--check-graph`, the
//! import graph of root modules' closure checked once (DESIGN.md §3.9, task
//! #171), over `CheckerIo`.
//!
//! The graph walk is the verified core's `frontend::modular::graph::graph_of`
//! over the instance's file operations: the roots' closure, its import graph
//! acyclic, every import resolved, the ranks one-to-one and decreasing along
//! every edge.  Its lines are upstream's: `graph: acyclic: N modules, E import
//! edges` on stdout, or `graph: <error>` on stderr, and the error's exit code.
//! The calls of the core are marked `ConRon.MainTheorem.Stages: <premise>`
//! (`rust_graph`).

use crate::arena::monad::AState;
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::driver::check_main;
use crate::driver::check_main::Note;
use crate::frontend::checker_io::CheckerIo;
use crate::frontend::modular::graph;
use crate::frontend::olean::files::Roots;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::OleanPins;
use crate::kernel::core_types::CheckError;
use crate::kernel::name::Name;

/// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
/// A graph walk's failure: its line, and its exit code.
pub fn graph_failed<I: CheckerIo>(io: &mut I, e: CheckError) -> u8 {
    let c = check_main::exit_code(&e);
    io.note(&Note::GraphFailed(e));
    c
}

/// con-leche: none — the start of a graph walk: the reserved-name pins, the
/// reader's pins
/// **The state a graph walk starts from**: the reserved-name pins interned into
/// the fresh store (as every run's first step), the reader's known handles; a
/// failure's exit code.
pub fn graph_start<I: CheckerIo>(io: &mut I, pers: &PersTier, st: &mut AState) -> Result<OleanPins, u8> {
    // ConRon.MainTheorem.Stages: h1g
    match pins::intern_reserved_pins(pers, st) {
        Err(e) => {
            io.note(&Note::GraphPins(e));
            return Err(3);
        }
        Ok(()) => (),
    }
    // ConRon.MainTheorem.Stages: hpk
    match spec::olean_pins(pers, &mut st.store) {
        Err(e) => Err(graph_failed(io, e)),
        Ok(pk) => Ok(pk),
    }
}

/// con-leche: ConLeche/Driver/Graph.lean:240-251 checkGraphG
/// **The graph check** (`--check-graph`): the roots' closure along the lookup
/// `sp`, its graph checked (`graph_of`, no import added); the accept line or
/// the error's.
pub fn check_graph<I: CheckerIo>(io: &mut I, sp: &Roots, roots: &Vec<Name>) -> u8 {
    let mut st = AState::empty();
    let pers = PersTier::empty();
    let pk = match graph_start(io, &pers, &mut st) {
        Err(c) => return c,
        Ok(pk) => pk,
    };
    // ConRon.MainTheorem.Stages: hroots
    let rs = match check_main::intern_names(&pers, &mut st, roots) {
        Err(e) => return graph_failed(io, e),
        Ok(rs) => rs,
    };
    // ConRon.MainTheorem.Stages: hgraph
    match graph::graph_of(&*io, &pk, &pers, &mut st.store, sp, &rs, &None) {
        Err(e) => graph_failed(io, e),
        Ok(c) => {
            io.graph_accepted(&c);
            0
        }
    }
}
