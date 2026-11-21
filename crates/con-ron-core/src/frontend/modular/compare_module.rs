//! `ConLeche/Driver/CompareModule.lean` — **the compare worker: a challenge as
//! one more module of a modular run** (task #166).
//!
//! The worker of the challenge `C` is `worker::worker_read` with `import all S`
//! added to `C`'s header (`graph::solution_import`).  Before it, where a trusted
//! path is given, the challenge's closure is walked through that path alone
//! (`chal_walk`).  Whether a trusted path is given, and why a module of the
//! closure is not on it (upstream's `fallbackOnly`), are the driver's, as
//! `--olean --compare`'s are.

use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::modular::graph;
use crate::frontend::olean::files;
use crate::frontend::olean::files::OleanFs;
use crate::frontend::olean::spec::OleanPins;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::Dup;

/// con-leche: ConLeche/Driver/CompareModule.lean:36-47 chalWalk
/// **The challenge's closure through the trusted path alone** (`chal_sp`, the
/// challenge's lookup): its graph, its verdict only.
pub fn chal_walk<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, chal_sp: &files::Roots, c: &NIdx) -> Result<(), CheckError> {
    let mut roots: Vec<NIdx> = Vec::with_capacity(1);
    roots.push(c.dup2());
    match graph::graph_of(fs, pk, pers, ar, chal_sp, &roots, &None) {
        Err(e) => Err(e),
        Ok(_) => Ok(()),
    }
}
