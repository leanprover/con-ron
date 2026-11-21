//! `ConLeche/Driver/Reach.lean` — a worker's context: the reach of a module,
//! its completion, the capture check (task #166).
//!
//! The types the reach is built on; the reach itself is ported by its own
//! lane.

use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::frontend::olean::reads::NamePosition;
use crate::frontend::olean::view::OLeanLevel;
use crate::kernel::name;
use crate::arena::monad::AState;
use crate::arena::store::PersTier;
use crate::frontend::olean::files::{OleanFs, Roots};
use crate::frontend::olean::index::WorkerReads;
use crate::frontend::olean::spec::OleanPins;
use crate::kernel::core_types::CheckError;
use crate::ron::hashmap::{Dup, Eq2, Hashable};
use crate::ron::hashmap2::HashMap2;

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// **A part of a view**: a module and a level.
pub struct PartKey {
    pub module: NIdx,
    pub level: OLeanLevel,
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// `OLeanLevel`'s derived `Hashable`'s word: the constructor's index.
pub fn level_index(l: &OLeanLevel) -> u64 {
    match l {
        OLeanLevel::Exported => 0,
        OLeanLevel::Server => 1,
        OLeanLevel::Private => 2,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// A level, copied.
pub fn level_dup(l: &OLeanLevel) -> OLeanLevel {
    match l {
        OLeanLevel::Exported => OLeanLevel::Exported,
        OLeanLevel::Server => OLeanLevel::Server,
        OLeanLevel::Private => OLeanLevel::Private,
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// The derived `Hashable`: `mixHash` over the fields.
impl Hashable for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn hash64(&self) -> u64 {
        name::mix_hash(self.module.hash64(), name::nat_hash(level_index(&self.level)))
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// The derived `BEq`.
impl Eq2 for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn eq2(&self, other: &PartKey) -> bool {
        self.module.eq2(&other.module) && level_index(&self.level) == level_index(&other.level)
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
/// A part key, copied.
impl Dup for PartKey {
    /// con-leche: ConLeche/Driver/Reach.lean:164-168 PartKey
    fn dup2(&self) -> PartKey {
        PartKey { module: self.module.dup2(), level: level_dup(&self.level) }
    }
}

/// con-leche: ConLeche/Driver/Reach.lean:170-173 Spot
/// **A copy of a name**: the part holding it and its name position there.
pub struct Spot {
    pub part: PartKey,
    pub pos: NamePosition,
}

/// con-leche: ConLeche/Driver/Reach.lean:923-930 Reach
/// **What the reach gives**: the context's records with their homes, the
/// completed names with the homes that located them, and its counts.
pub struct Reach {
    pub ctx: Vec<IDeclaration>,
    pub homes: Vec<NIdx>,
    pub completed: Vec<(NIdx, NIdx)>,
    pub searches: u64,
    pub inferred: u64,
}

// ---------------------------------------------------------------------------
// L3's STUB of lane L2's signatures (task #166): dropped when L2 integrates.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Driver/Reach.lean:94-95 recordReads
/// STUB (lane L2 ports it): what a record reads.
pub fn record_reads(pers: &PersTier, st: &mut AState, d: &IDeclaration) -> Result<Vec<NIdx>, CheckError> {
    crate::frontend::nat_op_ground::decl_used_consts(pers, st, d)
}

/// con-leche: ConLeche/Driver/Reach.lean:871-873 ownerMap
/// STUB (lane L2 ports it): the record of each name of a context.
pub fn owner_map(pers: &PersTier, st: &mut AState, ds: &Vec<IDeclaration>) -> Result<HashMap2<NIdx, u64>, CheckError> {
    let mut m: HashMap2<NIdx, u64> = HashMap2::new();
    let mut j = 0usize;
    while j < ds.len() {
        match crate::arena::install::decl_names(pers, st, &ds[j]) {
            Err(e) => return Err(e),
            Ok(ns) => {
                let mut i = 0usize;
                while i < ns.len() {
                    m.insert(ns[i].dup2(), j as u64);
                    i += 1;
                }
            }
        }
        j += 1;
    }
    Ok(m)
}

/// con-leche: ConLeche/Driver/Reach.lean:934-961 reach
/// STUB (lane L2 ports it): the reach of a module.
#[allow(unused_variables)]
#[allow(clippy::too_many_arguments)]
pub fn reach<F: OleanFs>(
    fs: &F,
    pk: &OleanPins,
    pers: &PersTier,
    st: &mut AState,
    sp: &Roots,
    m: &NIdx,
    wr: &WorkerReads,
    own: &HashMap2<NIdx, bool>,
    roots: &Vec<NIdx>,
) -> Result<Reach, CheckError> {
    Err(crate::kernel::core_types::internal({ const M: [u32; 4] = [115, 116, 117, 98]; crate::kernel::core_types::code_points(&M) }))
}
