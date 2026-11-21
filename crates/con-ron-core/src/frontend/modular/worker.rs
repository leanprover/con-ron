//! `ConLeche/Driver/Worker.lean` — a worker's reads and its own records (task
//! #166).
//!
//! The type a worker's phases 1–4 build; the worker itself is ported by its
//! own lane.

use crate::arena::env::IDeclaration;
use crate::arena::handle::NIdx;
use crate::frontend::modular::reach::Reach;
use crate::frontend::olean::index::WorkerReads;
use crate::frontend::olean::lazy::Loaded;
use crate::frontend::olean::module::Expo;
use crate::frontend::olean::records::ValueCache;

/// con-leche: ConLeche/Driver/Worker.lean:271-289 WorkerRead
/// **What a worker has read and checked before its jobs.**
pub struct WorkerRead {
    /// the module's private view, loaded
    pub home: Loaded,
    /// each own constant's exported level (`check_views`)
    pub expo: Vec<Expo>,
    /// the header fixpoint, the name index, the clash rule's copies
    pub reads: WorkerReads,
    /// the own records, as the emission gives them
    pub emitted: Vec<IDeclaration>,
    /// the own records, in the order they are checked
    pub own: Vec<IDeclaration>,
    /// the context
    pub reach: Reach,
    /// the records moved by the ground hoist
    pub hoisted: Vec<NIdx>,
    /// the home's region, which the theorems' values are read from
    pub values: ValueCache,
}
