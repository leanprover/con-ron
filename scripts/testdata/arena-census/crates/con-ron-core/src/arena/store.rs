//! The fixture's `arena::store`.
//!
//! Three `impl` blocks, and two of them define a method called `find`: the
//! BARE name is not the T2 subject, `<receiver>_<fn>` is.  `Tbl::find` has
//! `tbl_find_abs` and `EStore::find` has nothing, which is a verdict the
//! census can only reach by reading the enclosing `impl`.

pub struct Tbl {}

impl Tbl {
    /// con-leche: none — arena infrastructure
    /// Lean twin: `proof/ConRon/Arena/Store.lean Tbl.find?`
    pub fn find(&self, a: &A) -> Option<I> {
        None
    }
}

pub struct EStore {}

impl EStore {
    /// con-leche: none — arena infrastructure
    /// Lean twin: `proof/ConRon/Arena/Store.lean EStore.find?`
    pub fn find(&self, v: &ENodeView) -> Option<EIdx> {
        None
    }

    /// con-leche: none — arena infrastructure
    /// Lean twin: `proof/ConRon/Arena/Store.lean EStore.viewApp`
    pub fn view_app(&self, i: &EIdx) -> Option<(EIdx, EIdx)> {
        None
    }

    /// con-leche: none — arena infrastructure
    /// Lean twin: `proof/ConRon/Arena/Store.lean EStore.dropScratch`
    pub fn drop_scratch(self) -> EStore {
        self
    }

    /// con-leche: none — arena infrastructure
    /// Lean twin: `proof/ConRon/Arena/Store.lean EStore.derOfBVar`
    pub fn der_of_bvar(&self, i: u64) -> u64 {
        0
    }
}
