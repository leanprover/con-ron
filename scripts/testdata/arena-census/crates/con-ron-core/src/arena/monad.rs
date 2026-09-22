//! The fixture's `arena::monad`.

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Monad.lean derivedE`
pub fn derived_e(h: &EIdx) -> u64 {
    0
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Monad.lean viewApp`
pub fn view_app(h: &EIdx) -> Option<(EIdx, EIdx)> {
    None
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Monad.lean internE`
pub fn intern_e(v: &ENodeView) -> EIdx {
    EIdx::default()
}
