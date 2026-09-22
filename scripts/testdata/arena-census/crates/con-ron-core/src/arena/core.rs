//! The fixture's `arena::core`.  `iota_rec` and `iota_rec_at` BOTH cite the
//! same twin, and only one of them has a `_refines`: the row reads "cited,
//! one of two stated".

/// con-leche: ConLeche/Kernel/Core.lean:900-930 isBoolTrue
/// Lean twin: `proof/ConRon/Arena/Core.lean isBoolTrue`
pub fn is_bool_true(h: &EIdx) -> bool {
    false
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Core.lean flushCaches`
pub fn flush_caches() {}

/// con-leche: ConLeche/Kernel/Core.lean:1200-1260 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean iotaRec`
pub fn iota_rec(h: &EIdx) -> Option<EIdx> {
    None
}

/// con-leche: ConLeche/Kernel/Core.lean:1200-1260 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean iotaRec` — the second call site.
pub fn iota_rec_at(h: &EIdx) -> Option<EIdx> {
    None
}
