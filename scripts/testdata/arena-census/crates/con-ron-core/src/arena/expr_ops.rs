//! The fixture's `arena::expr_ops`.  Every `Lean twin:` line names a
//! definition of `proof/ConRon/Arena/**` and carries NO range: the census
//! reads the path and the name, and `scripts/twin-lines.py` owns the ranges.

/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean instantiate1Go` — the
/// DISPATCHER; the arms are the twin's own shape and cite nothing.
pub fn instantiate1_go(v: &EIdx, fuel: usize, h: &EIdx, d: usize) -> EIdx {
    v.clone()
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:150-180 instantiateList
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean instantiateList`
pub fn instantiate_list(vs: &Vec<EIdx>, h: &EIdx) -> EIdx {
    h.clone()
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean exprPtrBEq`
pub fn expr_ptr_beq(a: &EIdx, b: &EIdx) -> bool {
    a == b
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean wscopedBFast`
pub fn wscoped_b_fast(e: &EIdx) -> bool {
    true
}
