//! The fixture's `arena::checker` and `arena::promote`.

/// con-leche: ConLeche/Kernel/Checker.lean:100-200 checkDecl
/// Lean twin: `proof/ConRon/Arena/Checker.lean checkDecl`
pub fn check_decl(pd: &IDeclaration) {}

/// con-leche: ConLeche/Kernel/Checker.lean:240-300 checkDeclsPure
/// Lean twin: `proof/ConRon/Arena/Checker.lean checkDeclsPure`
pub fn check_decls_pure(ds: &Vec<IDeclaration>) {}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Promote.lean promoteN`
pub fn promote_n(n: &NIdx) -> NIdx {
    n.clone()
}

/// con-leche: none — arena infrastructure
/// Lean twin: `proof/ConRon/Arena/Promote.lean PMemo.empty`
pub fn empty() -> PMemo {
    PMemo::default()
}
