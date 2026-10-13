//! `ConLeche/Kernel/BasisA.lean`'s **two exactly-compared pins**, over task
//! #22's generated table.
//!
//! `BasisA.lean` holds the stored pinned basis blocks — `eqA`, `natA`,
//! `emptyA`, …, `quotSoundA` and `BasisKind.declsA` — and it does not *write*
//! them: they are computed from the raw pins (`ConLeche/Kernel/Basis/*`)
//! while the module elaborates (`#stored_basis`,
//! `ConLeche/Kernel/BasisGen.lean`: the raw pin, a recursor's rules carrying
//! the install-computed fields).  The *values* are therefore carried as
//! generated source in `crate::kernel::basis_tables` (task #22), and
//! `BasisKind.declsA` is `basis_tables::basis_decls_a`, which is what
//! `checkDecl`'s `.basisDecl` arm folds `installBasisDecl` over.
//!
//! ## What is left for this module
//!
//! Two of the sixteen stored pins are consumed by an **exact `ConstantInfo`
//! comparison**: `env.find? eqName = some eqA` and `env.find? natName = some
//! natA`.  They read the stored capabilities (`IndCaps`, `ruleK := true` on
//! `Eq`) and the whole constant, so they need the stored value and the
//! derived `DecidableEq` of `Kernel/Env.lean` — which is
//! `env::constant_info_beq`.
//!
//! Each pin is the **first** constant of its stored block, which is the
//! install order `BasisKind.declsA` fixes (`.eqK => [eqA, eqReflA, eqRecA]`,
//! `.natK => [natA, natZeroA, natSuccA, natRecA]`).  Reading it off the
//! generated table rather than spelling it a second time is what makes a
//! change upstream a *test* failure (`basis_tables`' regeneration) instead
//! of a silent verdict change.

use crate::kernel::basis_tables;
use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/BasisA.lean:30-46 _
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:21-27 eqRaw
/// The pinned stored `Eq` type former, `eqA` — the head of the `.eqK`
/// block (`BasisKind.declsA .eqK = [eqA, eqReflA, eqRecA]`).
///
/// (`eqA` has no `def` line to cite: it is one entry of the
/// `#stored_basis over []` command the first citation's range covers, so
/// that citation names no declaration.)  `eqA = eqRaw`: a type former's
/// stored form is its raw pin, so the raw pin is cited too.
pub fn eq_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_eq();
    env::constant_info_dup(&block[0])
}

/// con-leche: ConLeche/Kernel/BasisA.lean:30-46 _
/// The pinned stored `Nat` type former, `natA` — the head of the `.natK`
/// block (`BasisKind.declsA .natK = [natA, natZeroA, natSuccA, natRecA]`).
pub fn nat_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_nat();
    env::constant_info_dup(&block[0])
}

#[cfg(test)]
mod tests {
    // Task #97-SWAP: this module's tests ran the `Expr`-tree checker
    // (`cached::core_c`, `cached::state_c`) over the items above, and that
    // checker is gone — the arena's is the checker now.  What the items are
    // still FOR is the pinned DATA (`lib.rs`'s "Why `Expr` survives"), which
    // `arena::intern` reads and `crates/con-ron-core/src/arena/*`'s own tests
    // and `scripts/diff-e2e.sh` exercise end to end.
}
