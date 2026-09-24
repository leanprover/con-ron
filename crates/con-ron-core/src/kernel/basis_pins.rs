//! `ConLeche/Kernel/BasisA.lean`'s **two exactly-compared pins**, over task
//! #22's generated table.
//!
//! `BasisA.lean` holds the annotated pinned basis blocks — `eqA`, `natA`,
//! `punitA`, …, `quotSoundA` and `BasisKind.declsA` — and it does not *write*
//! them: they are computed from the raw pins (`ConLeche/Kernel/Basis/*`) by
//! the checker's own annotation pass while the module elaborates
//! (`#annotate_basis`, `ConLeche/Kernel/BasisGen.lean`).  The *values* are
//! therefore carried as generated source in
//! `crate::kernel::basis_tables` (task #22), and `BasisKind.declsA` is
//! `basis_tables::basis_decls_a`, which is what `checkDecl`'s `.basisDecl`
//! arm folds `installBasisDecl` over.
//!
//! ## What is left for this module
//!
//! Two of the nineteen annotated pins are consumed by an **exact
//! `ConstantInfo` comparison** rather than through
//! `ConstantVal.matchesPin`: `env.find? eqName = some eqA`
//! (`Kernel/StdAxioms.lean:346`, `Kernel/TrustAxioms.lean:193`,
//! `Kernel/Checker.lean:284,528`, `Kernel/DeclCheck.lean:243,299,313,744`,
//! `Kernel/Inductives/Modeled.lean:448,493,603,653`,
//! `Cached/CheckerC.lean:143`, `Cached/ParsedC.lean:228`) and
//! `env.find? natName = some natA` (`Kernel/TrustAxioms.lean:180`,
//! `Kernel/DeclCheck.lean:290`).  `matchesPin` erases every binder's
//! prop-ness datum (`Expr.erasePw`), which is the *only* thing annotation
//! changes in a raw pin, so every other pin is compared against its raw form
//! in `std_axioms`/`trust_axioms` with no table at all (those modules'
//! notes).  These two are not: they read the stored capabilities
//! (`IndCaps`, `ruleK := true` on `Eq`) and the whole constant, so they need
//! the annotated value and the derived `DecidableEq` of
//! `Kernel/Env.lean` — which is `env::constant_info_beq`.
//!
//! The comparison con-leche uses is the derived structural one.  A grep of
//! the implementation tree settles it: every site above spells `==` or
//! `decide (… = some …)` on `ConstantInfo`, and `ConstantInfo.canonEq`
//! (`Frontend/Export.lean:279`, which canonicalises level-parameter *names*)
//! is used by the frontend alone and never by the kernel.
//!
//! Each pin is the **first** constant of its annotated block, which is the
//! install order `BasisKind.declsA` fixes (`.eqK => [eqA, eqReflA, eqRecA]`,
//! `.natK => [natA, natZeroA, natSuccA, natRecA]`).  Reading it off the
//! generated table rather than spelling it a second time is what makes a
//! change upstream a *test* failure (`basis_tables`' regeneration) instead
//! of a silent verdict change.

use crate::kernel::basis_names;
use crate::kernel::basis_tables;
use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:22-28 eqRaw
/// The pinned annotated `Eq` type former, `eqA` — the head of the `.eqK`
/// block (`BasisKind.declsA .eqK = [eqA, eqReflA, eqRecA]`).
///
/// (`eqA` has no `def` line to cite: it is one entry of the
/// `#annotate_basis over []` command the first citation's range covers, so
/// that citation names no declaration.)
///
/// **`eqA = eqRaw`, and that is a fact, not an assumption** — which is why
/// the raw pin is cited here too.  `eqA` is `#annotate_basis`'s output, i.e.
/// `annotateCore .verified` applied to `eqRaw`'s type, and every binder of
/// `∀ {α : Sort u} (a b : α), Prop` has a codomain that is a `Sort` or a `∀`
/// whose datum is already `.never`, so `annotPwPi`'s head-symbol reader
/// answers `.never` at all three — the parse placeholder the raw pin
/// carries.  The test `eq_a_is_annotated` runs the port's own annotation pass
/// on the table's value and compares, so a change upstream breaks a test
/// rather than a verdict.
pub fn eq_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_eq();
    env::constant_info_dup(&block[0])
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// The pinned annotated `Nat` type former, `natA` — the head of the `.natK`
/// block (`BasisKind.declsA .natK = [natA, natZeroA, natSuccA, natRecA]`).
pub fn nat_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_nat();
    env::constant_info_dup(&block[0])
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Eq` type former?  This is
/// the `some ci = some eqA` half of `env.find? eqName = some eqA`, i.e. the
/// derived `DecidableEq (ConstantInfo)` against the table's pin.
pub fn is_pinned_eq_basis(ci: &ConstantInfo) -> bool {
    env::constant_info_beq(ci, &eq_a())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Nat` type former
/// (`env.find? natName = some natA`, `reduceElemOk`)?
pub fn is_pinned_nat_basis(ci: &ConstantInfo) -> bool {
    env::constant_info_beq(ci, &nat_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// **"The pinned `Eq` basis is installed, unmodified"** — the whole guard
/// `decide (env.find? eqName = some eqA)`, through the index.  Twelve sites
/// spell it (the module note lists them); two of those are in a pure `Bool`,
/// so a monadic "run the annotation pass now" is not available and the
/// comparison has to be against a value the core can write down.
pub fn eq_basis_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::eq_name()) {
        Some(ci) => is_pinned_eq_basis(ci),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:179-186 reduceElemOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF
/// The same for `Nat`: `decide (env.find? natName = some natA)`, the element
/// inductive an `ofReduceNat` axiom needs.
pub fn nat_basis_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::nat_name()) {
        Some(ci) => is_pinned_nat_basis(ci),
        None => false,
    }
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
