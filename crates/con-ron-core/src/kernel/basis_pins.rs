//! **A stub, to be folded into task #22's `basis_tables.rs`.**
//!
//! `ConLeche/Kernel/BasisA.lean` holds the *annotated* pinned basis blocks —
//! `eqA`, `natA`, `punitA`, …, `quotSoundA` and `BasisKind.declsA` — and it
//! does not *write* them: they are computed from the raw pins
//! (`ConLeche/Kernel/Basis/*`) by the checker's own annotation pass while the
//! module elaborates (`#annotate_basis`, `ConLeche/Kernel/BasisGen.lean`).
//! Porting them therefore means *generating a table*, which is task #22's
//! job; this module is what task #24's declaration checker needs in the
//! meantime, and task #22 should delete it in favour of `basis_tables.rs`.
//!
//! ## What the stubs do, and why that is sound
//!
//! Two of the nineteen annotated pins are consumed by an **exact**
//! `ConstantInfo` comparison rather than through `ConstantVal.matchesPin`:
//! `env.find? eqName = some eqA` and `env.find? natName = some natA`.
//! `matchesPin` erases every binder's prop-ness datum (`Expr.erasePw`), which
//! is the *only* thing annotation changes in a raw pin, so every other pin is
//! compared against its raw form in `std_axioms`/`trust_axioms` with no table
//! at all (see those modules' notes).  These two are not, so they are spelled
//! here as predicates on the stored constant, and the stubs answer `false`.
//!
//! A `false` makes every pinned-`Eq`/`Nat`-basis guard **decline** — the
//! verdict con-leche itself gives a stream that never installed the pinned
//! basis ("quotient basis requires the pinned Eq basis", "projection iota
//! requires the pinned Eq basis", `divModEnvGuard`, `stdAxiomOk`,
//! `ofReduceAxOk`).  Declining where the Lean succeeds can only make the Rust
//! *reject*, which is sound for the accept direction (DESIGN.md §1) and is
//! exactly the shape task #24's `nat_op_pins` stub takes.
//!
//! `decls_a` likewise returns an empty block, so `.basisDecl` installs
//! nothing and every later declaration that mentions a basis constant fails
//! `consts_resolve` — again a decline, never an accept.

use crate::kernel::env::{BasisKind, ConstantInfo};
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Eq` type former?  This is
/// how the port spells `env.find? eqName = some eqA`, which is an exact
/// `ConstantInfo` equality against a generated pin.
///
/// **Stub**: the annotated pin is generated at elaboration time; the table is
/// task #22's.  Answering `false` declines, as con-leche does for a stream
/// without the pinned `Eq` basis (see the module note).
pub fn is_pinned_eq_basis(ci: &ConstantInfo) -> bool {
    let _ = ci;
    false
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Nat` type former
/// (`env.find? natName = some natA`, `reduceElemOk`)?
///
/// **Stub**: see `is_pinned_eq_basis` and the module note.
pub fn is_pinned_nat_basis(ci: &ConstantInfo) -> bool {
    let _ = ci;
    false
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// The annotated constants of one basis block, in dependency order — what
/// `checkDecl`'s `.basisDecl` arm folds `installBasisDecl` over.
///
/// **Stub**: returns the empty block, so the fold installs nothing and the
/// pin loop is exercised with zero entries (task #22 supplies the table).
pub fn decls_a(kind: &BasisKind) -> Vec<ConstantInfo> {
    let _ = kind;
    Vec::new()
}
