//! `ConLeche/Kernel/TrustPins.lean` — the pinned defining expressions of the
//! toolchain's `Lean.reduceNat` / `Lean.reduceBool` opaques: the plain
//! identity functions.
//!
//! At install (`checker::check_reduce_pin`) the stream's stored opaque value
//! is compared against the pin by definitional equality — drift declines,
//! never silently — and the identity certificate `value x ≡ x` is what the
//! model consumes.
//!
//! Nothing here reads the compiling environment (con-leche task #273): the
//! pin has been `fun b => b` on every toolchain that had the opaques, so it
//! is written down once.

use crate::kernel::basis_builder;
use crate::kernel::core_types;
use crate::kernel::expr::Expr;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/TrustPins.lean:42-43 reduceBoolDeclPin
/// `Lean.reduceBool`'s pinned value: `fun (b : Bool) => b`.
pub fn reduce_bool_decl_pin() -> Expr {
    basis_builder::lm(
        basis_builder::cnst(basis_builder::bn({ const S: [u32; 4] = [66, 111, 111, 108]; core_types::code_points(&S) }), Vec::new()),
        basis_builder::bv(0),
    )
}

/// con-leche: ConLeche/Kernel/TrustPins.lean:45-46 reduceNatDeclPin
/// `Lean.reduceNat`'s pinned value: `fun (n : Nat) => n`.
pub fn reduce_nat_decl_pin() -> Expr {
    basis_builder::lm(
        basis_builder::cnst(basis_builder::bn({ const S: [u32; 3] = [78, 97, 116]; core_types::code_points(&S) }), Vec::new()),
        basis_builder::bv(0),
    )
}
