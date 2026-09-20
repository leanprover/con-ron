//! `arena::inductives` — the inductive block's dispatch (DESIGN.md §8, task
//! #97-P4d part 2).
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives.lean`: the `.indDecl` arm of
//! con-leche's `checkDecl`, from the declared parameter count down to the two
//! install routes.  This is the single entry point `arena::checker`'s
//! declaration checker calls, and everything under `arena/inductives/` is what
//! it calls.
//!
//! What is NOT here is the **pinned basis block** (`basis_pin_hit`): a stream's
//! `Nat` block arrives as an ordinary `indDecl` and is recognised before this,
//! in the declaration checker, because its install is `check_basis_decl`'s and
//! not an inductive route's.
//!
//! **This file is the seam of task #97-P4d's two halves.**  Part 1 (the
//! declaration checker) created it with this signature and a body that
//! declines; part 2 replaces the body with the parameter check and the
//! two-route dispatch (`ind_params_ok`, `native_parts`, `check_native`,
//! `check_modeled`) and adds the modules under `arena/inductives/`.  Nothing
//! above this module sees the difference.

use crate::arena::env::{IConstantInfo, IFEnv};
use crate::arena::monad::AState;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"arena: inductive install not yet wired"`, as code points.
pub const M_NOT_WIRED: [u32; 38] = [
    97, 114, 101, 110, 97, 58, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 105,
    110, 115, 116, 97, 108, 108, 32, 110, 111, 116, 32, 121, 101, 116, 32, 119, 105, 114,
    101, 100
];

/// con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl
/// Lean twin: `proof/ConRon/Arena/Inductives.lean:38-44 checkIndDecl` — the
/// `.indDecl` arm: **the declared parameter count first, and for both routes**
/// (con-leche task #228; `indParamsOk` is official's own check, one-sided, so a
/// `false` is official's reject), then ONE ROUTE (task #210) — the fixpoint
/// route takes every block its recogniser recognises, and everything else is
/// the modeled path's, which DECLINES, naming the block, when there is no
/// model.
///
/// **The body is task #97-P4d part 2's.**  Until it lands the arm declines
/// with a `NotImplemented`, which can only make the Rust *reject* and is sound
/// for the accept direction (DESIGN.md §1); the Lean twin's own part-1 sweep
/// declined here in exactly the same way ("declined: arena: inductive install
/// not yet wired", 287 of task #97d's 348 fixtures).
pub fn check_ind_decl(
    mode: CheckMode,
    fe: IFEnv,
    block: Vec<IConstantInfo>,
    num_params: u64,
    st: &mut AState,
) -> Result<IFEnv, CheckError> {
    let _ = mode;
    let _ = fe;
    let _ = block;
    let _ = num_params;
    let _ = st;
    Err(CheckError::NotImplemented(code_points(&M_NOT_WIRED)))
}
