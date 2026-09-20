//! `arena::inductives` — the inductive block's dispatch.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives.lean`: the `.indDecl` arm of
//! con-leche's `checkDecl` (`ConLeche/Kernel/Checker.lean:566-609`), from the
//! declared parameter count down to the two routes.  This is the single entry
//! point `arena::checker`'s declaration checker calls, and everything in
//! `arena::inductives::*` is what it calls.
//!
//! What is NOT here is the **pinned basis block** (`basisPinHit`): a stream's
//! `Nat` block arrives as an ordinary `indDecl` and is recognised before this,
//! in the declaration checker, because its install is `checkBasisDecl`'s and
//! not an inductive route's.  con-leche's `checkDecl` makes that test first and
//! only then reaches the two clauses below; the arena's does the same.
//!
//! | Rust | Lean twin |
//! |---|---|
//! | `struct_parts` | `Arena/Inductives/StructParts.lean` |
//! | `sum_parts` | `Arena/Inductives/SumParts.lean` |
//! | `modeled` | `Arena/Inductives/Modeled.lean` |
//! | `struct_install` | `Arena/Inductives/StructInstall.lean` |
//! | `struct_install_f` | `Arena/Inductives/StructInstallF.lean` |
//! | `sum_install` | `Arena/Inductives/SumInstall.lean` |
//! | `sum_install_f` | `Arena/Inductives/SumInstallF.lean` |
//! | `native_parts` | `Arena/Inductives/NativeParts.lean` |
//! | `native_install` | `Arena/Inductives/NativeInstall.lean` |
//! | `native_install_f` | `Arena/Inductives/NativeInstallF.lean` |
//! | `ind_base` | **borrowed**: `Arena/{CheckerBase,Intern,StdAxioms}.lean` |
//!
//! `ind_base` is the one module with no twin of its own: it holds the
//! declaration checker's helpers until P4d-1's `arena::checker_base` lands, and
//! its own module note carries the map (the Lean side had the same file, as
//! `Arena/Inductives/Base.lean`, and task #97f deleted it once the Lean halves
//! merged).

pub mod ind_base;
pub mod modeled;
pub mod native_install;
pub mod native_install_f;
pub mod native_parts;
pub mod struct_install;
pub mod struct_install_f;
pub mod struct_parts;
pub mod sum_install;
pub mod sum_install_f;
pub mod sum_parts;

use crate::arena::env::{IConstantInfo, IFEnv};
use crate::arena::monad::{fail, AState};
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'number of parameters mismatch'`, as code points —
/// `con_ron_core::cached::parsed_c::check_ind_decl_route_c`'s own, so the
/// differential test can compare error text.
pub const M_NUM_PARAMS: [u32; 29] = [
    110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
    32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: ConLeche/Kernel/Checker.lean:440-609 checkDecl
/// Lean twin: `proof/ConRon/Arena/Inductives.lean:38-44 checkIndDecl` — the
/// `.indDecl` arm: **the declared parameter count first, and for both routes**
/// (con-leche's task #228; `indParamsOk` is official's own check, one-sided,
/// so a `false` is official's reject), then ONE ROUTE (task #210) — the
/// fixpoint route takes every block its recogniser recognises, and everything
/// else is the modeled path's, which DECLINES, naming the block, when there is
/// no model.  The dispatch is the RECOGNISER alone (task #219): a mutual or
/// nested block carries several type formers, resp. several recursors, so
/// `sumSplit` refuses it outright and no model lookup is needed to route it.
///
/// The signature is the one the coordinator froze for the two halves of P4d,
/// with the state first as `arena::monad`'s convention has it.
pub fn check_ind_decl(
    mode: &CheckMode,
    fe: IFEnv,
    block: Vec<IConstantInfo>,
    num_params: u64,
    st: &mut AState,
) -> Result<IFEnv, CheckError> {
    match ind_base::ind_params_ok(st, num_params, &block) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_NUM_PARAMS))),
        Ok(true) => match native_parts::native_parts(st, num_params, &block) {
            Err(e) => Err(e),
            Ok(Some(p)) => native_install::check_native(st, mode, &fe, &p),
            Ok(None) => modeled::check_modeled(st, mode, fe, &block),
        },
    }
}
