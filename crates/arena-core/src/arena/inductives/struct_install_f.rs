//! `arena::inductives::struct_install_f` — the `F` names.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StructInstallF.lean`.
//!
//! `ConLeche/Kernel/Inductives/StructInstallF.lean` is `StructInstall.lean`'s
//! two functions over an `FEnv`, plus the `StructWalkers` record the cached
//! driver fills with its memoised walks.  The arena has ONE environment type
//! (task #97c's deviation 1), so the `F` twins ARE
//! `arena::inductives::struct_install`'s; what is left for this module is the
//! `F`-suffixed NAMES — which P4d's reader, the census and anyone reading
//! con-leche's `Cached` tier beside the arena will look for.  The Lean twin
//! makes them `abbrev`s so that nothing can drift; the Rust makes them
//! one-line delegations, which is the same thing after inlining and is what
//! `arena::fenv` already does for `Core.lean`'s seven.
//!
//! **`StructWalkers` has no twin.**  It is a record of two FUNCTION VALUES
//! whose only purpose is to let con-leche's cached driver substitute memoised
//! walks for the pure ones at run time (`ConLeche.Cached.structWalkersC`).
//! The arena has no such seam: its `consts_resolve_f_fast` and
//! `struct_proj_bodies` ARE the memoised walks, there is one of each, and a
//! record of two closures is exactly what DESIGN.md §3.4 forbids in code
//! Aeneas must translate.  So `StructWalkers` and `StructWalkers.plain` are
//! census class (P) here — apparatus of a tier the port does not have — and
//! every `w.resolve` / `w.projBodies` of the `F` files is the arena's own
//! function at the call site.

use super::struct_install;
use crate::arena::env::{IConstantVal, IFEnv};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::AState;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstallF.lean:34 checkStructDomsAtF`
/// — `checkStructDomsAt` through the index; the same function (module note).
pub fn check_struct_doms_at_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    off: u64,
    fvs: &Vec<EIdx>,
    doms: &Vec<EIdx>,
    k: u64,
) -> Result<(), CheckError> {
    struct_install::check_struct_doms_at(pers, vis, st, mode, fe, off, fvs, doms, k)
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstallF.lean:39 checkStructDomsAtFA`
/// — `checkStructDomsAtF` over arrays; the same function at `List.toArray`,
/// and over a `Vec` there is nothing left to distinguish.
pub fn check_struct_doms_at_fa(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    off: u64,
    fvs: &Vec<EIdx>,
    doms: &Vec<EIdx>,
    k: u64,
) -> Result<(), CheckError> {
    struct_install::check_struct_doms_at(pers, vis, st, mode, fe, off, fvs, doms, k)
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstallF.lean:44 checkStructProjTableF`
/// — `checkStructProjTable` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn check_struct_proj_table_f(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    res_sort: &LIdx,
    guards: Vec<LIdx>,
    off: u64,
    cv_ca: &IConstantVal,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    struct_install::check_struct_proj_table(
        pers,
        st, t, c, lps, n_p, n_f, res_sort, guards, off, cv_ca, fe,
    )
}
