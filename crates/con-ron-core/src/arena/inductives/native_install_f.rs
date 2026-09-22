//! `arena::inductives::native_install_f` — the `F` names.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/NativeInstallF.lean`.
//!
//! `ConLeche/Kernel/Inductives/NativeInstallF.lean` is `NativeInstall.lean`'s
//! five `StructWalkers`-taking functions over an `FEnv`.  The arena has ONE
//! environment type and no `StructWalkers` seam (task #97c's deviation 1 and
//! `arena::inductives::struct_install_f`'s note), so the `F` twins ARE
//! `arena::inductives::native_install`'s; this module carries the `F`-suffixed
//! NAMES as one-line delegations.

use super::native_install;
use super::native_parts::{NativeParts, RecFieldKind};
use crate::arena::env::{IConstantVal, IFEnv};
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::AState;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstallF.lean:18 nativeOpenedOkF`
/// — `nativeOpenedOk` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn native_opened_ok_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe0: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    cty: &EIdx,
    n_f: u64,
    ks: &Vec<RecFieldKind>,
) -> Result<bool, CheckError> {
    native_install::native_opened_ok(pers, vis, st, fe0, t, lps, n_p, n_idx, cty, n_f, ks)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstallF.lean:22 nativeFieldsOkF`
/// — `nativeFieldsOk` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn native_fields_ok_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe0: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
) -> Result<bool, CheckError> {
    native_install::native_fields_ok(pers, vis, st, fe0, t, lps, n_p, n_idx, ctors_a, kinds)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstallF.lean:26 checkNativeRulesF`
/// — `checkNativeRules` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn check_native_rules_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe_r: &IFEnv,
    rlps: &Vec<NIdx>,
    t: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    k: u64,
    j: u64,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    native_install::check_native_rules(
        pers,
        vis,
        st, fe_r, rlps, t, lps, elim, large, n_p, n_idx, tty, ctors, rec_c, rlvls, k, j, out,
    )
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstallF.lean:30 checkNativeRecF`
/// — `checkNativeRec` through the index; the same function.
pub fn check_native_rec_f(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &mut IFEnv,
    p: &NativeParts,
    cv_ta: &IConstantVal,
    ctors_a: &Vec<(IConstantVal, u64)>,
) -> Result<(IConstantVal, Vec<EIdx>), CheckError> {
    native_install::check_native_rec(pers, st, mode, fe, p, cv_ta, ctors_a)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstallF.lean:34 checkNativeTableF`
/// — `checkNativeTable` through the index; the same function.
pub fn check_native_table_f(
    pers: &PersTier,
    st: &mut AState,
    p: &NativeParts,
    ctors_a: &Vec<(IConstantVal, u64)>,
    sortss: &Vec<Vec<LIdx>>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    native_install::check_native_table(pers, st, p, ctors_a, sortss, fe)
}
