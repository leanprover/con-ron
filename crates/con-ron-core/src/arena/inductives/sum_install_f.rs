//! `arena::inductives::sum_install_f` — the `F` names.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/SumInstallF.lean`.
//!
//! `ConLeche/Kernel/Inductives/SumInstallF.lean` is `SumInstall.lean`'s stages
//! over an `FEnv`.  The arena has ONE environment type (task #97c's deviation
//! 1), so the `F` twins ARE `arena::inductives::sum_install`'s; this module
//! carries the `F`-suffixed NAMES, as `arena::inductives::struct_install_f` and
//! `arena::fenv` do.

use super::sum_install;
use crate::arena::env::{IConstantVal, IFEnv};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::AState;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:19-21 checkSumTeleF`
/// — `checkSumTele` through the index; the same function.
pub fn check_sum_tele_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    n: u64,
    cv_ta0: &IConstantVal,
) -> Result<(IConstantVal, LIdx), CheckError> {
    sum_install::check_sum_tele(pers, vis, st, mode, fe, cv, n, cv_ta0)
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:27-29 checkStructFieldSortsIF`
/// — `checkStructFieldSortsI` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn check_struct_field_sorts_i_f(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    is_prop: bool,
    large: bool,
    s: &LIdx,
    n_p: u64,
    fvs: &Vec<EIdx>,
    idx_args: &Vec<EIdx>,
    k: u64,
) -> Result<Vec<LIdx>, CheckError> {
    sum_install::check_struct_field_sorts_i(pers, vis, st, mode, fe, is_prop, large, s, n_p, fvs, idx_args, k)
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:31-34 checkStructFieldSortsIFA`
/// — the same function over an array of field variables; over a `Vec` there is
/// nothing left to distinguish.
#[allow(clippy::too_many_arguments)]
pub fn check_struct_field_sorts_i_fa(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    is_prop: bool,
    large: bool,
    s: &LIdx,
    n_p: u64,
    fvs: &Vec<EIdx>,
    idx_args: &Vec<EIdx>,
    k: u64,
) -> Result<Vec<LIdx>, CheckError> {
    sum_install::check_struct_field_sorts_i(pers, vis, st, mode, fe, is_prop, large, s, n_p, fvs, idx_args, k)
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:40-42 checkSumCtorF`
/// — `checkSumCtor` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctor_f(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe0: &IFEnv,
    fe: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    res_sort: &LIdx,
    is_prop: bool,
    large: bool,
    cv_c: &IConstantVal,
    n_f: u64,
    cv_ta: &IConstantVal,
) -> Result<(IConstantVal, Vec<LIdx>), CheckError> {
    sum_install::check_sum_ctor(
        pers,
        st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, cv_c, n_f, cv_ta,
    )
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:44-46 checkSumCtorsF`
/// — `checkSumCtors` through the index; the same function.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctors_f(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe0: &IFEnv,
    fe: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    res_sort: &LIdx,
    is_prop: bool,
    large: bool,
    cv_ta: &IConstantVal,
    ctors: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
    sout: Vec<Vec<LIdx>>,
) -> Result<(Vec<(IConstantVal, u64)>, Vec<Vec<LIdx>>), CheckError> {
    sum_install::check_sum_ctors(
        pers,
        st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, cv_ta, ctors, i, out, sout,
    )
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstallF.lean:48-50 consSumCtorsF`
/// — `consSumCtors` through the index; the same function.
pub fn cons_sum_ctors_f(n_p: u64, ctors: &Vec<(IConstantVal, u64)>, i: usize, fe: IFEnv) -> IFEnv {
    sum_install::cons_sum_ctors(n_p, ctors, i, fe)
}

