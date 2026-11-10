//! `arena::inductives::sum_install` — the block install's shared stages.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/SumInstall.lean`, which is
//! `ConLeche/Kernel/Inductives/SumInstall.lean` whole over handles: the type
//! former's telescope, the per-field universe bound, the constructors' stage
//! (every constructor stored AS DECLARED, every stage a check returning
//! nothing) and the stored rules.
//!
//! ## The twin's deviations
//!
//! * **One function per stage, at the index**: each function is both the
//!   `Env`-level specification and its cached twin over the index
//!   (`checkSumCtorC`, `checkSumCtorsC` in `ConLeche/Cached/IndBlock.lean`,
//!   `checkStructFieldSortsIC` in `ConLeche/Cached/IndPositivity.lean`),
//!   cited side by side; the field loops are list loops.
//! * **`consSumCtors` stays pure** — the index push touches no term.

use super::struct_install;
use super::struct_parts;
use crate::arena::canon;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_SORT};
use crate::arena::monad::{AState, fail, fail_dangling_e, intern_e_const, read_level_m, view_sort};
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::level;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages (con-ron-core's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former does not reduce to a sort                 `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_TELE_SORT: [u32; 66] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101, 100, 117, 99, 101, 32,
    116, 111, 32, 97, 32, 115, 111, 114, 116, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: field index     `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FLD_IDX: [u32; 28] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32, 105, 110,
    100, 101, 120, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: field universe too large  `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FLD_BIG: [u32; 38] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32, 117, 110,
    105, 118, 101, 114, 115, 101, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: large eliminator with a non-propositional field             `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FLD_ELIM: [u32; 72] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 108, 97, 114, 103, 101, 32, 101, 108,
    105, 109, 105, 110, 97, 116, 111, 114, 32, 119, 105, 116, 104, 32, 97, 32, 110, 111, 110, 45,
    112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 102, 105, 101, 108, 100,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: constructor field telescope        `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FIELD_TELE: [u32; 47] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 102, 105, 101, 108, 100, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32,
    32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: constructor telescope        `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_TELE: [u32; 41] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: invalid constructor return type  `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_RET: [u32; 45] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 105, 110, 118, 97, 108, 105, 100, 32,
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 116, 117, 114, 110, 32, 116,
    121, 112, 101, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former telescope       `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_TTELE: [u32; 40] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: opened constructor residual      `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_RESID: [u32; 45] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 111, 112, 101, 110, 101, 100, 32, 99,
    111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32,
    32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: field domain after the block       `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_DOM: [u32; 47] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32, 100, 111,
    109, 97, 105, 110, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107,
    32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: index expression mentions the block   `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_CTOR_IDX: [u32; 50] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 105, 110, 100, 101, 120, 32, 101, 120,
    112, 114, 101, 115, 115, 105, 111, 110, 32, 109, 101, 110, 116, 105, 111, 110, 115, 32, 116,
    104, 101, 32, 98, 108, 111, 99, 107, 32, 32, 32,
];

// ---------------------------------------------------------------------------
// The type former's stage
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:33-38 checkSumTele
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:31-43 checkSumTele`
/// — the type former's TELESCOPE: `n` Π binders ending in a sort (the block's
/// check puts a former at its telescope, `reduceMember`).  Returns the former
/// and its sort.
pub fn check_sum_tele(
    pers: &PersTier,
    st: &AState,
    n: u64,
    cv_ta0: &IConstantVal,
) -> Result<(IConstantVal, LIdx), CheckError> {
    match expr_ops::strip_pis(pers, st, n, &cv_ta0.ty) {
        Err(e) => Err(e),
        Ok(Some(q)) => if q.1.tag() == ETAG_SORT {
            match view_sort(pers, st, &q.1) {
                None => fail_dangling_e(),
                Some(s) => Ok((env::i_constant_val_dup(cv_ta0), s)),
            }
        } else {
            fail(core_types::invalid(code_points(&M_TELE_SORT)))
        },
        Ok(None) => fail(core_types::invalid(code_points(&M_TELE_SORT))),
    }
}

// ---------------------------------------------------------------------------
// The constructors' stage (`SumInstall.lean:141-326` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `xs.contains x` over a `Vec<EIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:47-70 checkStructFieldSortsI`
/// — `idxArgs.contains fv`; handles, so `==` is word equality.
pub fn eidx_contains(xs: &Vec<EIdx>, x: &EIdx, i: usize) -> bool {
    if i >= xs.len() {
        false
    } else if xs[i].eq2(x) {
        true
    } else {
        eidx_contains(xs, x, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:40-64 checkStructFieldSortsI
/// con-leche: ConLeche/Cached/IndPositivity.lean:497-513 checkStructFieldSortsIC
/// con-leche: ConLeche/Cached/IndBlock.lean:127-142 checkStructFieldSortsC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:47-70 checkStructFieldSortsI`
/// — every field's domain has a sort over the opened constructor telescope,
/// under the official per-field universe bound unless the family is
/// propositional.  **Walks the fields from the LAST to the first** (the twin's
/// `j + 1` recursion).
#[allow(clippy::too_many_arguments)]
pub fn check_struct_field_sorts_i(
    pers: &PersTier,
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
) -> Result<(), CheckError> {
    if k == 0 {
        Ok(())
    } else {
        let j: u64 = k - 1;
        let at: Option<EIdx> = if j < fvs.len() as u64 {
            Some(fvs[j as usize].dup2())
        } else {
            None
        };
        match checker_base::unwrap_or(at, core_types::internal(code_points(&M_FLD_IDX))) {
            Err(e) => Err(e),
            Ok(fv) => match expr_ops::fvar_type_d(pers, st, &fv) {
                Err(e) => Err(e),
                Ok(fvt) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, n_p + j, &fvt) {
                    Err(e) => Err(e),
                    Ok(ty) => match core::ensure_sort_core(pers, st, mode, fe, core::CHECK_FUEL, n_p + j, &ty) {
                        Err(e) => Err(e),
                        Ok(u) => match field_sort_bound(pers, st, is_prop, large, s, &u, &fv, idx_args) {
                            Err(e) => Err(e),
                            Ok(()) => check_struct_field_sorts_i(
                                pers, st, mode, fe, is_prop, large, s, n_p, fvs, idx_args, j,
                            ),
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:40-64 checkStructFieldSortsI
/// con-leche: ConLeche/Cached/IndPositivity.lean:497-513 checkStructFieldSortsIC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:47-70 checkStructFieldSortsI`
/// — one field's universe bound: official's `leq` against the family's sort at
/// a non-propositional family, and the large eliminator's escape hatch
/// (`Prop`-valued or an index argument) at a propositional one.
#[allow(clippy::too_many_arguments)]
pub fn field_sort_bound(
    pers: &PersTier,
    st: &mut AState,
    is_prop: bool,
    large: bool,
    s: &LIdx,
    u: &LIdx,
    fv: &EIdx,
    idx_args: &Vec<EIdx>,
) -> Result<(), CheckError> {
    if !is_prop {
        match read_level_m(pers, st, u) {
            Err(e) => Err(e),
            Ok(lu) => match read_level_m(pers, st, s) {
                Err(e) => Err(e),
                Ok(ls) => match core::lift_fueled(level::leq(&lu, &ls)) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_FLD_BIG))),
                    Ok(true) => Ok(()),
                },
            },
        }
    } else if large {
        match core::zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => match core::lvl_eq(pers, st, u, &z) {
                Err(e) => Err(e),
                Ok(eq) => {
                    let zero: bool = match eq {
                        Some(true) => true,
                        Some(false) => false,
                        None => false,
                    };
                    if zero || eidx_contains(idx_args, fv, 0) {
                        Ok(())
                    } else {
                        fail(core_types::invalid(code_points(&M_FLD_ELIM)))
                    }
                }
            },
        }
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — stage 2, one constructor's type: the ordinary constant check, the
/// result shape, the parameter pins against the type former's opened
/// telescope, the pre-block resolution of the field domains, and the per-field
/// universe bound.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctor(
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
) -> Result<(), CheckError> {
    match checker_base::check_constant_val(pers, st, mode, fe, cv_c, false) {
        Err(e) => Err(e),
        Ok(()) => match expr_ops::strip_pis(pers, st, n_p + n_f, &cv_c.ty) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
                Ok(Some(cq)) => {
                    match struct_parts::struct_ctor_resid_ok(pers, st, t, lps, n_p, n_f, n_idx, &cq.1) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_CTOR_RET))),
                        Ok(true) => check_sum_ctor_frames(
                            pers,
                            st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, n_f,
                            cv_ta, cv_c,
                        ),
                    }
                }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — the opened frames: the constructor's parameters against the former's, the
/// opened residual's shape, the field domains' pre-block resolution and the
/// per-field universe bound.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctor_frames(
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
    n_f: u64,
    cv_ta: &IConstantVal,
    cv_c: &IConstantVal,
) -> Result<(), CheckError> {
    match core::open_pis_at_fvars_f(pers, st, n_p, &cv_c.ty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
        Ok(Some(cq)) => match core::open_pis_at_fvars_f(pers, st, n_p, &cv_ta.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TTELE))),
            Ok(Some(tq)) => match checker_base::fvar_type_ds(pers, st, &tq.0, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(tdoms) => {
                    match struct_install::check_struct_doms_at(pers, st, mode, fe, 0, &cq.0, &tdoms, n_p)
                    {
                        Err(e) => Err(e),
                        Ok(()) => match core::open_pis_at_fvars_f(pers, st, n_f, &cq.1, n_p) {
                            Err(e) => Err(e),
                            Ok(None) => {
                                fail(core_types::not_implemented(code_points(&M_FIELD_TELE)))
                            }
                            Ok(Some(xq)) => check_sum_ctor_resid(
                                pers,
                                st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large,
                                n_f, &cq.0, &xq.0, &xq.1,
                            ),
                        },
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — the opened residual is the family at the opened parameter variables
/// followed by the index expressions, the field domains and the index
/// expressions resolve BEFORE the block, and the fields' sorts are measured.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctor_resid(
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
    n_f: u64,
    p_fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
) -> Result<(), CheckError> {
    match struct_parts::param_levels(pers, st, lps) {
        Err(e) => Err(e),
        Ok(us) => match intern_e_const(pers, st, t.dup2(), us) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, xrest) {
                Err(e) => Err(e),
                Ok(xfn) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, xrest) {
                    Err(e) => Err(e),
                    Ok(xargs) => {
                        let pre: Vec<EIdx> = expr_ops::take_eidx_n(&xargs, n_p);
                        if !(xfn.eq2(&hd)
                            && canon::eidx_vec_beq(&pre, p_fvs, 0)
                            && xargs.len() as u64 == n_p + n_idx)
                        {
                            fail(core_types::not_implemented(code_points(&M_CTOR_RESID)))
                        } else {
                            let idx_args: Vec<EIdx> = core::drop_eidx(&xargs, n_p as usize);
                            check_sum_ctor_sorts(
                                pers,
                                st, mode, fe0, fe, n_p, res_sort, is_prop, large, n_f,
                                x_fvs, &idx_args,
                            )
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — the field domains and the index expressions resolve BEFORE the block, and
/// the fields' sorts are measured under the official bound.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctor_sorts(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe0: &IFEnv,
    fe: &IFEnv,
    n_p: u64,
    res_sort: &LIdx,
    is_prop: bool,
    large: bool,
    n_f: u64,
    x_fvs: &Vec<EIdx>,
    idx_args: &Vec<EIdx>,
) -> Result<(), CheckError> {
    match field_doms_resolve(pers, st, fe0, x_fvs, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::not_implemented(code_points(&M_CTOR_DOM))),
        Ok(true) => match idx_args_resolve(pers, st, fe0, idx_args, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_CTOR_IDX))),
            Ok(true) => check_struct_field_sorts_i(
                pers, st, mode, fe, is_prop, large, res_sort, n_p, x_fvs, idx_args, n_f,
            ),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — every field domain resolves at the PRE-BLOCK environment.
pub fn field_doms_resolve(
    pers: &PersTier,
    st: &mut AState,
    fe0: &IFEnv,
    x_fvs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= x_fvs.len() {
        Ok(true)
    } else {
        match expr_ops::fvar_type_d(pers, st, &x_fvs[i]) {
            Err(e) => Err(e),
            Ok(t) => match checker_base::consts_resolve_f_fast(pers, st, fe0, &t) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => field_doms_resolve(pers, st, fe0, x_fvs, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:66-107 checkSumCtor
/// con-leche: ConLeche/Cached/IndBlock.lean:144-170 checkSumCtorC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:89-129 checkSumCtor`
/// — the index expressions never mention the block.
pub fn idx_args_resolve(
    pers: &PersTier,
    st: &mut AState,
    fe0: &IFEnv,
    idx_args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= idx_args.len() {
        Ok(true)
    } else {
        let e: EIdx = idx_args[i].dup2();
        match checker_base::consts_resolve_f_fast(pers, st, fe0, &e) {
            Err(er) => Err(er),
            Ok(false) => Ok(false),
            Ok(true) => idx_args_resolve(pers, st, fe0, idx_args, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:109-117 checkSumCtors
/// con-leche: ConLeche/Cached/IndBlock.lean:172-179 checkSumCtorsC
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:131-141 checkSumCtors`
/// — stage 2, all constructors' types from `i` on, at the environment holding
/// the type former.
#[allow(clippy::too_many_arguments)]
pub fn check_sum_ctors(
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
) -> Result<(), CheckError> {
    if i >= ctors.len() {
        Ok(())
    } else {
        match check_sum_ctor(
            pers, st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, &ctors[i].0,
            ctors[i].1, cv_ta,
        ) {
            Err(e) => Err(e),
            Ok(()) => check_sum_ctors(
                pers, st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, cv_ta, ctors,
                i + 1,
            ),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:119-122 consSumCtors
/// con-leche: ConLeche/Cached/IndBlock.lean:37-40 consSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:143-149 consSumCtors`
/// — the constructors' conses, in order (the first constructor deepest).
/// Pure: the index push touches no term.
pub fn cons_sum_ctors(n_p: u64, ctors: &Vec<(IConstantVal, u64)>, i: usize, fe: IFEnv) -> IFEnv {
    if i >= ctors.len() {
        fe
    } else {
        let stored = IConstantInfo::CtorInfo(env::i_constant_val_dup(&ctors[i].0), n_p, ctors[i].1);
        cons_sum_ctors(n_p, ctors, i + 1, env::ifenv_push(fe, stored))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:124-130 sumRules
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:151-157 sumRules`
/// — the stored rules from `i` on: constructor `j`'s with the generated
/// right-hand side `j`, `.plain` (the major is the family at the recursor's
/// parameters); pairwise, stopping at the shorter list.
pub fn sum_rules(ctors: &Vec<(IConstantVal, u64)>, rhss: &Vec<EIdx>, i: usize, out: Vec<IRecRule>) -> Vec<IRecRule> {
    if i >= ctors.len() || i >= rhss.len() {
        out
    } else {
        let mut o: Vec<IRecRule> = out;
        o.push(IRecRule {
            ctor: ctors[i].0.name.dup2(),
            nfields: ctors[i].1,
            fire: IRecRuleFire::Plain,
            rhs: rhss[i].dup2(),
        });
        sum_rules(ctors, rhss, i + 1, o)
    }
}
