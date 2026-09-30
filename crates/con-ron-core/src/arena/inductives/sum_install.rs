//! `arena::inductives::sum_install` — the block install's shared stages.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/SumInstall.lean`, which is
//! `ConLeche/Kernel/Inductives/SumInstall.lean` whole over handles: official's
//! telescope loop, the type former's telescope, the per-field universe bound,
//! the constructors' stage (every constructor stored AS DECLARED) and the
//! stored rules.
//!
//! ## The twin's deviations
//!
//! * **The `…F` twins collapse into these** (task #97c's deviation 1):
//!   `ConLeche/Kernel/Inductives/SumInstallF.lean`'s eight declarations are the
//!   same functions over an `FEnv`, and `checkStructFieldSortsIFA` is one of
//!   them over `Array`.  The names live on in
//!   `arena::inductives::sum_install_f`.
//! * **`sumRules` takes `fe : IFEnv`, not `find?`**: con-leche abstracts the
//!   lookup so that the pure and the indexed tier share one body; the arena has
//!   one environment, and a `find?` passed as an argument is a closure.
//! * **`consSumCtors` stays pure** — the index push touches no term.
//! * **The fields' sorts are a `Vec<LIdx>`**, not an interned `LsIdx`
//!   (`arena::inductives::struct_parts`' module note).

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
use crate::arena::monad::{
    AState, fail, fail_dangling_e, intern_e_const, intern_e_forall_e, intern_e_fvar, intern_e_sort, read_level_m, view, view_sort,
};
use crate::arena::store::ENodeView;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
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
/// `direct sum: type former does not reduce to a telescope                `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_TELE_SHAPE: [u32; 70] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101, 100, 117, 99, 101, 32,
    116, 111, 32, 97, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former telescope       `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_IND_TELE: [u32; 40] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former result sort        `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_IND_SORT: [u32; 43] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 114, 101, 115, 117, 108, 116, 32, 115, 111, 114, 116, 32, 32, 32, 32, 32,
    32, 32, 32,
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
/// `direct sum: positivity walk fuel  `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_POS_FUEL: [u32; 34] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 112, 111, 115, 105, 116, 105, 118, 105,
    116, 121, 32, 119, 97, 108, 107, 32, 102, 117, 101, 108, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: non positive occurrence of the inductive   `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_POS_NEG: [u32; 55] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 110, 111, 110, 32, 112, 111, 115, 105,
    116, 105, 118, 101, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 116,
    104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 32, 32,
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
// The type former's stage (`SumInstall.lean:42-139` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:34-57 whnfTelescope
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:43-64 whnfTelescope`
/// — **official's telescope loop** (`check_inductive_types`): peel `n` Π
/// binders off `e`, reducing the residual to weak head normal form before each
/// binder and at the end, where it must be a sort.  Lean conses the binder on
/// the way out; the port pushes on the way in, at the same order of effects.
pub fn whnf_telescope(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    i: u64,
    n: u64,
    e: &EIdx,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<(Vec<(EIdx, BinderMeta)>, LIdx), CheckError> {
    match core::whnf(pers, vis, st, mode, fe, core::CHECK_FUEL, i, e) {
        Err(er) => Err(er),
        Ok(e2) => match view(pers, st, &e2) {
            Err(er) => Err(er),
            Ok(ENodeView::Sort(s)) => {
                if n == 0 {
                    Ok((out, s))
                } else {
                    fail(core_types::invalid(code_points(&M_TELE_SHAPE)))
                }
            }
            Ok(ENodeView::ForallE(dom, body, bm)) => {
                if n == 0 {
                    fail(core_types::invalid(code_points(&M_TELE_SORT)))
                } else {
                    match intern_e_fvar(pers, st, i, dom.dup2()) {
                        Err(er) => Err(er),
                        Ok(fv) => {
                            match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                                Err(er) => Err(er),
                                Ok(b) => {
                                    let mut o: Vec<(EIdx, BinderMeta)> = out;
                                    o.push((dom, bm));
                                    whnf_telescope(pers, vis, st, mode, fe, i + 1, n - 1, &b, o)
                                }
                            }
                        }
                    }
                }
            }
            Ok(_) => {
                if n == 0 {
                    fail(core_types::invalid(code_points(&M_TELE_SORT)))
                } else {
                    fail(core_types::invalid(code_points(&M_TELE_SHAPE)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/Positivity.lean:211-219 closeTelescope
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:66-74 closeTelescope`
/// — close a telescope opened at the free variables `i ..< i + bs.length` back
/// into a syntactic Π-telescope over `body`.  The cursor recursion builds the
/// innermost binder first, as the twin's `let inner ← …` does.
pub fn close_telescope(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    k: usize,
    i: u64,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    if k >= bs.len() {
        Ok(body.dup2())
    } else {
        match close_telescope(pers, st, bs, k + 1, i + 1, body) {
            Err(e) => Err(e),
            Ok(inner) => match expr_ops::abstract1_fast(pers, st, CORE_WALK_FUEL, &inner, i, 0) {
                Err(e) => Err(e),
                Ok(closed) => {
                    let dom: EIdx = bs[k].0.dup2();
                    let bm: BinderMeta = expr::binder_meta_dup(&bs[k].1);
                    intern_e_forall_e(pers, st, dom, closed, bm)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:76-103 checkSumTele`
/// — the type former's TELESCOPE (con-leche's task #195): the checked declared
/// type when it is already a syntactic telescope of `n` Π binders ending in a
/// sort, else the declared type's whnf'd telescope, closed and checked as the
/// former's type in its place.
pub fn check_sum_tele(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
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
            check_sum_tele_slow(pers, vis, st, mode, fe, cv, n, cv_ta0)
        },
        Ok(None) => check_sum_tele_slow(pers, vis, st, mode, fe, cv, n, cv_ta0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:59-73 checkSumTele
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:93-103 checkSumTele.checkSumTeleSlow`
/// — the `_` arm of `checkSumTele`'s match, named because over handles the
/// syntactic test is two `view`s and duplicating the arm would duplicate the
/// whnf loop.
pub fn check_sum_tele_slow(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    n: u64,
    cv_ta0: &IConstantVal,
) -> Result<(IConstantVal, LIdx), CheckError> {
    match whnf_telescope(pers, vis, st, mode, fe, 0, n, &cv_ta0.ty, Vec::new()) {
        Err(e) => Err(e),
        Ok(q) => match intern_e_sort(pers, st, q.1.dup2()) {
            Err(e) => Err(e),
            Ok(sort_s) => match close_telescope(pers, st, &q.0, 0, 0, &sort_s) {
                Err(e) => Err(e),
                Ok(ty) => {
                    let cv2 = IConstantVal {
                        name: cv.name.dup2(),
                        level_params: env::nidx_vec_dup(&cv.level_params),
                        ty,
                    };
                    match checker_base::check_constant_val(pers, vis, st, mode, fe, &cv2) {
                        Err(e) => Err(e),
                        Ok(cv_ta) => Ok((cv_ta, q.1)),
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The constructors' stage (`SumInstall.lean:141-326` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `xs.contains x` over a `Vec<EIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:144-168 checkStructFieldSortsI`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-48 checkStructFieldSortsIF
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:50-68 checkStructFieldSortsIFA
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:144-168 checkStructFieldSortsI`
/// — the fields' sorts over the opened constructor telescope, with the
/// official per-field universe bound unless the family is propositional.
/// **Walks the fields from the LAST to the first** (the twin's `j + 1`
/// recursion) and returns the sorts in field order, which is the twin's
/// `rest ++ [u]`.
#[allow(clippy::too_many_arguments)]
pub fn check_struct_field_sorts_i(
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
    if k == 0 {
        Ok(Vec::new())
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
                Ok(fvt) => {
                    match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, n_p + j, &fvt) {
                        Err(e) => Err(e),
                        Ok(ty) => {
                            match core::ensure_sort_core(
                                pers,
                                vis,
                                st,
                                mode,
                                fe,
                                core::CHECK_FUEL,
                                n_p + j,
                                &ty,
                            ) {
                                Err(e) => Err(e),
                                Ok(u) => {
                                    match field_sort_bound(pers, st, is_prop, large, s, &u, &fv, idx_args)
                                    {
                                        Err(e) => Err(e),
                                        Ok(()) => match check_struct_field_sorts_i(
                                            pers,
                                            vis,
                                            st, mode, fe, is_prop, large, s, n_p, fvs, idx_args, j,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(rest) => {
                                                let mut o: Vec<LIdx> = rest;
                                                o.push(u);
                                                Ok(o)
                                            }
                                        },
                                    }
                                }
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:75-100 checkStructFieldSortsI
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:144-168 checkStructFieldSortsI`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:70-100 checkSumCtorF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
/// — stage 2, one constructor's type: the ordinary constant check, the
/// annotated result shape, the parameter pins against the type former's opened
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
) -> Result<(IConstantVal, Vec<LIdx>), CheckError> {
    match checker_base::check_constant_val(pers, fe.visible_below, st, mode, fe, cv_c) {
        Err(e) => Err(e),
        Ok(cv_ca) => match expr_ops::strip_pis(pers, st, n_p + n_f, &cv_ca.ty) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
                Ok(Some(cq)) => {
                    match struct_parts::struct_ctor_resid_ok(pers, st, t, lps, n_p, n_f, n_idx, &cq.1) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_CTOR_RET))),
                        Ok(true) => check_sum_ctor_frames(
                            pers,
                            st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, n_f,
                            cv_ta, cv_ca,
                        ),
                    }
                }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
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
    cv_ca: IConstantVal,
) -> Result<(IConstantVal, Vec<LIdx>), CheckError> {
    match checker_base::open_pis_at_fvars_f(pers, st, n_p, &cv_ca.ty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
        Ok(Some(cq)) => match checker_base::open_pis_at_fvars_f(pers, st, n_p, &cv_ta.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TTELE))),
            Ok(Some(tq)) => match checker_base::fvar_type_ds(pers, st, &tq.0, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(tdoms) => {
                    match struct_install::check_struct_doms_at(pers, fe.visible_below, st, mode, fe, 0, &cq.0, &tdoms, n_p)
                    {
                        Err(e) => Err(e),
                        Ok(()) => match checker_base::open_pis_at_fvars_f(pers, st, n_f, &cq.1, n_p) {
                            Err(e) => Err(e),
                            Ok(None) => {
                                fail(core_types::not_implemented(code_points(&M_FIELD_TELE)))
                            }
                            Ok(Some(xq)) => check_sum_ctor_resid(
                                pers,
                                st, mode, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large,
                                n_f, cv_ca, &cq.0, &xq.0, &xq.1,
                            ),
                        },
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
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
    cv_ca: IConstantVal,
    p_fvs: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
) -> Result<(IConstantVal, Vec<LIdx>), CheckError> {
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
                                st, mode, fe0, fe, n_p, res_sort, is_prop, large, n_f, cv_ca,
                                x_fvs, &idx_args,
                            )
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
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
    cv_ca: IConstantVal,
    x_fvs: &Vec<EIdx>,
    idx_args: &Vec<EIdx>,
) -> Result<(IConstantVal, Vec<LIdx>), CheckError> {
    match field_doms_resolve(pers, fe0.visible_below, st, fe0, x_fvs, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::not_implemented(code_points(&M_CTOR_DOM))),
        Ok(true) => match idx_args_resolve(pers, fe0.visible_below, st, fe0, idx_args, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_CTOR_IDX))),
            Ok(true) => match check_struct_field_sorts_i(pers, fe.visible_below,
                st, mode, fe, is_prop, large, res_sort, n_p, x_fvs, idx_args, n_f,
            ) {
                Err(e) => Err(e),
                Ok(sorts) => Ok((cv_ca, sorts)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
/// — every field domain resolves at the PRE-BLOCK environment.
pub fn field_doms_resolve(
    pers: &PersTier,
    vis: u64,
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
            Ok(t) => match checker_base::consts_resolve_f_fast(pers, vis, st, fe0, &t) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => field_doms_resolve(pers, vis, st, fe0, x_fvs, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:102-147 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:242-282 checkSumCtor`
/// — the index expressions never mention the block.
pub fn idx_args_resolve(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe0: &IFEnv,
    idx_args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= idx_args.len() {
        Ok(true)
    } else {
        let e: EIdx = idx_args[i].dup2();
        match checker_base::consts_resolve_f_fast(pers, vis, st, fe0, &e) {
            Err(er) => Err(er),
            Ok(false) => Ok(false),
            Ok(true) => idx_args_resolve(pers, vis, st, fe0, idx_args, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:149-161 checkSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:102-112 checkSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:284-298 checkSumCtors`
/// — stage 2, all constructors' types, at the environment holding the type
/// former.  Lean conses on the way out; the port pushes on the way in.
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
    out: Vec<(IConstantVal, u64)>,
    sout: Vec<Vec<LIdx>>,
) -> Result<(Vec<(IConstantVal, u64)>, Vec<Vec<LIdx>>), CheckError> {
    if i >= ctors.len() {
        Ok((out, sout))
    } else {
        match check_sum_ctor(
            pers,
            st,
            mode,
            fe0,
            fe,
            t,
            lps,
            n_p,
            n_idx,
            res_sort,
            is_prop,
            large,
            &ctors[i].0,
            ctors[i].1,
            cv_ta,
        ) {
            Err(e) => Err(e),
            Ok(q) => {
                let mut o: Vec<(IConstantVal, u64)> = out;
                o.push((q.0, ctors[i].1));
                let mut so: Vec<Vec<LIdx>> = sout;
                so.push(q.1);
                check_sum_ctors(
                    pers,
                    st,
                    mode,
                    fe0,
                    fe,
                    t,
                    lps,
                    n_p,
                    n_idx,
                    res_sort,
                    is_prop,
                    large,
                    cv_ta,
                    ctors,
                    i + 1,
                    o,
                    so,
                )
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:163-166 consSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:114-117 consSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:300-306 consSumCtors`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:168-184 sumRules
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:308-323 sumRules`
/// — the stored rules: constructor `j`'s with the generated right-hand side
/// `j`, plain when the generated type's major is the family at the parameters,
/// with the two rescue bits `recRuleBits` reads off the block's own store and
/// `paramsBlind`, because the route's rule law holds at any pair of fitting
/// parameter spines.
#[allow(clippy::too_many_arguments)]
pub fn sum_rules(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    rec_name: &NIdx,
    n_p: u64,
    m_i: u64,
    r_p: u64,
    rec_ty: &EIdx,
    ctors: &Vec<(IConstantVal, u64)>,
    rhss: &Vec<EIdx>,
    i: usize,
    out: Vec<IRecRule>,
) -> Result<Vec<IRecRule>, CheckError> {
    if i >= ctors.len() || i >= rhss.len() {
        Ok(out)
    } else {
        match expr_ops::rec_rule_plain(pers, st, CORE_WALK_FUEL, rec_ty, m_i, r_p, n_p) {
            Err(e) => Err(e),
            Ok(plain) => {
                let fire = if plain {
                    IRecRuleFire::Plain
                } else {
                    IRecRuleFire::Inert
                };
                let rl = IRecRule {
                    ctor: ctors[i].0.name.dup2(),
                    nfields: ctors[i].1,
                    ctor_params: n_p,
                    fire,
                    rhs: rhss[i].dup2(),
                    k: false,
                    eta: false,
                    params_blind: true,
                };
                match core::rec_rule_bits(pers, vis, st, fe, rec_name, rl) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        let mut o: Vec<IRecRule> = out;
                        o.push(r);
                        sum_rules(
                            pers,
                            vis,
                            st,
                            fe,
                            rec_name,
                            n_p,
                            m_i,
                            r_p,
                            rec_ty,
                            ctors,
                            rhss,
                            i + 1,
                            o,
                        )
                    }
                }
            }
        }
    }
}
