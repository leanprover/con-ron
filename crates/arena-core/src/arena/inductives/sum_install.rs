//! `arena::inductives::sum_install` — the direct install's stages.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/SumInstall.lean`, which is
//! `ConLeche/Kernel/Inductives/SumInstall.lean` whole over handles: official's
//! telescope loop, the type former's stage, the per-field universe bound,
//! official's positivity walk as a normalisation, the constructors' stage and
//! the stored rules.
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
//! * **`checkSumInd` takes `isRec : bool`, not `capsOf : InductiveShape →
//!   IndCaps`.**  A function argument is a closure and there is exactly ONE
//!   instantiation left in con-leche, so `nativeCapsAt` is twinned HERE, one
//!   module earlier than con-leche places it, and `checkSumInd` calls it.
//! * **`consSumCtors` stays pure** — the index push touches no term.
//! * **The fields' sorts are a `Vec<LIdx>`**, not an interned `LsIdx`
//!   (`arena::inductives::struct_parts`' module note).

use super::struct_install;
use super::struct_parts;
use super::sum_parts;
use super::sum_parts::InductiveShape;
use crate::arena::canon;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IIndCaps, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{fail, intern_e, read_level, view, AState};
use crate::arena::store::ENodeView;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::level;
use con_ron_core::ron::hashmap::{Dup, Eq2};
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:48-65 whnfTelescope`
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
                    match intern_e(pers, st, ENodeView::FVar(i, dom.dup2())) {
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:70-78 closeTelescope
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:70-75 closeTelescope`
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
                    intern_e(pers, st, ENodeView::ForallE(dom, closed, bm))
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:83-90 checkSumTele`
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
        Ok(Some(q)) => match view(pers, st, &q.1) {
            Err(e) => Err(e),
            Ok(ENodeView::Sort(s)) => Ok((env::i_constant_val_dup(cv_ta0), s)),
            Ok(_) => check_sum_tele_slow(pers, vis, st, mode, fe, cv, n, cv_ta0),
        },
        Ok(None) => check_sum_tele_slow(pers, vis, st, mode, fe, cv, n, cv_ta0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:96-102 checkSumTeleSlow`
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
        Ok(q) => match intern_e(pers, st, ENodeView::Sort(q.1.dup2())) {
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

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:110-122 nativeCapsAt`
/// — the capabilities a block on the fixpoint route earns (con-leche's task
/// #210 Part A): structure eta at a non-`Prop` structure-like block,
/// unit-likeness at a fieldless constructor, rule K at official's
/// `is_K_target`, nothing at any other block.  Twinned here rather than in
/// `arena::inductives::native_install` — see the module note.
pub fn native_caps_at(
    pers: &PersTier,
    st: &mut AState,
    p: &InductiveShape,
    is_rec: bool,
) -> Result<IIndCaps, CheckError> {
    if p.ctors.len() != 1 {
        Ok(env::i_ind_caps_default())
    } else {
        // the constructor's name and field count are read out FIRST: a `&&`
        // that still holds a loan into `p.ctors[0]` while the record is built
        // is what Aeneas cannot join (task #97-P4a's second extraction rule)
        let c_name: NIdx = p.ctors[0].0.name.dup2();
        let c_fields: u64 = p.ctors[0].1;
        match read_level(pers, st, &p.res_sort) {
            Err(e) => Err(e),
            Ok(l) => Ok(IIndCaps {
                eta: p.n_idx == 0 && !p.is_prop && !is_rec,
                eta_ctor: c_name,
                eta_params: p.n_p,
                eta_fields: c_fields,
                unitlike: p.n_idx == 0 && c_fields == 0,
                unit_params: p.n_p,
                rule_k: c_fields == 0 && p.is_prop,
                sort_z: level::zeroness_of(&l),
            }),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:128-139 checkSumInd`
/// — stage 1: the type former, stored with the block's capability record at
/// its telescope; returns the record completed with the result sort.
pub fn check_sum_ind(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &InductiveShape,
    is_rec: bool,
) -> Result<(IFEnv, IConstantVal, InductiveShape), CheckError> {
    match checker_base::check_constant_val(pers, fe.visible_below, st, mode, &fe, &p.cv_t) {
        Err(e) => Err(e),
        Ok(cv_ta0) => match check_sum_tele(pers, fe.visible_below, st, mode, &fe, &p.cv_t, p.n_p + p.n_idx, &cv_ta0) {
            Err(e) => Err(e),
            Ok(q) => check_sum_ind_at(pers, st, fe, p, is_rec, q.0, q.1),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:132-139 checkSumInd`
/// — the checked telescope's residual sort, the completed record and the
/// install.
pub fn check_sum_ind_at(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    p: &InductiveShape,
    is_rec: bool,
    cv_ta: IConstantVal,
    s: LIdx,
) -> Result<(IFEnv, IConstantVal, InductiveShape), CheckError> {
    match expr_ops::strip_pis(pers, st, p.n_p + p.n_idx, &cv_ta.ty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::internal(code_points(&M_IND_TELE))),
        Ok(Some(q)) => match intern_e(pers, st, ENodeView::Sort(s.dup2())) {
            Err(e) => Err(e),
            Ok(sort_s) => {
                if !q.1.eq2(&sort_s) {
                    fail(core_types::internal(code_points(&M_IND_SORT)))
                } else {
                    match sum_parts::with_sort(pers, st, sum_parts::inductive_shape_dup(p), s) {
                        Err(e) => Err(e),
                        Ok(p2) => match native_caps_at(pers, st, &p2, is_rec) {
                            Err(e) => Err(e),
                            Ok(caps) => {
                                let stored =
                                    IConstantInfo::IndInfo(env::i_constant_val_dup(&cv_ta), caps);
                                Ok((env::ifenv_push(fe, stored), cv_ta, p2))
                            }
                        },
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The constructors' stage (`SumInstall.lean:141-326` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — `xs.contains x` over a `Vec<EIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:163 checkStructFieldSortsI`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:149-167 checkStructFieldSortsI`
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
        let at: Option<EIdx> = if (j as usize) < fvs.len() {
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:156-165 checkStructFieldSortsI`
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
        match read_level(pers, st, u) {
            Err(e) => Err(e),
            Ok(lu) => match read_level(pers, st, s) {
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:173-190 normPosDom`
/// — **official's positivity walk, as a normalisation** (con-leche's task #210
/// Part D): the field's domain is REPLACED by the form official classifies —
/// whnf'd at its own depth, and, while the block occurs, walked under its Π
/// binders.
pub fn norm_pos_dom(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    t: &NIdx,
    d: u64,
    fuel: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(core_types::not_implemented(code_points(&M_POS_FUEL)))
    } else {
        match struct_parts::mentions_const(pers, st, t, e) {
            Err(er) => Err(er),
            Ok(false) => Ok(e.dup2()),
            Ok(true) => match core::whnf(pers, vis, st, mode, fe, core::CHECK_FUEL, d, e) {
                Err(er) => Err(er),
                Ok(w) => match struct_parts::mentions_const(pers, st, t, &w) {
                    Err(er) => Err(er),
                    Ok(false) => Ok(w),
                    Ok(true) => norm_pos_dom_at(pers, vis, st, mode, fe, t, d, fuel - 1, &w),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:180-190 normPosDom`
/// — the walk under a Π binder: a domain that mentions the block is official's
/// non-positive occurrence, and the body is normalised one frame down.
pub fn norm_pos_dom_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    t: &NIdx,
    d: u64,
    fuel: u64,
    w: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, w) {
        Err(er) => Err(er),
        Ok(ENodeView::ForallE(dom, body, bm)) => match struct_parts::mentions_const(pers, st, t, &dom) {
            Err(er) => Err(er),
            Ok(true) => fail(core_types::invalid(code_points(&M_POS_NEG))),
            Ok(false) => match intern_e(pers, st, ENodeView::FVar(d, dom.dup2())) {
                Err(er) => Err(er),
                Ok(fv) => match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                    Err(er) => Err(er),
                    Ok(opened) => match norm_pos_dom(pers, vis, st, mode, fe, t, d + 1, fuel, &opened) {
                        Err(er) => Err(er),
                        Ok(body2) => {
                            match expr_ops::abstract1_fast(pers, st, CORE_WALK_FUEL, &body2, d, 0) {
                                Err(er) => Err(er),
                                Ok(closed) => intern_e(pers, st, ENodeView::ForallE(dom, closed, bm)),
                            }
                        }
                    },
                },
            },
        },
        Ok(_) => Ok(w.dup2()),
    }
}

/// con-leche: none — the twin's `normPosDom … 1024 dom`, the positivity walk's own budget
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:202 normFieldDoms`.
pub const POS_WALK_FUEL: u64 = 1024;

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:196-207 normFieldDoms`
/// — the constructor's field binders with their domains normalised, opened at
/// the free variables `i ..< i + n`; the residual returned scoped at those
/// variables.  Lean conses on the way out; the port pushes on the way in.
#[allow(clippy::too_many_arguments)]
pub fn norm_field_doms(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    t: &NIdx,
    i: u64,
    n: u64,
    h: &EIdx,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<(Vec<(EIdx, BinderMeta)>, EIdx), CheckError> {
    if n == 0 {
        Ok((out, h.dup2()))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, bm)) => {
                match norm_pos_dom(pers, vis, st, mode, fe, t, i, POS_WALK_FUEL, &dom) {
                    Err(e) => Err(e),
                    Ok(dom2) => match intern_e(pers, st, ENodeView::FVar(i, dom)) {
                        Err(e) => Err(e),
                        Ok(fv) => {
                            match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                                Err(e) => Err(e),
                                Ok(opened) => {
                                    let mut o: Vec<(EIdx, BinderMeta)> = out;
                                    o.push((dom2, bm));
                                    norm_field_doms(pers, vis, st, mode, fe, t, i + 1, n - 1, &opened, o)
                                }
                            }
                        }
                    },
                }
            }
            Ok(_) => fail(core_types::not_implemented(code_points(&M_FIELD_TELE))),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:213-218 zipFvarDoms`
/// — `List.zipWith (fun x b => (x.fvarTypeD, b.2)) fvsP cbs`, as a cursor
/// recursion: the map's body reads the store, so con-leche's `zipWith` closure
/// becomes a helper.
pub fn zip_fvar_doms(
    pers: &PersTier,
    st: &AState,
    xs: &Vec<EIdx>,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    if i >= xs.len() || i >= bs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(pers, st, &xs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((t, expr::binder_meta_dup(&bs[i].1)));
                zip_fvar_doms(pers, st, xs, bs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:225-235 normCtorVal`
/// — the checked constructor with its field domains normalised, closed back
/// into a telescope and — when anything changed — checked as the constructor's
/// type in its place, from scratch.
#[allow(clippy::too_many_arguments)]
pub fn norm_ctor_val(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    t: &NIdx,
    n_p: u64,
    n_f: u64,
    cv_c: &IConstantVal,
    cv_ca: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p, &cv_ca.ty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
        Ok(Some(cq)) => match checker_base::open_pis_at_fvars_f(pers, st, n_p, &cv_ca.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_CTOR_TELE))),
            Ok(Some(pq)) => match zip_fvar_doms(pers, st, &pq.0, &cq.0, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(pbs) => match norm_field_doms(pers, vis, st, mode, fe, t, n_p, n_f, &pq.1, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(fq) => {
                        let all: Vec<(EIdx, BinderMeta)> =
                            expr_ops::binder_copy_from(&fq.0, 0, pbs);
                        match close_telescope(pers, st, &all, 0, 0, &fq.1) {
                            Err(e) => Err(e),
                            Ok(ty2) => {
                                if ty2.eq2(&cv_ca.ty) {
                                    Ok(env::i_constant_val_dup(cv_ca))
                                } else {
                                    let cv2 = IConstantVal {
                                        name: cv_c.name.dup2(),
                                        level_params: env::nidx_vec_dup(&cv_c.level_params),
                                        ty: ty2,
                                    };
                                    checker_base::check_constant_val(pers, vis, st, mode, fe, &cv2)
                                }
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:243-277 checkSumCtor`
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
        Ok(cv_ca0) => match norm_ctor_val(pers, fe.visible_below, st, mode, fe, t, n_p, n_f, cv_c, &cv_ca0) {
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
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:255-277 checkSumCtor`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:262-277 checkSumCtor`
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
        Ok(us) => match intern_e(pers, st, ENodeView::Const(t.dup2(), us)) {
            Err(e) => Err(e),
            Ok(hd) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, xrest) {
                Err(e) => Err(e),
                Ok(xfn) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, xrest) {
                    Err(e) => Err(e),
                    Ok(xargs) => {
                        let pre: Vec<EIdx> = expr_ops::take_eidx(&xargs, n_p as usize);
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:270-277 checkSumCtor`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:270-271 checkSumCtor`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:273-274 checkSumCtor`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:255-267 checkSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:130-140 checkSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:283-293 checkSumCtors`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:142-145 consSumCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:299-301 consSumCtors`
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

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
/// Lean twin: `proof/ConRon/Arena/Inductives/SumInstall.lean:309-318 sumRules`
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
