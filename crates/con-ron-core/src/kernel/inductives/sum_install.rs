//! `ConLeche/Kernel/Inductives/SumInstall.lean` and its index-threaded twins
//! `ConLeche/Kernel/Inductives/SumInstallF.lean` — the **former's and the
//! constructors' stages**, which the fixpoint route uses verbatim: the
//! official telescope loop, the constructors' checks with official's
//! positivity walk as a *normalisation*, and the stored rules.

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::decl_check;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{
    CheckMode, ConstantInfo, ConstantVal, IndCaps, RecRule, RecRuleFire,
};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::struct_install;
use crate::kernel::inductives::struct_parts;
use crate::kernel::inductives::sum_parts;
use crate::kernel::inductives::sum_parts::InductiveShape;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use std::vec::Vec;

/// con-leche: none — replaces the `capsOf : InductiveShape → IndCaps` argument of `checkSumInd`
/// The one-method trait that stands for `checkSumInd`'s capability-record
/// argument (task #9's pattern 1; §3.4 forbids closures).  The one
/// implementation is the fixpoint route's `nativeCapsAt p₁ isRec`
/// (`native_install::NativeCapsAt`); the sum route that also instantiated it
/// was deleted at con-leche's task #210 Part C.
pub trait CapsOf {
    /// con-leche: none — the `capsOf` of `checkSumInd capsOf`
    fn caps_of(&self, p: &InductiveShape) -> IndCaps;
}

// ---------------------------------------------------------------------------
// The former's telescope (`SumInstall.lean:43-107`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:45-68 whnfTelescope
/// **Official's telescope loop** (`check_inductive_types`): peel `n` Π binders
/// off `e`, reducing the residual to weak head normal form before each binder
/// and at the end, where it must be a sort.  Binder `i` is opened at the free
/// variable `i`, so the returned binder domains and the sort are scoped at the
/// free variables `0 ..< n`.
///
/// Deviation: the binder list is accumulated on the way *in* (task #13's
/// pattern 3), which gives the same outermost-first list.
pub fn whnf_telescope(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    i: u64,
    n: u64,
    e: &Expr,
    out: Vec<(Expr, BinderMeta)>,
) -> CheckM<(Vec<(Expr, BinderMeta)>, Level)> {
    const M_SORT: [u32; 66] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101,
        100, 117, 99, 101, 32, 116, 111, 32, 97, 32, 115, 111, 114, 116, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_TELE: [u32; 70] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101,
        100, 117, 99, 101, 32, 116, 111, 32, 97, 32, 116, 101, 108, 101, 115, 99, 111, 112,
        101, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    match core_c::whnf(mode, core_k::check_fuel(), st, fe, i, e) {
        Err(err) => Err(err),
        Ok(w) => {
            if n == 0 {
                match &w.0.kind {
                    ExprKind::Sort(s) => Ok((out, level::dup(s))),
                    _ => Err(core_types::invalid(core_types::code_points(&M_SORT))),
                }
            } else {
                match &w.0.kind {
                    ExprKind::ForallE(dom, body, bm) => {
                        let dom2: Expr = expr::dup(dom);
                        let fv: Expr = expr::fvar(i, expr::dup(dom));
                        let opened: Expr = expr_ops::instantiate1(body, &fv, 0);
                        let mut out = out;
                        out.push((dom2, expr::binder_meta_dup(bm)));
                        whnf_telescope(mode, st, fe, i + 1, n - 1, &opened, out)
                    }
                    _ => Err(core_types::invalid(core_types::code_points(&M_TELE))),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:70-78 closeTelescope
/// Close a telescope opened at the free variables `i ..< i + bs.length` back
/// into a syntactic Π-telescope over `body`: innermost binder first, each
/// abstraction turning the binder's own free variable into the bound one.
/// Built on the way out, as cited; `k` is the cursor into `bs`.
pub fn close_telescope(bs: &Vec<(Expr, BinderMeta)>, k: usize, i: u64, body: &Expr) -> Expr {
    if k >= bs.len() {
        expr::dup(body)
    } else {
        let rest: Expr = close_telescope(bs, k + 1, i + 1, body);
        expr::forall_e(
            expr::dup(&bs[k].0),
            expr_ops::abstract1(&rest, i, 0),
            expr::binder_meta_dup(&bs[k].1),
        )
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
/// The type former's TELESCOPE: the checked declared type when it is already
/// a syntactic telescope of `n` Π binders ending in a sort, else the declared
/// type's whnf'd telescope, closed and checked as the former's type in its
/// place — `checkConstantVal` from scratch, so nothing about the reduction is
/// trusted.
pub fn check_sum_tele(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    n: u64,
    cv_ta0: &ConstantVal,
) -> CheckM<(ConstantVal, Level)> {
    match expr_ops::strip_pis(n, &cv_ta0.ty) {
        Some(q) => match &q.1 .0.kind {
            ExprKind::Sort(s) => Ok((env::constant_val_dup(cv_ta0), level::dup(s))),
            _ => check_sum_tele_whnf(mode, st, fe, cv, n, cv_ta0),
        },
        None => check_sum_tele_whnf(mode, st, fe, cv, n, cv_ta0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:80-94 checkSumTele
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:20-30 checkSumTeleF
/// The `| _ => do …` arm of `checkSumTele`, split off so the syntactic arm
/// above stays a tail position (task #18's pattern 3; the cited `match`'s
/// fallthrough arm is reached from two patterns here, a `Vec`'s having no
/// nested `some (_, .sort s)` pattern).
pub fn check_sum_tele_whnf(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    n: u64,
    cv_ta0: &ConstantVal,
) -> CheckM<(ConstantVal, Level)> {
    match whnf_telescope(mode, st, fe, 0, n, &cv_ta0.ty, Vec::new()) {
        Err(err) => Err(err),
        Ok(q) => {
            let closed: Expr =
                close_telescope(&q.0, 0, 0, &expr::sort(level::dup(&q.1)));
            let cv2 = ConstantVal {
                name: name::dup(&cv.name),
                level_params: prop_when::names_copy(&cv.level_params),
                ty: closed,
            };
            match checker_base::check_constant_val(mode, st, fe, &cv2) {
                Err(err) => Err(err),
                Ok(cv_ta) => Ok((cv_ta, q.1)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:96-112 checkSumInd
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:32-43 checkSumIndF
/// Stage 1: the type former, stored with the block's capability record at its
/// telescope; returns the record completed with the result sort, which every
/// later stage runs on.
///
/// Deviation: the index is threaded by value and returned (task #14), so the
/// result's first component is the pushed index rather than a cons.
pub fn check_sum_ind<C>(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    p: InductiveShape,
    caps_of: &C,
) -> CheckM<(FEnv, ConstantVal, InductiveShape)>
where
    C: CapsOf,
{
    const M_TELE: [u32; 40] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32, 32,
    ];
    const M_SORT: [u32; 43] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 114, 101, 115, 117, 108, 116, 32, 115, 111, 114, 116, 32,
        32, 32, 32, 32, 32, 32, 32,
    ];
    match checker_base::check_constant_val(mode, st, &fe, &p.cv_t) {
        Err(err) => Err(err),
        Ok(cv_ta0) => {
            match check_sum_tele(mode, st, &fe, &p.cv_t, p.n_p + p.n_idx, &cv_ta0) {
                Err(err) => Err(err),
                Ok(q) => {
                    let cv_ta: ConstantVal = q.0;
                    let s: Level = q.1;
                    match expr_ops::strip_pis(p.n_p + p.n_idx, &cv_ta.ty) {
                        None => {
                            Err(core_types::internal(core_types::code_points(&M_TELE)))
                        }
                        Some(tq) => {
                            if !expr::beq(&tq.1, &expr::sort(level::dup(&s))) {
                                Err(core_types::internal(core_types::code_points(&M_SORT)))
                            } else {
                                let p2: InductiveShape =
                                    sum_parts::with_sort(p, level::dup(&s));
                                let caps: IndCaps = caps_of.caps_of(&p2);
                                let fe2: FEnv = fenv::push(
                                    fe,
                                    ConstantInfo::IndInfo(
                                        env::constant_val_dup(&cv_ta),
                                        caps,
                                    ),
                                );
                                Ok((fe2, cv_ta, p2))
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The fields' sorts (`SumInstall.lean:118-152`)
// ---------------------------------------------------------------------------

/// con-leche: none — `idxArgs.contains fv` over a `Vec<Expr>`
/// `List.contains` at `BEq Expr`, as an index recursion (task #3's pattern).
pub fn exprs_contains(xs: &Vec<Expr>, e: &Expr) -> bool {
    exprs_contains_from(xs, e, 0)
}

/// con-leche: none — the index recursion behind `exprs_contains`
pub fn exprs_contains_from(xs: &Vec<Expr>, e: &Expr, i: usize) -> bool {
    if i >= xs.len() {
        false
    } else if expr::beq(&xs[i], e) {
        true
    } else {
        exprs_contains_from(xs, e, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:114-139 checkStructFieldSortsI
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:45-61 checkStructFieldSortsIF
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:63-81 checkStructFieldSortsIFA
/// The fields' sorts over the opened constructor telescope, with the official
/// per-field universe bound unless the family is propositional: at a `Prop`
/// family with a large eliminator every field must be a proposition OR one of
/// the residual's index expressions (official's
/// `elim_only_at_universe_zero` for one constructor — the
/// subsingleton-elimination criterion, `Eq`'s rule).  Walks the fields from
/// the last to the first and returns the sorts in field order.
///
/// The `Array` twin is the same function (one list type in the port).
pub fn check_struct_field_sorts_i(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    is_prop: bool,
    large: bool,
    s: &Level,
    n_p: u64,
    fvs: &Vec<Expr>,
    idx_args: &Vec<Expr>,
    j: u64,
) -> CheckM<Vec<Level>> {
    const M_IDX: [u32; 28] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32,
        105, 110, 100, 101, 120, 32, 32, 32, 32, 32,
    ];
    const M_BIG: [u32; 38] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32,
        117, 110, 105, 118, 101, 114, 115, 101, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101,
        32, 32,
    ];
    const M_ELIM: [u32; 72] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 108, 97, 114, 103, 101, 32,
        101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 119, 105, 116, 104, 32, 97, 32,
        110, 111, 110, 45, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32,
        102, 105, 101, 108, 100, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    if j == 0 {
        Ok(Vec::new())
    } else {
        let i: u64 = j - 1;
        if (i as usize) >= fvs.len() {
            Err(core_types::internal(core_types::code_points(&M_IDX)))
        } else {
            let fv: Expr = expr::dup(&fvs[i as usize]);
            let dom: Expr = expr_ops::fvar_type_d(&fv);
            match core_c::infer(mode, core_k::check_fuel(), st, fe, n_p + i, &dom) {
                Err(err) => Err(err),
                Ok(ty) => {
                    match core_c::ensure_sort_i(
                        mode,
                        core_k::check_fuel(),
                        st,
                        fe,
                        n_p + i,
                        &ty,
                    ) {
                        Err(err) => Err(err),
                        Ok(u) => {
                            let guard: CheckM<()> = if !is_prop {
                                match core_k::lift_fueled(level::leq(&u, s)) {
                                    Err(err) => Err(err),
                                    Ok(true) => Ok(()),
                                    Ok(false) => Err(core_types::invalid(
                                        core_types::code_points(&M_BIG),
                                    )),
                                }
                            } else if large {
                                let ok = match level::is_equiv(&u, &level::zero()) {
                                    Some(true) => true,
                                    Some(false) => exprs_contains(idx_args, &fv),
                                    None => exprs_contains(idx_args, &fv),
                                };
                                if ok {
                                    Ok(())
                                } else {
                                    Err(core_types::invalid(core_types::code_points(
                                        &M_ELIM,
                                    )))
                                }
                            } else {
                                Ok(())
                            };
                            match guard {
                                Err(err) => Err(err),
                                Ok(()) => match check_struct_field_sorts_i(
                                    mode, st, fe, is_prop, large, s, n_p, fvs, idx_args, i,
                                ) {
                                    Err(err) => Err(err),
                                    Ok(rest) => {
                                        let mut rest = rest;
                                        rest.push(u);
                                        Ok(rest)
                                    }
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Official's positivity walk as a normalisation (`SumInstall.lean:154-216`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:141-175 normPosDom
/// **Official's positivity walk, as a normalisation**: `check_positivity`
/// reduces a constructor field's type to weak head normal form before
/// classifying it, and again under every Π binder of a reflexive field.  So
/// the field's domain is REPLACED by the form official classifies.  A domain
/// the block does not occur in is kept as declared, unreduced.  `fuel` bounds
/// the Π walk; exhaustion is a positive decline.
pub fn norm_pos_dom(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    t: &Name,
    d: u64,
    fuel: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_FUEL: [u32; 34] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 112, 111, 115, 105, 116, 105,
        118, 105, 116, 121, 32, 119, 97, 108, 107, 32, 102, 117, 101, 108, 32, 32,
    ];
    const M_NEG: [u32; 55] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 110, 111, 110, 32, 112, 111,
        115, 105, 116, 105, 118, 101, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32,
        111, 102, 32, 116, 104, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 32,
        32,
    ];
    if fuel == 0 {
        Err(core_types::not_implemented(core_types::code_points(&M_FUEL)))
    } else if !struct_parts::mentions_const(t, e) {
        Ok(expr::dup(e))
    } else {
        match core_c::whnf(mode, core_k::check_fuel(), st, fe, d, e) {
            Err(err) => Err(err),
            Ok(w) => {
                if !struct_parts::mentions_const(t, &w) {
                    Ok(w)
                } else {
                    match &w.0.kind {
                        ExprKind::ForallE(dom, body, bm) => {
                            if struct_parts::mentions_const(t, dom) {
                                Err(core_types::invalid(core_types::code_points(&M_NEG)))
                            } else {
                                let dom2: Expr = expr::dup(dom);
                                let bm2: BinderMeta = expr::binder_meta_dup(bm);
                                let fv: Expr = expr::fvar(d, expr::dup(dom));
                                let opened: Expr = expr_ops::instantiate1(body, &fv, 0);
                                match norm_pos_dom(
                                    mode,
                                    st,
                                    fe,
                                    t,
                                    d + 1,
                                    fuel - 1,
                                    &opened,
                                ) {
                                    Err(err) => Err(err),
                                    Ok(body2) => Ok(expr::forall_e(
                                        dom2,
                                        expr_ops::abstract1(&body2, d, 0),
                                        bm2,
                                    )),
                                }
                            }
                        }
                        _ => Ok(w),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:177-188 normFieldDoms
/// The constructor's field binders with their domains normalised
/// (`normPosDom`), opened at the free variables `i ..< i + n` as
/// `whnfTelescope` opens the former's; the residual returned scoped at those
/// variables.  The `1024` fuel is the cited literal.
pub fn norm_field_doms(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    t: &Name,
    i: u64,
    n: u64,
    e: &Expr,
    out: Vec<(Expr, BinderMeta)>,
) -> CheckM<(Vec<(Expr, BinderMeta)>, Expr)> {
    const M_TELE: [u32; 47] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 102, 105, 101, 108, 100, 32, 116, 101, 108, 101, 115, 99,
        111, 112, 101, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    if n == 0 {
        Ok((out, expr::dup(e)))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(dom, body, bm) => {
                match norm_pos_dom(mode, st, fe, t, i, 1024, dom) {
                    Err(err) => Err(err),
                    Ok(dom2) => {
                        let fv: Expr = expr::fvar(i, expr::dup(dom));
                        let opened: Expr = expr_ops::instantiate1(body, &fv, 0);
                        let mut out = out;
                        out.push((dom2, expr::binder_meta_dup(bm)));
                        norm_field_doms(mode, st, fe, t, i + 1, n - 1, &opened, out)
                    }
                }
            }
            _ => Err(core_types::not_implemented(core_types::code_points(&M_TELE))),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:83-95 normCtorValF
/// The checked constructor with its field domains normalised: the parameter
/// binders as declared, the field binders through `normFieldDoms`, closed back
/// into a telescope and — when anything changed — checked as the
/// constructor's type in its place, from scratch.
pub fn norm_ctor_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    t: &Name,
    n_p: u64,
    n_f: u64,
    cv_c: &ConstantVal,
    cv_ca: &ConstantVal,
) -> CheckM<ConstantVal> {
    const M_TELE: [u32; 41] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32, 32, 32,
    ];
    match expr_ops::strip_pis(n_p, &cv_ca.ty) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_TELE))),
        Some(cq) => match checker_base::open_pis_at_fvars_f(n_p, &cv_ca.ty, 0) {
            None => Err(core_types::not_implemented(core_types::code_points(&M_TELE))),
            Some(oq) => {
                let pbs: Vec<(Expr, BinderMeta)> = zip_param_binders(&oq.0, &cq.0);
                match norm_field_doms(mode, st, fe, t, n_p, n_f, &oq.1, Vec::new()) {
                    Err(err) => Err(err),
                    Ok(fq) => {
                        let all: Vec<(Expr, BinderMeta)> = append_binders(pbs, &fq.0);
                        let ty2: Expr = close_telescope(&all, 0, 0, &fq.1);
                        if expr::beq(&ty2, &cv_ca.ty) {
                            Ok(env::constant_val_dup(cv_ca))
                        } else {
                            let cv2 = ConstantVal {
                                name: name::dup(&cv_c.name),
                                level_params: prop_when::names_copy(&cv_c.level_params),
                                ty: ty2,
                            };
                            checker_base::check_constant_val(mode, st, fe, &cv2)
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
/// `List.zipWith (fun x b => (x.fvarTypeD, b.2)) fvsP cbs`: the opened
/// parameter variables' annotations with the declared binders' data.
pub fn zip_param_binders(
    fvs: &Vec<Expr>,
    cbs: &Vec<(Expr, BinderMeta)>,
) -> Vec<(Expr, BinderMeta)> {
    zip_param_binders_from(fvs, cbs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:190-205 normCtorVal
/// The index recursion behind `zip_param_binders`; `List.zipWith` stops at
/// the shorter list, as this does.
pub fn zip_param_binders_from(
    fvs: &Vec<Expr>,
    cbs: &Vec<(Expr, BinderMeta)>,
    i: usize,
    out: Vec<(Expr, BinderMeta)>,
) -> Vec<(Expr, BinderMeta)> {
    if i >= fvs.len() {
        out
    } else if i >= cbs.len() {
        out
    } else {
        let mut out = out;
        out.push((
            expr_ops::fvar_type_d(&fvs[i]),
            expr::binder_meta_dup(&cbs[i].1),
        ));
        zip_param_binders_from(fvs, cbs, i + 1, out)
    }
}

/// con-leche: none — `++` over a `Vec<(Expr, BinderMeta)>`
/// Lean's list append, which shares; a `Vec` copies the spine.
pub fn append_binders(
    xs: Vec<(Expr, BinderMeta)>,
    ys: &Vec<(Expr, BinderMeta)>,
) -> Vec<(Expr, BinderMeta)> {
    append_binders_from(xs, ys, 0)
}

/// con-leche: none — the index recursion behind `append_binders`
pub fn append_binders_from(
    xs: Vec<(Expr, BinderMeta)>,
    ys: &Vec<(Expr, BinderMeta)>,
    i: usize,
) -> Vec<(Expr, BinderMeta)> {
    if i >= ys.len() {
        xs
    } else {
        let mut xs = xs;
        xs.push((expr::dup(&ys[i].0), expr::binder_meta_dup(&ys[i].1)));
        append_binders_from(xs, ys, i + 1)
    }
}

// ---------------------------------------------------------------------------
// The constructors' stage (`SumInstall.lean:219-279`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
/// The syntactic half of `checkSumCtor`'s tail: the opened residual is the
/// family at the opened parameter variables followed by `nIdx` index
/// expressions.  Split off so the cited `&&` cascade's arms stay tail
/// positions.
pub fn opened_resid_ok(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<Expr>,
    resid: &Expr,
) -> bool {
    let head: Expr = expr_ops::get_app_fn(resid);
    let expected: Expr = expr::mk_const(name::dup(t), struct_parts::params_of(lps));
    if expr::beq(&head, &expected) {
        let args: Vec<Expr> = expr_ops::get_app_args(resid);
        if expr::exprs_beq(&expr_ops::take_exprs(&args, n_p as usize), fvs_p) {
            args.len() as u64 == n_p + n_idx
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
/// `xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀` — every field domain
/// resolves in the pre-block environment.
pub fn field_doms_resolve_from(fe0: &FEnv, fvs: &Vec<Expr>, i: usize) -> bool {
    if i >= fvs.len() {
        true
    } else {
        let dom: Expr = expr_ops::fvar_type_d(&fvs[i]);
        if decl_check::consts_resolve_f_fast(fe0, &dom) {
            field_doms_resolve_from(fe0, fvs, i + 1)
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
/// `(xq.2.getAppArgs.drop nP).all fun e => e.constsResolveF fe₀` — the index
/// expressions never mention the block (official `is_valid_ind_app`).
pub fn index_args_resolve_from(fe0: &FEnv, args: &Vec<Expr>, i: usize) -> bool {
    if i >= args.len() {
        true
    } else if decl_check::consts_resolve_f_fast(fe0, &args[i]) {
        index_args_resolve_from(fe0, args, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:207-253 checkSumCtor
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:97-128 checkSumCtorF
/// Stage 2, one constructor's type: the ordinary constant check, the
/// normalised constructor, the annotated result shape, the parameter pins
/// against the type former's opened telescope, the pre-block resolution of
/// the field domains, and the per-field universe bound.  Returns the
/// annotated constructor and its fields' sorts.
pub fn check_sum_ctor(
    mode: &CheckMode,
    st: &mut CState,
    fe0: &FEnv,
    fe: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    res_sort: &Level,
    is_prop: bool,
    large: bool,
    cv_c: &ConstantVal,
    n_f: u64,
    cv_ta: &ConstantVal,
) -> CheckM<(ConstantVal, Vec<Level>)> {
    const M_CTELE: [u32; 41] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32, 32, 32,
    ];
    const M_RET: [u32; 45] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 105, 110, 118, 97, 108, 105,
        100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 116, 117,
        114, 110, 32, 116, 121, 112, 101, 32, 32,
    ];
    const M_TTELE: [u32; 40] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32, 32,
    ];
    const M_FTELE: [u32; 47] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 102, 105, 101, 108, 100, 32, 116, 101, 108, 101, 115, 99,
        111, 112, 101, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_RESID: [u32; 45] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 111, 112, 101, 110, 101, 100,
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 114, 101, 115, 105, 100,
        117, 97, 108, 32, 32, 32, 32, 32, 32,
    ];
    const M_DOM: [u32; 47] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32,
        100, 111, 109, 97, 105, 110, 32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 98,
        108, 111, 99, 107, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_IDX: [u32; 50] = [
        100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 105, 110, 100, 101, 120, 32,
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 109, 101, 110, 116, 105, 111,
        110, 115, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 32, 32,
    ];
    match checker_base::check_constant_val(mode, st, fe, cv_c) {
        Err(err) => Err(err),
        Ok(cv_ca0) => {
            match norm_ctor_val(mode, st, fe, t, n_p, n_f, cv_c, &cv_ca0) {
                Err(err) => Err(err),
                Ok(cv_ca) => match expr_ops::strip_pis(n_p + n_f, &cv_ca.ty) {
                    None => Err(core_types::not_implemented(core_types::code_points(
                        &M_CTELE,
                    ))),
                    Some(bq) => {
                        if !struct_parts::struct_ctor_resid_ok(
                            t, lps, n_p, n_f, n_idx, &bq.1,
                        ) {
                            Err(core_types::invalid(core_types::code_points(&M_RET)))
                        } else {
                            match checker_base::open_pis_at_fvars_f(n_p, &cv_ca.ty, 0) {
                                None => Err(core_types::not_implemented(
                                    core_types::code_points(&M_CTELE),
                                )),
                                Some(cq) => {
                                    match checker_base::open_pis_at_fvars_f(
                                        n_p, &cv_ta.ty, 0,
                                    ) {
                                        None => Err(core_types::not_implemented(
                                            core_types::code_points(&M_TTELE),
                                        )),
                                        Some(tq) => {
                                            let doms: Vec<Expr> =
                                                checker_base::fvar_types(&tq.0);
                                            match struct_install::check_struct_doms_at(
                                                mode, st, fe, 0, &cq.0, &doms, n_p,
                                            ) {
                                                Err(err) => Err(err),
                                                Ok(()) => {
                                                    match checker_base::open_pis_at_fvars_f(
                                                        n_f, &cq.1, n_p,
                                                    ) {
                                                        None => {
                                                            Err(core_types::not_implemented(
                                                                core_types::code_points(
                                                                    &M_FTELE,
                                                                ),
                                                            ))
                                                        }
                                                        Some(xq) => {
                                                            let idx_args: Vec<Expr> =
                                                                core_k::drop_exprs(
                                                                    &expr_ops::get_app_args(
                                                                        &xq.1,
                                                                    ),
                                                                    n_p as usize,
                                                                );
                                                            if !opened_resid_ok(
                                                                t, lps, n_p, n_idx, &cq.0,
                                                                &xq.1,
                                                            ) {
                                                                Err(core_types::not_implemented(
                                                                    core_types::code_points(
                                                                        &M_RESID,
                                                                    ),
                                                                ))
                                                            } else if !field_doms_resolve_from(
                                                                fe0, &xq.0, 0,
                                                            ) {
                                                                Err(core_types::not_implemented(
                                                                    core_types::code_points(
                                                                        &M_DOM,
                                                                    ),
                                                                ))
                                                            } else if !index_args_resolve_from(
                                                                fe0, &idx_args, 0,
                                                            ) {
                                                                Err(core_types::invalid(
                                                                    core_types::code_points(
                                                                        &M_IDX,
                                                                    ),
                                                                ))
                                                            } else {
                                                                match check_struct_field_sorts_i(
                                                                    mode, st, fe, is_prop,
                                                                    large, res_sort, n_p,
                                                                    &xq.0, &idx_args, n_f,
                                                                ) {
                                                                    Err(err) => Err(err),
                                                                    Ok(sorts) => {
                                                                        Ok((cv_ca, sorts))
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
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
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:255-267 checkSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:130-140 checkSumCtorsF
/// Stage 2, all constructors' types, at the environment holding the type
/// former; returns the annotated constructors with their field counts, and
/// beside them the constructors' field sorts.  The two accumulators are
/// pushed on the way in (task #13's pattern 3).
pub fn check_sum_ctors(
    mode: &CheckMode,
    st: &mut CState,
    fe0: &FEnv,
    fe: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    res_sort: &Level,
    is_prop: bool,
    large: bool,
    cv_ta: &ConstantVal,
    cs: &Vec<(ConstantVal, u64)>,
    i: usize,
    out: Vec<(ConstantVal, u64)>,
    souts: Vec<Vec<Level>>,
) -> CheckM<(Vec<(ConstantVal, u64)>, Vec<Vec<Level>>)> {
    if i >= cs.len() {
        Ok((out, souts))
    } else {
        match check_sum_ctor(
            mode, st, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large, &cs[i].0,
            cs[i].1, cv_ta,
        ) {
            Err(err) => Err(err),
            Ok(q) => {
                let mut out = out;
                let mut souts = souts;
                out.push((q.0, cs[i].1));
                souts.push(q.1);
                check_sum_ctors(
                    mode, st, fe0, fe, t, lps, n_p, n_idx, res_sort, is_prop, large,
                    cv_ta, cs, i + 1, out, souts,
                )
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:269-272 consSumCtors
/// con-leche: ConLeche/Kernel/Inductives/SumInstallF.lean:142-145 consSumCtorsF
/// The constructors' conses, in order (the first constructor deepest).
pub fn cons_sum_ctors(n_p: u64, cs: &Vec<(ConstantVal, u64)>, i: usize, fe: FEnv) -> FEnv {
    if i >= cs.len() {
        fe
    } else {
        let fe2: FEnv = fenv::push(
            fe,
            ConstantInfo::CtorInfo(env::constant_val_dup(&cs[i].0), n_p, cs[i].1),
        );
        cons_sum_ctors(n_p, cs, i + 1, fe2)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
/// The stored rules: constructor `j`'s with the generated right-hand side
/// `j`, plain when the generated type's major is the family at the parameters
/// (always, by construction), carrying the two rescue bits `recRuleBits`
/// reads off the block's own store — and `paramsBlind`, because the route's
/// rule law holds at any pair of fitting parameter spines.
///
/// Deviations: the `find? : Name → Option ConstantInfo` argument is the index
/// itself (`fe`), as everywhere in the port; the two-list recursion is an
/// index recursion whose "one list ran out" arm is the cited `| _, _ => []`.
pub fn sum_rules(
    fe: &FEnv,
    rec_name: &Name,
    n_p: u64,
    m_i: u64,
    r_p: u64,
    rec_ty: &Expr,
    cs: &Vec<(ConstantVal, u64)>,
    rhss: &Vec<Expr>,
) -> Vec<RecRule> {
    sum_rules_from(fe, rec_name, n_p, m_i, r_p, rec_ty, cs, rhss, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/SumInstall.lean:274-290 sumRules
/// The index recursion behind `sum_rules`.
pub fn sum_rules_from(
    fe: &FEnv,
    rec_name: &Name,
    n_p: u64,
    m_i: u64,
    r_p: u64,
    rec_ty: &Expr,
    cs: &Vec<(ConstantVal, u64)>,
    rhss: &Vec<Expr>,
    i: usize,
    out: Vec<RecRule>,
) -> Vec<RecRule> {
    if i >= cs.len() {
        out
    } else if i >= rhss.len() {
        out
    } else {
        let fire = if expr_ops::rec_rule_plain(rec_ty, m_i, r_p, n_p) {
            RecRuleFire::Plain
        } else {
            RecRuleFire::Inert
        };
        let rl = RecRule {
            ctor: name::dup(&cs[i].0.name),
            nfields: cs[i].1,
            ctor_params: n_p,
            fire,
            rhs: expr::dup(&rhss[i]),
            k: false,
            eta: false,
            params_blind: true,
        };
        let mut out = out;
        out.push(core_k::rec_rule_bits(fe, rec_name, rl));
        sum_rules_from(fe, rec_name, n_p, m_i, r_p, rec_ty, cs, rhss, i + 1, out)
    }
}
