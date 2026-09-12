//! `ConLeche/Kernel/Inductives/NativeInstall.lean` and its index-threaded
//! twins `ConLeche/Kernel/Inductives/NativeInstallF.lean` — **the direct
//! recursive install**: the capability record, the positivity
//! classification's install-time re-check, the generated recursor and its
//! rules, the projection table at a structure-like block, and the two-pass
//! driver.
//!
//! ## Two `fenv::dup`s, and why
//!
//! con-leche's index is persistent: `fe.push` and `fe.restrictTo` leave their
//! argument intact because the runtime shares the `Std.HashMap` field.  The
//! port threads an `FEnv` linearly (task #14's ruling: by value, returned),
//! which is exact and `O(1)` wherever a caller needs *one* view at a time.
//! Two sites here need **two** views at once, and they are the only ones in
//! the directory:
//!
//! * `check_native_pass` hands an index to `check_sum_ind` (which pushes the
//!   former onto it) while `check_native` keeps the pre-block index for the
//!   second pass and for `check_native_tail`;
//! * `check_native_rec` builds `feR = fe.push (.recInfo cvRa … [])` — a
//!   *temporary* view in which the generated rules are scope-checked — while
//!   `check_native_tail` keeps `fe₂` for the rules and the table.
//!
//! Both take `fenv::dup` (task #14's copy: the index is rebuilt with
//! `mk_fenv_go`, the constants themselves stay shared).  That is `O(|env|)`
//! **twice per inductive block**, not per term; it is the price task #14's
//! option 3 named, and the `Rc<HashMap>` index it foreclosed removes it
//! without touching the model, because `abs` reads the index through `find`
//! either way.

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::decl_check;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal, IndCaps};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::native_parts;
use crate::kernel::inductives::native_parts::{NativeParts, RecFieldKind};
use crate::kernel::inductives::struct_install;
use crate::kernel::inductives::struct_parts;
use crate::kernel::inductives::sum_install;
use crate::kernel::inductives::sum_install::CapsOf;
use crate::kernel::inductives::sum_parts;
use crate::kernel::inductives::sum_parts::InductiveShape;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::ron::hashmap::HashMap;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The capability record (`NativeInstall.lean:57-140`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
/// The capabilities a block on the fixpoint route earns: at a
/// **structure-like** block — one constructor, no index, and no recursive or
/// reflexive field (official's `is_structure_like`) — structure eta at a
/// non-`Prop` sort and unit-likeness when the constructor has no field; rule
/// K exactly at official's `is_K_target`; nothing at any other block.  The
/// `is_rec` verdict is a parameter: the former is installed before the
/// constructors are classified.
pub fn native_caps_at(p: &InductiveShape, is_rec: bool) -> IndCaps {
    if p.ctors.len() == 1 {
        let eta = if p.n_idx == 0 {
            if !p.is_prop {
                !is_rec
            } else {
                false
            }
        } else {
            false
        };
        let unitlike = if p.n_idx == 0 {
            p.ctors[0].1 == 0
        } else {
            false
        };
        let rule_k = if p.ctors[0].1 == 0 { p.is_prop } else { false };
        IndCaps {
            eta,
            eta_ctor: name::dup(&p.ctors[0].0.name),
            eta_params: p.n_p,
            eta_fields: p.ctors[0].1,
            unitlike,
            unit_params: p.n_p,
            rule_k,
            sort_z: level::zeroness_of(&p.res_sort),
        }
    } else {
        env::ind_caps_default()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
/// The one implementation of `checkSumInd`'s `capsOf` argument
/// (`sum_install::CapsOf`): `fun p₁ => nativeCapsAt p₁ isRec`, with the
/// closure's captured `isRec` as the dictionary's one field (task #9's
/// pattern 1).
pub struct NativeCapsAt {
    pub is_rec: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
impl CapsOf for NativeCapsAt {
    /// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:59-98 nativeCapsAt
    fn caps_of(&self, p: &InductiveShape) -> IndCaps {
        native_caps_at(p, self.is_rec)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// Official's `is_rec` off the classified kinds: some field is recursive or
/// reflexive.
pub fn native_is_rec(kinds: &Vec<Vec<RecFieldKind>>) -> bool {
    native_is_rec_from(kinds, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// The outer `kinds.any` of `native_is_rec`.
pub fn native_is_rec_from(kinds: &Vec<Vec<RecFieldKind>>, j: usize) -> bool {
    if j >= kinds.len() {
        false
    } else if kinds_any_rec_from(&kinds[j], 0) {
        true
    } else {
        native_is_rec_from(kinds, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// The inner `ks.any fun k => k == .recursive || k == .reflexive`.
pub fn kinds_any_rec_from(ks: &Vec<RecFieldKind>, i: usize) -> bool {
    if i >= ks.len() {
        false
    } else if native_parts::rec_field_kind_beq(&ks[i], &RecFieldKind::Recursive) {
        true
    } else if native_parts::rec_field_kind_beq(&ks[i], &RecFieldKind::Reflexive) {
        true
    } else {
        kinds_any_rec_from(ks, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:105-108 nativeCaps
/// The block's capability record at its classified kinds.
pub fn native_caps(p: &NativeParts) -> IndCaps {
    native_caps_at(&p.shape, native_is_rec(&p.kinds))
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
/// **The syntactic reading of `is_rec`**: does the block occur in some
/// declared field domain of some constructor?  Official's `is_rec` is read
/// off the WHNF'd domains, and the raw occurrence is a superset of it.  Read
/// only where the record depends on it — one constructor — as `nativeCapsAt`
/// does.
pub fn native_raw_rec(p: &NativeParts) -> bool {
    if p.shape.ctors.len() == 1 {
        let c: &(ConstantVal, u64) = &p.shape.ctors[0];
        match expr_ops::strip_pis(p.shape.n_p + c.1, &c.0.ty) {
            Some(q) => {
                dom_mentions_from(&p.shape.cv_t.name, &q.0, p.shape.n_p as usize)
            }
            None => false,
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
/// `(cbs.drop p.nP).any fun b => b.1.mentionsConst p.cvT.name`, as an index
/// recursion (task #3's pattern).
pub fn dom_mentions_from(
    t: &Name,
    cbs: &Vec<(Expr, BinderMeta)>,
    i: usize,
) -> bool {
    if i >= cbs.len() {
        false
    } else if struct_parts::mentions_const(t, &cbs[i].0) {
        true
    } else {
        dom_mentions_from(t, cbs, i + 1)
    }
}

// ---------------------------------------------------------------------------
// `mentionsFvar` and its memoized walk (`NativeInstall.lean:141-395`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:139-141 Expr.mentionsFvar
/// Does the variable `q` occur as a leaf of `e` (annotations included, as
/// `fvarLeaves` walks them)?  The *logical* definition — `e.fvarLeaves.any`,
/// whose list is tree-sized by construction; the executed one is
/// `mentions_fvar` below (the `@[csimp]` family).
pub fn mentions_fvar_spec(q: u64, e: &Expr) -> bool {
    let leaves: Vec<(u64, Expr)> = expr_ops::fvar_leaves(e);
    leaves_any_from(&leaves, q, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:139-141 Expr.mentionsFvar
/// `e.fvarLeaves.any fun l => l.1 == q`, as an index recursion.
pub fn leaves_any_from(leaves: &Vec<(u64, Expr)>, q: u64, i: usize) -> bool {
    if i >= leaves.len() {
        false
    } else if leaves[i].0 == q {
        true
    } else {
        leaves_any_from(leaves, q, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:214-219 Expr.mentionsFvarIns
/// Record one answer for `e` in the memo the walk hands back.
pub fn mentions_fvar_ins(memo: &mut HashMap<Expr, bool>, e: &Expr, r: bool) {
    memo.insert(expr::dup(e), r);
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
/// The memoized `mentionsFvar` walk: the four leaf arms answer before the
/// probe, every other node is probed, walked and recorded.  Unlike
/// `mentionsConstGo` this walk **does** short-circuit (`| (true, memo) =>
/// (true, memo)`), and the port keeps that.
pub fn mentions_fvar_go(q: u64, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => false,
        ExprKind::Sort(_) => false,
        ExprKind::Const(_, _) => false,
        ExprKind::Lit(_) => false,
        _ => match struct_parts::memo_eb_get(memo, e) {
            Some(r) => r,
            None => {
                let r = mentions_fvar_node(q, memo, e);
                mentions_fvar_ins(memo, e, r);
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
/// The inner `match e with` of the miss branch, split off so the probe's
/// borrow dies before the descent mutates the memo (task #14's rule).  The
/// last arm is the cited unreachable one.
pub fn mentions_fvar_node(q: u64, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Fvar(idx, ty) => {
            if *idx == q {
                true
            } else {
                mentions_fvar_go(q, memo, ty)
            }
        }
        ExprKind::App(f, a) => {
            if mentions_fvar_go(q, memo, f) {
                true
            } else {
                mentions_fvar_go(q, memo, a)
            }
        }
        ExprKind::Lam(ty, b, _) => {
            if mentions_fvar_go(q, memo, ty) {
                true
            } else {
                mentions_fvar_go(q, memo, b)
            }
        }
        ExprKind::ForallE(ty, b, _) => {
            if mentions_fvar_go(q, memo, ty) {
                true
            } else {
                mentions_fvar_go(q, memo, b)
            }
        }
        ExprKind::LetE(t, v, b) => {
            if mentions_fvar_go(q, memo, t) {
                true
            } else if mentions_fvar_go(q, memo, v) {
                true
            } else {
                mentions_fvar_go(q, memo, b)
            }
        }
        ExprKind::Proj(_, _, sub) => mentions_fvar_go(q, memo, sub),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:379-381 Expr.mentionsFvarFast
/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:139-141 Expr.mentionsFvar
/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:383-386 Expr.mentionsFvar_eq_mentionsFvarFast
/// **The executed `mentionsFvar`** — one memoized DAG walk.
pub fn mentions_fvar(q: u64, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    mentions_fvar_go(q, &mut memo, e)
}

// ---------------------------------------------------------------------------
// The kinds re-checked on the annotated constructors
// (`NativeInstall.lean:389-448` / `NativeInstallF.lean:22-70`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// `(es).all (fun e => e.constsResolve env₀)` over the index (the walkers
/// record's `w.resolve`, dissolved — `super`'s module note 3).
pub fn all_resolve_from(fe0: &FEnv, es: &Vec<Expr>, i: usize) -> bool {
    if i >= es.len() {
        true
    } else if decl_check::consts_resolve_f_fast(fe0, &es[i]) {
        all_resolve_from(fe0, es, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// `afvs.all (fun a => w.resolve fe₀ a.fvarTypeD)` — a reflexive field's own
/// telescope domains resolve in the pre-block environment.
pub fn all_annots_resolve_from(fe0: &FEnv, fvs: &Vec<Expr>, i: usize) -> bool {
    if i >= fvs.len() {
        true
    } else {
        let dom: Expr = expr_ops::fvar_type_d(&fvs[i]);
        if decl_check::consts_resolve_f_fast(fe0, &dom) {
            all_annots_resolve_from(fe0, fvs, i + 1)
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// `!(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i))` —
/// no later field's domain mentions the recursive field's variable.
pub fn no_later_mentions_from(x_fvs: &Vec<Expr>, q: u64, i: usize) -> bool {
    if i >= x_fvs.len() {
        true
    } else {
        let dom: Expr = expr_ops::fvar_type_d(&x_fvs[i]);
        if mentions_fvar(q, &dom) {
            false
        } else {
            no_later_mentions_from(x_fvs, q, i + 1)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// The `.recursive` arm of `nativeOpenedOk`'s per-field match: the field's
/// domain is the family at the opened parameter variables followed by `nIdx`
/// index expressions resolving in `env₀`, and the variable occurs in no later
/// field's domain nor in the residual.
pub fn native_opened_recursive(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<Expr>,
    x_fvs: &Vec<Expr>,
    xrest: &Expr,
    i: u64,
    dom: &Expr,
) -> bool {
    let head: Expr = expr_ops::get_app_fn(dom);
    let expected: Expr = expr::mk_const(name::dup(t), struct_parts::params_of(lps));
    if !expr::beq(&head, &expected) {
        false
    } else {
        let args: Vec<Expr> = expr_ops::get_app_args(dom);
        if !expr::exprs_beq(&expr_ops::take_exprs(&args, n_p as usize), fvs_p) {
            false
        } else if args.len() as u64 != n_p + n_idx {
            false
        } else if !all_resolve_from(fe0, &core_k::drop_exprs(&args, n_p as usize), 0) {
            false
        } else if !no_later_mentions_from(x_fvs, n_p + i, (i + 1) as usize) {
            false
        } else {
            !mentions_fvar(n_p + i, xrest)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// The `.reflexive` arm: the field's own telescope, OPENED at variables at
/// the field's depth, its domains resolving in `env₀`, its body the family at
/// the parameter variables and `nIdx` index expressions resolving in `env₀`.
pub fn native_opened_reflexive(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<Expr>,
    x_fvs: &Vec<Expr>,
    xrest: &Expr,
    i: u64,
    dom: &Expr,
) -> bool {
    let tele_len: u64 = native_parts::pi_binders(dom).0.len() as u64;
    match checker_base::open_pis_at_fvars_f(tele_len, dom, n_p + i) {
        None => false,
        Some(aq) => {
            if aq.0.len() == 0 {
                false
            } else if !all_annots_resolve_from(fe0, &aq.0, 0) {
                false
            } else {
                let head: Expr = expr_ops::get_app_fn(&aq.1);
                let expected: Expr =
                    expr::mk_const(name::dup(t), struct_parts::params_of(lps));
                if !expr::beq(&head, &expected) {
                    false
                } else {
                    let args: Vec<Expr> = expr_ops::get_app_args(&aq.1);
                    if !expr::exprs_beq(
                        &expr_ops::take_exprs(&args, n_p as usize),
                        fvs_p,
                    ) {
                        false
                    } else if args.len() as u64 != n_p + n_idx {
                        false
                    } else if !all_resolve_from(
                        fe0,
                        &core_k::drop_exprs(&args, n_p as usize),
                        0,
                    ) {
                        false
                    } else if !no_later_mentions_from(x_fvs, n_p + i, (i + 1) as usize) {
                        false
                    } else {
                        !mentions_fvar(n_p + i, xrest)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// The `(List.range nF).all` of `nativeOpenedOk`: one clause per field kind.
pub fn native_opened_fields_from(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<Expr>,
    x_fvs: &Vec<Expr>,
    xrest: &Expr,
    ks: &Vec<RecFieldKind>,
    n_f: u64,
    i: u64,
) -> bool {
    if i >= n_f {
        true
    } else if (i as usize) >= x_fvs.len() {
        false
    } else {
        let dom: Expr = expr_ops::fvar_type_d(&x_fvs[i as usize]);
        let ok = match native_parts::kind_get_d(ks, i) {
            RecFieldKind::Ordinary => decl_check::consts_resolve_f_fast(fe0, &dom),
            RecFieldKind::Recursive => native_opened_recursive(
                fe0, t, lps, n_p, n_idx, fvs_p, x_fvs, xrest, i, &dom,
            ),
            RecFieldKind::Reflexive => native_opened_reflexive(
                fe0, t, lps, n_p, n_idx, fvs_p, x_fvs, xrest, i, &dom,
            ),
            RecFieldKind::Negative => false,
            RecFieldKind::Unsupported => false,
        };
        if ok {
            native_opened_fields_from(
                fe0, t, lps, n_p, n_idx, fvs_p, x_fvs, xrest, ks, n_f, i + 1,
            )
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// The kinds the recogniser computed, re-checked on the annotated
/// constructor type OPENED at variables (as the stage read it).
pub fn native_opened_ok(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    cty: &Expr,
    n_f: u64,
    ks: &Vec<RecFieldKind>,
) -> bool {
    match checker_base::open_pis_at_fvars_f(n_p, cty, 0) {
        None => false,
        Some(pq) => match checker_base::open_pis_at_fvars_f(n_f, &pq.1, n_p) {
            None => false,
            Some(xq) => {
                let resid: Vec<Expr> = core_k::drop_exprs(
                    &expr_ops::get_app_args(&xq.1),
                    n_p as usize,
                );
                if !all_resolve_from(fe0, &resid, 0) {
                    false
                } else {
                    native_opened_fields_from(
                        fe0, t, lps, n_p, n_idx, &pq.0, &xq.0, &xq.1, ks, n_f, 0,
                    )
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
/// The kinds, re-checked on every annotated constructor, one kind list per
/// constructor, one kind per field.
pub fn native_fields_ok(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
) -> bool {
    if ctors_a.len() == kinds.len() {
        native_fields_ok_from(fe0, t, lps, n_p, n_idx, ctors_a, kinds, 0)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
/// The `(List.range ctorsA.length).all` behind `native_fields_ok`.
pub fn native_fields_ok_from(
    fe0: &FEnv,
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    j: usize,
) -> bool {
    if j >= ctors_a.len() {
        true
    } else if j >= kinds.len() {
        false
    } else if kinds[j].len() as u64 != ctors_a[j].1 {
        false
    } else if native_opened_ok(
        fe0,
        t,
        lps,
        n_p,
        n_idx,
        &ctors_a[j].0.ty,
        ctors_a[j].1,
        &kinds[j],
    ) {
        native_fields_ok_from(fe0, t, lps, n_p, n_idx, ctors_a, kinds, j + 1)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The recursor stage (`NativeInstall.lean:450-503` / `NativeInstallF.lean:71-124`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
/// The generated rules for constructors `j, j+1, …` (`k` of them), each
/// scoped at the environment holding the recursor's constant (`feR`): a rule
/// mentions the recursor and is not inferred.  Accumulated on the way in
/// (task #13's pattern 3).
pub fn check_native_rules(
    fe_r: &FEnv,
    rlps: &Vec<Name>,
    t: &Name,
    lps: &Vec<Name>,
    elim: &Name,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &Expr,
    ctors: &Vec<(Name, u64, Expr, Vec<u64>)>,
    rec_c: &Name,
    rlvls: &Vec<Level>,
    k: u64,
    j: u64,
    out: Vec<Expr>,
) -> CheckM<Vec<Expr>> {
    const M_RULE: [u32; 30] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 114, 117, 108, 101, 32, 32, 32, 32, 32,
    ];
    const M_SCOPE: [u32; 38] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 114, 117, 108, 101, 32, 115, 99, 111, 112, 105, 110, 103, 32, 32, 32,
        32, 32,
    ];
    if k == 0 {
        Ok(out)
    } else {
        match native_parts::struct_rec_rhs_r(
            t, lps, elim, large, n_p, n_idx, tty, ctors, rec_c, rlvls, j,
        ) {
            None => Err(core_types::internal(core_types::code_points(&M_RULE))),
            Some(rhs) => {
                if !term_scoped(fe_r, rlps, &rhs) {
                    Err(core_types::internal(core_types::code_points(&M_SCOPE)))
                } else {
                    let mut out = out;
                    out.push(rhs);
                    check_native_rules(
                        fe_r, rlps, t, lps, elim, large, n_p, n_idx, tty, ctors, rec_c,
                        rlvls, k - 1, j + 1, out,
                    )
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
/// The scoping guard both recursor stages spell,
/// `e.allLevelParamsDefined rlps && w.resolve fe e && e.looseBVarsBounded 0
/// && !e.hasFvar`.  Its own function because the conjunction borrows the index
/// and the term and both arms of the `unless` read them again (task #14's
/// rule; Aeneas answered *"Could not match the contexts"* at the joined
/// `if`).
pub fn term_scoped(fe: &FEnv, lps: &Vec<Name>, e: &Expr) -> bool {
    if expr_ops::all_level_params_defined_fast(lps, e) {
        if decl_check::consts_resolve_f_fast(fe, e) {
            if expr_ops::loose_bvars_bounded(0, e) {
                !expr_ops::has_fvar(e)
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
/// Stage 3: **the recursor, generated and compared** — the generated type has
/// the inductive-hypothesis binders in each minor (`structRecTyR`), and the
/// generated rules are scoped at the environment holding the recursor's
/// constant.  The recursor PIN is thrown here (con-leche task #220): a record
/// naming something other than the generated `T.rec`, or contradicting it in
/// its level parameters or its argument sums and rules, is INVALID INPUT.
///
/// Deviation: `feR` needs a second view of `fe`, hence the `fenv::dup`
/// (module note).
pub fn check_native_rec(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p: &NativeParts,
    cv_ta: &ConstantVal,
    ctors_a: &Vec<(ConstantVal, u64)>,
) -> CheckM<(ConstantVal, Vec<Expr>)> {
    const REC: [u32; 3] = [114, 101, 99];
    const M_NAME: [u32; 56] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 98, 108,
        111, 99, 107, 39, 115, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 105, 115, 32,
        110, 111, 116, 32, 84, 46, 114, 101, 99, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_LPS: [u32; 60] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 108, 101, 118, 101, 108, 32,
        112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 114, 101, 32, 110, 111, 116,
        32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101,
        115, 32, 32, 32, 32, 32,
    ];
    const M_PIN: [u32; 52] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101,
        99, 111, 114, 100, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101,
        110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 32, 32, 32, 32, 32,
    ];
    const M_TY: [u32; 30] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 116, 121, 112, 101, 32, 32, 32, 32, 32,
    ];
    const M_TYSC: [u32; 38] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 116, 121, 112, 101, 32, 115, 99, 111, 112, 105, 110, 103, 32, 32, 32,
        32, 32,
    ];
    const M_DEFEQ: [u32; 52] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101,
        32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 32, 32,
    ];
    let expected_rec: Name = name::mk_str(
        name::dup(&p.shape.cv_t.name),
        core_types::code_points(&REC),
    );
    if !name::beq(&p.shape.cv_r.name, &expected_rec) {
        Err(core_types::invalid(core_types::code_points(&M_NAME)))
    } else if !native_parts::native_rec_lps_ok(&p.shape) {
        Err(core_types::invalid(core_types::code_points(&M_LPS)))
    } else if !p.rec_pinned {
        Err(core_types::invalid(core_types::code_points(&M_PIN)))
    } else {
        match checker_base::check_constant_val(mode, st, fe, &p.shape.cv_r) {
            Err(err) => Err(err),
            Ok(cv_ri) => {
                let ctors: Vec<(Name, u64, Expr, Vec<u64>)> =
                    native_parts::native_ctors4(ctors_a, &p.kinds);
                match native_parts::struct_rec_ty_r(
                    &p.shape.cv_t.name,
                    &p.shape.cv_t.level_params,
                    &p.shape.elim,
                    p.shape.large,
                    p.shape.n_p,
                    p.shape.n_idx,
                    &cv_ta.ty,
                    &ctors,
                ) {
                    None => Err(core_types::internal(core_types::code_points(&M_TY))),
                    Some(rec_ty) => {
                        if !term_scoped(fe, &p.shape.cv_r.level_params, &rec_ty) {
                            Err(core_types::internal(core_types::code_points(&M_TYSC)))
                        } else {
                            match core_c::infer(
                                mode,
                                core_k::check_fuel(),
                                st,
                                fe,
                                0,
                                &rec_ty,
                            ) {
                                Err(err) => Err(err),
                                Ok(sty) => match core_c::ensure_sort_i(
                                    mode,
                                    core_k::check_fuel(),
                                    st,
                                    fe,
                                    0,
                                    &sty,
                                ) {
                                    Err(err) => Err(err),
                                    Ok(_u) => match core_c::defeq(
                                        mode,
                                        core_k::check_fuel(),
                                        st,
                                        fe,
                                        0,
                                        &cv_ri.ty,
                                        &rec_ty,
                                    ) {
                                        Err(err) => Err(err),
                                        Ok(false) => Err(core_types::invalid(
                                            core_types::code_points(&M_DEFEQ),
                                        )),
                                        Ok(true) => check_native_rec_rules(
                                            fe, p, cv_ta, &ctors, rec_ty,
                                        ),
                                    },
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
/// The tail of `checkNativeRec`: the annotated recursor constant, the
/// ruleless provisioning of the index the rules are scoped at, and the rules.
/// Split off so the nest above stays readable; this is where the `fenv::dup`
/// of the module note happens.
pub fn check_native_rec_rules(
    fe: &FEnv,
    p: &NativeParts,
    cv_ta: &ConstantVal,
    ctors: &Vec<(Name, u64, Expr, Vec<u64>)>,
    rec_ty: Expr,
) -> CheckM<(ConstantVal, Vec<Expr>)> {
    let cv_ra = ConstantVal {
        name: name::dup(&p.shape.cv_r.name),
        level_params: prop_when::names_copy(&p.shape.cv_r.level_params),
        ty: rec_ty,
    };
    let fe_r: FEnv = fenv::push(
        fenv::dup(fe),
        ConstantInfo::RecInfo(
            env::constant_val_dup(&cv_ra),
            sum_parts::major_idx(&p.shape),
            sum_parts::rule_prefix(&p.shape),
            Vec::new(),
        ),
    );
    let rlvls: Vec<Level> = struct_parts::params_of(&p.shape.cv_r.level_params);
    match check_native_rules(
        &fe_r,
        &p.shape.cv_r.level_params,
        &p.shape.cv_t.name,
        &p.shape.cv_t.level_params,
        &p.shape.elim,
        p.shape.large,
        p.shape.n_p,
        p.shape.n_idx,
        &cv_ta.ty,
        ctors,
        &p.shape.cv_r.name,
        &rlvls,
        ctors.len() as u64,
        0,
        Vec::new(),
    ) {
        Err(err) => Err(err),
        Ok(rhss) => Ok((cv_ra, rhss)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
/// Stage 4: **the projection table** at a STRUCTURE-LIKE block — one
/// constructor, no index — the direct structure route's table at the TAGGED
/// tower's projection offset `1` (`ProjTable.off`: the carrier's first pair
/// component is the constructor tag); nothing at any other block.
pub fn check_native_table(
    p: &NativeParts,
    ctors_a: &Vec<(ConstantVal, u64)>,
    sortss: &Vec<Vec<Level>>,
    fe: FEnv,
) -> CheckM<FEnv> {
    if ctors_a.len() == 1 {
        if sortss.len() == 1 {
            if p.shape.n_idx == 0 {
                let guards: Vec<Level> = struct_parts::struct_proj_guards(
                    &ctors_a[0].0.ty,
                    p.shape.n_p,
                    ctors_a[0].1,
                    &sortss[0],
                );
                struct_install::check_struct_proj_table(
                    &p.shape.cv_t.name,
                    &ctors_a[0].0.name,
                    &p.shape.cv_t.level_params,
                    p.shape.n_p,
                    ctors_a[0].1,
                    &p.shape.res_sort,
                    guards,
                    1,
                    &ctors_a[0].0,
                    fe,
                )
            } else {
                Ok(fe)
            }
        } else {
            Ok(fe)
        }
    } else {
        Ok(fe)
    }
}

// ---------------------------------------------------------------------------
// The two-pass driver (`NativeInstall.lean:526-641`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:521-537 NativePass
/// **What one pass over the former and the constructors yields**: the
/// former's environment, the annotated former, the record completed with the
/// sort the former's run read and the kinds the pass classified, the
/// annotated constructors and their fields' sorts.
///
/// Deviation: the cited structure is generic in the environment
/// representation (`E`, `Env` at the pure install and `FEnv` at the cached
/// driver's mirror); the port has one spelling (`super`'s module note 1).
pub struct NativePass {
    pub env1: FEnv,
    pub cv_ta: ConstantVal,
    pub p: NativeParts,
    pub ctors_a: Vec<(ConstantVal, u64)>,
    pub sortss: Vec<Vec<Level>>,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// `ctorsA.mapM (recCtorKinds T lps nP nIdx)` at the `Option` monad, as an
/// index recursion: the first `none` is the whole `none`.
pub fn rec_ctor_kinds_all(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(ConstantVal, u64)>,
    i: usize,
    out: Vec<Vec<RecFieldKind>>,
) -> Option<Vec<Vec<RecFieldKind>>> {
    if i >= ctors_a.len() {
        Some(out)
    } else {
        match native_parts::rec_ctor_kinds(t, lps, n_p, n_idx, &ctors_a[i]) {
            None => None,
            Some(ks) => {
                let mut out = out;
                out.push(ks);
                rec_ctor_kinds_all(t, lps, n_p, n_idx, ctors_a, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// `kinds.any (fun ks => ks.any (· == k))`, as an index recursion.
pub fn kinds_any_from(kinds: &Vec<Vec<RecFieldKind>>, k: &RecFieldKind, j: usize) -> bool {
    if j >= kinds.len() {
        false
    } else if kind_list_any_from(&kinds[j], k, 0) {
        true
    } else {
        kinds_any_from(kinds, k, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// The inner `ks.any (· == k)`.
pub fn kind_list_any_from(ks: &Vec<RecFieldKind>, k: &RecFieldKind, i: usize) -> bool {
    if i >= ks.len() {
        false
    } else if native_parts::rec_field_kind_beq(&ks[i], k) {
        true
    } else {
        kind_list_any_from(ks, k, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// **The fields' kinds, classified at install** on the stored constructors —
/// their field domains normalised by official's positivity walk
/// (`normCtorVal`), so the syntactic classification is official's: a
/// non-positive or non-valid occurrence is INVALID, a nested occurrence — the
/// one positive occurrence the route does not model — a positive decline.
pub fn classify_fix_kinds(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(ConstantVal, u64)>,
) -> CheckM<Vec<Vec<RecFieldKind>>> {
    const M_TELE: [u32; 41] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32, 32, 32,
    ];
    const M_NEG: [u32; 68] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 110, 111, 110, 32, 112, 111,
        115, 105, 116, 105, 118, 101, 32, 111, 114, 32, 110, 111, 110, 32, 118, 97, 108, 105,
        100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 32, 32, 32, 32, 32, 32,
        32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_NEST: [u32; 46] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 32, 110, 101, 115, 116,
        101, 100, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 116,
        104, 101, 32, 98, 108, 111, 99, 107, 32, 32,
    ];
    match rec_ctor_kinds_all(t, lps, n_p, n_idx, ctors_a, 0, Vec::new()) {
        None => Err(core_types::not_implemented(core_types::code_points(&M_TELE))),
        Some(kinds) => {
            if kinds_any_from(&kinds, &RecFieldKind::Negative, 0) {
                Err(core_types::invalid(core_types::code_points(&M_NEG)))
            } else if kinds_any_from(&kinds, &RecFieldKind::Unsupported, 0) {
                Err(core_types::not_implemented(core_types::code_points(&M_NEST)))
            } else {
                Ok(kinds)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
/// con-leche: ConLeche/Cached/CheckerC.lean:177-190 checkNativePassS
/// **One pass over the former and the constructors** at a given `is_rec`
/// verdict: the former with the capability record at that verdict, the
/// constructors at the former's environment (normalised, checked; the
/// resolution guard pointed at that same environment), the kinds classified
/// on THOSE constructors and the record completed with them.  The last
/// component says whether the classification confirms the verdict the pass
/// ran at.
///
/// Deviations: the pre-block index is copied (`fenv::dup`, module note), and
/// the cached driver's two `flushC`s are `inductives_c`'s.
pub fn check_native_pass(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p0: &NativeParts,
    is_rec: bool,
) -> CheckM<(NativePass, bool)> {
    match check_native_pass_former(mode, st, fe, p0, is_rec) {
        Err(err) => Err(err),
        Ok(q) => check_native_pass_ctors(mode, st, q.0, q.1, q.2, p0, q.3),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
/// con-leche: ConLeche/Cached/CheckerC.lean:177-190 checkNativePassS
/// The **former's half** of one pass: `checkSumIndF` at the capability record
/// the verdict names, and the record that the classification must reproduce.
/// Split from the constructors' half so that the cached driver's `flushC`
/// (between them, `checkNativePassS`) sits exactly where the cited code puts
/// it, with one body for both.
pub fn check_native_pass_former(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p0: &NativeParts,
    is_rec: bool,
) -> CheckM<(FEnv, ConstantVal, InductiveShape, IndCaps)> {
    let caps_of = NativeCapsAt { is_rec };
    match sum_install::check_sum_ind(
        mode,
        st,
        fenv::dup(fe),
        sum_parts::inductive_shape_dup(&p0.shape),
        &caps_of,
    ) {
        Err(err) => Err(err),
        Ok(q) => {
            let expected: IndCaps = native_caps_at(&q.2, is_rec);
            Ok((q.0, q.1, q.2, expected))
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
/// con-leche: ConLeche/Cached/CheckerC.lean:177-190 checkNativePassS
/// The **constructors' half** of one pass: the constructors at the former's
/// environment, the kinds classified on those constructors, the record
/// completed with them, and the verdict's confirmation.
pub fn check_native_pass_ctors(
    mode: &CheckMode,
    st: &mut CState,
    fe1: FEnv,
    cv_ta: ConstantVal,
    p1: InductiveShape,
    p0: &NativeParts,
    expected: IndCaps,
) -> CheckM<(NativePass, bool)> {
    {
        {
            let pc: NativeParts = native_parts::complete(p0, p1);
            match sum_install::check_sum_ctors(
                mode,
                st,
                &fe1,
                &fe1,
                &pc.shape.cv_t.name,
                &pc.shape.cv_t.level_params,
                pc.shape.n_p,
                pc.shape.n_idx,
                &pc.shape.res_sort,
                pc.shape.is_prop,
                pc.shape.large,
                &cv_ta,
                &pc.shape.ctors,
                0,
                Vec::new(),
                Vec::new(),
            ) {
                Err(err) => Err(err),
                Ok(cq) => {
                    let ctors_a: Vec<(ConstantVal, u64)> = cq.0;
                    let sortss: Vec<Vec<Level>> = cq.1;
                    match classify_fix_kinds(
                        &pc.shape.cv_t.name,
                        &pc.shape.cv_t.level_params,
                        pc.shape.n_p,
                        pc.shape.n_idx,
                        &ctors_a,
                    ) {
                        Err(err) => Err(err),
                        Ok(kinds) => {
                            let p: NativeParts = native_parts::with_kinds(pc, kinds);
                            let settled =
                                env::ind_caps_beq(&native_caps(&p), &expected);
                            Ok((
                                NativePass {
                                    env1: fe1,
                                    cv_ta,
                                    p,
                                    ctors_a,
                                    sortss,
                                },
                                settled,
                            ))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// **The install after the pass**: the elimination restriction, the index
/// binders' sorts, the kinds re-checked, the stream's rules against the
/// generated ones, the constructors consed, the recursor with its rules, and
/// — at a structure-like block — the projection table.
pub fn check_native_tail(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    q: NativePass,
) -> CheckM<FEnv> {
    match check_native_tail_guards(mode, st, fe, &q) {
        Err(err) => Err(err),
        Ok(()) => {
            let cq = check_native_cons(q);
            check_native_install(mode, st, cq.0, cq.1, cq.2, cq.3, cq.4)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// **Official's `elim_only_at_universe_zero`**: a large eliminator on a block
/// whose sort may be `Prop` is `.invalid` at two or more constructors; at one
/// constructor it is the subsingleton case, taken with the per-field criterion
/// at `checkStructFieldSortsI`.  Its own function because the cited `if`'s
/// condition borrows the record and both arms read it again (task #14's rule;
/// Aeneas answered *"Unreachable"* at the joined `if`).
pub fn elim_restriction_violated(p: &NativeParts) -> bool {
    if p.shape.large {
        if !level::is_never_zero(&p.shape.res_sort) {
            p.shape.ctors.len() >= 2
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// **The guard half of `checkNativeTail`**: the elimination restriction, the
/// index binders' sorts (read, not compared), the kinds re-checked on the
/// stored constructors in the opened form the model reads, and the stream's
/// rules against the generated ones.
pub fn check_native_tail_guards(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    q: &NativePass,
) -> CheckM<()> {
    const M_ELIM: [u32; 62] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 108, 97, 114, 103, 101, 32,
        101, 108, 105, 109, 105, 110, 97, 116, 111, 114, 32, 111, 110, 32, 97, 32, 109, 117,
        108, 116, 105, 45, 99, 116, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101,
        32, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_TELE: [u32; 39] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 121, 112, 101, 32, 102,
        111, 114, 109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32,
        32, 32, 32,
    ];
    const M_KINDS: [u32; 25] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 102, 105, 101, 108, 100, 32,
        107, 105, 110, 100, 115, 32, 32,
    ];
    const M_RULES: [u32; 55] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115,
        111, 114, 32, 114, 117, 108, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116,
        104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 115, 32,
        32,
    ];
    if elim_restriction_violated(&q.p) {
        Err(core_types::invalid(core_types::code_points(&M_ELIM)))
    } else {
        match checker_base::open_pis_at_fvars_f(
            q.p.shape.n_p + q.p.shape.n_idx,
            &q.cv_ta.ty,
            0,
        ) {
            None => Err(core_types::internal(core_types::code_points(&M_TELE))),
            Some(tq) => {
                let idx_fvs: Vec<Expr> =
                    core_k::drop_exprs(&tq.0, q.p.shape.n_p as usize);
                let no_idx_args: Vec<Expr> = Vec::new();
                match sum_install::check_struct_field_sorts_i(
                    mode,
                    st,
                    &q.env1,
                    true,
                    false,
                    &q.p.shape.res_sort,
                    q.p.shape.n_p,
                    &idx_fvs,
                    &no_idx_args,
                    q.p.shape.n_idx,
                ) {
                    Err(err) => Err(err),
                    Ok(_isorts) => {
                        if !native_fields_ok(
                            fe,
                            &q.p.shape.cv_t.name,
                            &q.p.shape.cv_t.level_params,
                            q.p.shape.n_p,
                            q.p.shape.n_idx,
                            &q.ctors_a,
                            &q.p.kinds,
                        ) {
                            Err(core_types::internal(core_types::code_points(&M_KINDS)))
                        } else {
                            let rlvls: Vec<Level> = struct_parts::params_of(
                                &q.p.shape.cv_r.level_params,
                            );
                            if !native_parts::native_rules_ok(
                                &q.p.shape.cv_r.name,
                                &rlvls,
                                &prop_when::never(),
                                q.p.shape.n_p,
                                q.p.shape.ctors.len() as u64,
                                &q.ctors_a,
                                &q.p.kinds,
                                &q.p.shape.rhss,
                                &q.p.shape.cv_r.ty,
                            ) {
                                Err(core_types::invalid(core_types::code_points(&M_RULES)))
                            } else {
                                Ok(())
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// `let fe₂ := consSumCtorsF p.nP q.ctorsA q.env₁` — the pass's record taken
/// apart and the constructors consed onto the former's index.  It is its own
/// function because the cached driver's `flushC` sits between it and the
/// recursor's stage.
pub fn check_native_cons(
    q: NativePass,
) -> (
    FEnv,
    NativeParts,
    ConstantVal,
    Vec<(ConstantVal, u64)>,
    Vec<Vec<Level>>,
) {
    let p: NativeParts = q.p;
    let cv_ta: ConstantVal = q.cv_ta;
    let ctors_a: Vec<(ConstantVal, u64)> = q.ctors_a;
    let sortss: Vec<Vec<Level>> = q.sortss;
    let fe2: FEnv = sum_install::cons_sum_ctors(p.shape.n_p, &ctors_a, 0, q.env1);
    (fe2, p, cv_ta, ctors_a, sortss)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// The installing tail of `checkNativeTail`: the recursor generated, its rules
/// stored, and the projection table.
pub fn check_native_install(
    mode: &CheckMode,
    st: &mut CState,
    fe2: FEnv,
    p: NativeParts,
    cv_ta: ConstantVal,
    ctors_a: Vec<(ConstantVal, u64)>,
    sortss: Vec<Vec<Level>>,
) -> CheckM<FEnv> {
    match check_native_rec(mode, st, &fe2, &p, &cv_ta, &ctors_a) {
        Err(err) => Err(err),
        Ok(rq) => {
            let cv_ra: ConstantVal = rq.0;
            let rhss: Vec<Expr> = rq.1;
            let rules = sum_install::sum_rules(
                &fe2,
                &cv_ra.name,
                p.shape.n_p,
                sum_parts::major_idx(&p.shape),
                sum_parts::rule_prefix(&p.shape),
                &cv_ra.ty,
                &ctors_a,
                &rhss,
            );
            let fe3: FEnv = fenv::push(
                fe2,
                ConstantInfo::RecInfo(
                    cv_ra,
                    sum_parts::major_idx(&p.shape),
                    sum_parts::rule_prefix(&p.shape),
                    rules,
                ),
            );
            check_native_table(&p, &ctors_a, &sortss, fe3)
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// con-leche: ConLeche/Cached/CheckerC.lean:217-231 checkNativeS
/// Check and install a **direct recursive block**: the distinct names, the
/// pass over the former (with the block's capability record) and the
/// constructors — again where the record's syntactic reading overshot — and
/// the install after it.
///
/// The two-pass shape is the cited one: `nativeRawRec` is a *superset* of
/// official's `is_rec`, and it is strict exactly when a redex over the block
/// reduces away; there the block is passed again at the classified verdict,
/// which then stands (the second pass stores the same constructors the first
/// did, so a verdict that moved again is an internal error, never a decline).
pub fn check_native(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p0: &NativeParts,
) -> CheckM<FEnv> {
    const M_DUP: [u32; 33] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 100, 117, 112, 108, 105, 99,
        97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
    ];
    const M_SETTLE: [u32; 57] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 99, 97,
        112, 97, 98, 105, 108, 105, 116, 121, 32, 114, 101, 99, 111, 114, 100, 32, 100, 105,
        100, 32, 110, 111, 116, 32, 115, 101, 116, 116, 108, 101, 32, 32, 32, 32, 32, 32, 32,
        32, 32,
    ];
    let names: Vec<Name> = ctor_names(&p0.shape.ctors);
    if !level::name_nodup(&names) {
        Err(core_types::invalid(core_types::code_points(&M_DUP)))
    } else {
        match check_native_pass(mode, st, fe, p0, native_raw_rec(p0)) {
            Err(err) => Err(err),
            Ok(q) => {
                if q.1 {
                    check_native_tail(mode, st, fe, q.0)
                } else {
                    let is_rec2: bool = native_is_rec(&q.0.p.kinds);
                    match check_native_pass(mode, st, fe, p0, is_rec2) {
                        Err(err) => Err(err),
                        Ok(q2) => {
                            if q2.1 {
                                check_native_tail(mode, st, fe, q2.0)
                            } else {
                                Err(core_types::internal(core_types::code_points(
                                    &M_SETTLE,
                                )))
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// `p₀.ctors.map (·.1.name)`, whose `Nodup` the front guard decides
/// (`level::name_nodup`, task #13's port of `Name.nodup`).
pub fn ctor_names(cs: &Vec<(ConstantVal, u64)>) -> Vec<Name> {
    ctor_names_from(cs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// The index recursion behind `ctor_names`.
pub fn ctor_names_from(cs: &Vec<(ConstantVal, u64)>, i: usize, out: Vec<Name>) -> Vec<Name> {
    if i >= cs.len() {
        out
    } else {
        let mut out = out;
        out.push(name::dup(&cs[i].0.name));
        ctor_names_from(cs, i + 1, out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cached::state_c;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env::RecRule;
    use crate::kernel::inductives::native_parts::RecFieldKind;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn child(pre: &Name, s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::dup(pre), cps)
    }

    /// The parse placeholder every exported binder carries.
    fn raw() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn cv(n: Name, lps: Vec<Name>, ty: Expr) -> ConstantVal {
        ConstantVal {
            name: n,
            level_params: lps,
            ty,
        }
    }

    fn ax(n: Name, ty: Expr) -> ConstantInfo {
        ConstantInfo::AxiomInfo(cv(n, Vec::new(), ty))
    }

    fn sort1() -> Expr {
        expr::sort(level::succ(level::zero()))
    }

    /// The stream's recursor for a block whose shape is `(T, lps, elim,
    /// large, nP, nIdx, tty)` with the given constructors and kinds: the
    /// **generated** type and rules, which is what an export carries (the
    /// elaborator generated them, `checkNativeRec` regenerates and compares).
    fn generated_rec(
        t: &Name,
        lps: &Vec<Name>,
        elim: &Name,
        large: bool,
        n_p: u64,
        n_idx: u64,
        tty: &Expr,
        ctors_a: &Vec<(ConstantVal, u64)>,
        kinds: &Vec<Vec<RecFieldKind>>,
    ) -> (Expr, Vec<Expr>) {
        let ctors = native_parts::native_ctors4(ctors_a, kinds);
        let rec_ty = native_parts::struct_rec_ty_r(
            t, lps, elim, large, n_p, n_idx, tty, &ctors,
        )
        .expect("the recursor type generates");
        let rec_name = child(t, "rec");
        let mut rlvls: Vec<Name> = Vec::new();
        if large {
            rlvls.push(name::dup(elim));
        }
        rlvls = prop_when::append_from(lps, 0, rlvls);
        let lv: Vec<Level> = struct_parts::params_of(&rlvls);
        let mut rhss: Vec<Expr> = Vec::new();
        let mut j: u64 = 0;
        while j < ctors.len() as u64 {
            rhss.push(
                native_parts::struct_rec_rhs_r(
                    t, lps, elim, large, n_p, n_idx, tty, &ctors, &rec_name, &lv, j,
                )
                .expect("the rule generates"),
            );
            j += 1;
        }
        (rec_ty, rhss)
    }

    /// The `Nat`-like block: `N : Sort 1`, `Nz : N`, `Ns : N → N`, and the
    /// generated `N.rec` at a fresh elimination parameter `u`.
    fn nat_like_block() -> Vec<ConstantInfo> {
        let t = nm("N");
        let cv_t = cv(name::dup(&t), Vec::new(), sort1());
        let cv_z = cv(nm("Nz"), Vec::new(), expr::mk_const(name::dup(&t), Vec::new()));
        let cv_s = cv(
            nm("Ns"),
            Vec::new(),
            expr::forall_e(
                expr::mk_const(name::dup(&t), Vec::new()),
                expr::mk_const(name::dup(&t), Vec::new()),
                raw(),
            ),
        );
        let mut ctors_a: Vec<(ConstantVal, u64)> = Vec::new();
        ctors_a.push((env::constant_val_dup(&cv_z), 0));
        ctors_a.push((env::constant_val_dup(&cv_s), 1));
        let mut kinds: Vec<Vec<RecFieldKind>> = Vec::new();
        kinds.push(Vec::new());
        let mut ks1: Vec<RecFieldKind> = Vec::new();
        ks1.push(RecFieldKind::Recursive);
        kinds.push(ks1);
        let u = nm("u");
        let (rec_ty, rhss) = generated_rec(
            &t,
            &Vec::new(),
            &u,
            true,
            0,
            0,
            &sort1(),
            &ctors_a,
            &kinds,
        );
        let mut rlps: Vec<Name> = Vec::new();
        rlps.push(name::dup(&u));
        let cv_r = cv(child(&t, "rec"), rlps, rec_ty);
        let mut rules: Vec<RecRule> = Vec::new();
        rules.push(env::rec_rule_parsed(
            nm("Nz"),
            0,
            expr::dup(&rhss[0]),
        ));
        rules.push(env::rec_rule_parsed(
            nm("Ns"),
            1,
            expr::dup(&rhss[1]),
        ));
        let mut block: Vec<ConstantInfo> = Vec::new();
        block.push(ConstantInfo::IndInfo(cv_t, env::ind_caps_default()));
        block.push(ConstantInfo::CtorInfo(cv_z, 0, 0));
        block.push(ConstantInfo::CtorInfo(cv_s, 0, 1));
        block.push(ConstantInfo::RecInfo(cv_r, 3, 3, rules));
        block
    }

    /// **The `Nat`-like block is recognised and installed.**  Two
    /// constructors, one of them recursive, a large eliminator, no index — the
    /// whole direct route end to end: the recogniser, the former's telescope,
    /// the constructors with official's positivity walk as a normalisation,
    /// the classification, the recursor generated and compared with the
    /// stream's, and the rules.
    #[test]
    fn check_native_installs_a_nat_like_block() {
        let block = nat_like_block();
        let p = native_parts::native_parts(0, &block).expect("the block is recognised");
        assert!(p.rec_pinned, "the recursor record must pass the structural pin");
        assert_eq!(p.shape.n_p, 0);
        assert_eq!(p.shape.n_idx, 0);
        assert_eq!(p.shape.ctors.len(), 2);
        assert!(p.shape.large, "a fresh elimination parameter is the large eliminator");
        assert!(!native_raw_rec(&p), "the syntactic reading needs one constructor");

        let fe: FEnv = fenv::mk_fenv(env::empty());
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        match check_native(&mode, &mut st, &fe, &p) {
            Ok(fe2) => {
                // the former, both constructors and the ruled recursor are stored
                assert!(fenv::find(&fe2, &nm("N")).is_some());
                assert!(fenv::find(&fe2, &nm("Nz")).is_some());
                assert!(fenv::find(&fe2, &nm("Ns")).is_some());
                match fenv::find(&fe2, &child(&nm("N"), "rec")) {
                    Some(ConstantInfo::RecInfo(_, m_i, r_p, rules)) => {
                        assert_eq!(*m_i, 3);
                        assert_eq!(*r_p, 3);
                        assert_eq!(rules.len(), 2);
                        // the route's rules are plain and parameter-blind
                        assert!(rules[0].params_blind);
                        assert!(rules[1].params_blind);
                    }
                    _ => panic!("the recursor must be stored with its rules"),
                }
                // no projection table: two constructors is not structure-like
                assert!(fenv::find(&fe2, &env::proj_table_name(&nm("N"))).is_none());
            }
            Err(_) => panic!("the Nat-like block must install"),
        }
    }

    /// The classification of the `Nat`-like block's fields: the nullary
    /// constructor has none, the successor's single field is `recursive`, and
    /// `nativeIsRec` reads `true` off that.
    #[test]
    fn classify_reads_the_recursive_field() {
        let block = nat_like_block();
        let p = native_parts::native_parts(0, &block).unwrap();
        match classify_fix_kinds(
            &p.shape.cv_t.name,
            &p.shape.cv_t.level_params,
            p.shape.n_p,
            p.shape.n_idx,
            &p.shape.ctors,
        ) {
            Ok(kinds) => {
                assert_eq!(kinds.len(), 2);
                assert_eq!(kinds[0].len(), 0);
                assert_eq!(kinds[1].len(), 1);
                assert!(native_parts::rec_field_kind_beq(
                    &kinds[1][0],
                    &RecFieldKind::Recursive
                ));
                assert!(native_is_rec(&kinds));
            }
            Err(_) => panic!("the kinds must classify"),
        }
    }

    /// **The `Eq`-like indexed family is recognised and installed.**
    /// `Q : A → Prop` with `Qmk : ∀ (a : A), Q a` — one constructor, one
    /// index, a `Prop` result and a large eliminator: the subsingleton case,
    /// where a non-propositional field is admitted exactly because it *is* one
    /// of the residual's index expressions (`Eq`'s rule,
    /// `checkStructFieldSortsI`).
    #[test]
    fn check_native_installs_an_indexed_prop_family() {
        let a = nm("A");
        let t = nm("Q");
        let a_ty = expr::mk_const(name::dup(&a), Vec::new());
        // `Q : ∀ (a : A), Prop`
        let tty = expr::forall_e(expr::dup(&a_ty), expr::sort(level::zero()), raw());
        let cv_t = cv(name::dup(&t), Vec::new(), expr::dup(&tty));
        // `Qmk : ∀ (a : A), Q a`
        let mut idx: Vec<Expr> = Vec::new();
        idx.push(expr::bvar(0));
        let cv_mk = cv(
            nm("Qmk"),
            Vec::new(),
            expr::forall_e(
                expr::dup(&a_ty),
                expr_ops::mk_app_n(expr::mk_const(name::dup(&t), Vec::new()), &idx),
                raw(),
            ),
        );
        let mut ctors_a: Vec<(ConstantVal, u64)> = Vec::new();
        ctors_a.push((env::constant_val_dup(&cv_mk), 1));
        let mut kinds: Vec<Vec<RecFieldKind>> = Vec::new();
        let mut ks: Vec<RecFieldKind> = Vec::new();
        ks.push(RecFieldKind::Ordinary);
        kinds.push(ks);
        let u = nm("u");
        let (rec_ty, rhss) = generated_rec(
            &t,
            &Vec::new(),
            &u,
            true,
            0,
            1,
            &tty,
            &ctors_a,
            &kinds,
        );
        let mut rlps: Vec<Name> = Vec::new();
        rlps.push(name::dup(&u));
        let cv_r = cv(child(&t, "rec"), rlps, rec_ty);
        let mut rules: Vec<RecRule> = Vec::new();
        rules.push(env::rec_rule_parsed(nm("Qmk"), 1, expr::dup(&rhss[0])));
        let mut block: Vec<ConstantInfo> = Vec::new();
        block.push(ConstantInfo::IndInfo(cv_t, env::ind_caps_default()));
        block.push(ConstantInfo::CtorInfo(cv_mk, 0, 1));
        block.push(ConstantInfo::RecInfo(cv_r, 3, 2, rules));

        let p = native_parts::native_parts(0, &block).expect("the family is recognised");
        assert_eq!(p.shape.n_idx, 1, "the index is read off the former's telescope");
        assert!(p.shape.is_prop, "the result sort is provably Prop");
        assert!(p.rec_pinned);

        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ax(name::dup(&a), sort1()));
        let fe: FEnv = fenv::mk_fenv(env::env_of(&consts));
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        match check_native(&mode, &mut st, &fe, &p) {
            Ok(fe2) => {
                assert!(fenv::find(&fe2, &nm("Q")).is_some());
                assert!(fenv::find(&fe2, &nm("Qmk")).is_some());
                assert!(fenv::find(&fe2, &child(&nm("Q"), "rec")).is_some());
                // an indexed family earns no capability (η needs `nIdx = 0`)
                match fenv::find(&fe2, &nm("Q")) {
                    Some(ConstantInfo::IndInfo(_, caps)) => {
                        assert!(!caps.eta);
                        assert!(!caps.unitlike);
                        assert!(!caps.rule_k, "one field is not K's shape");
                    }
                    _ => panic!("the former must be stored as an inductive"),
                }
                // and no projection table (an index is not structure-like)
                assert!(fenv::find(&fe2, &env::proj_table_name(&nm("Q"))).is_none());
            }
            Err(_) => panic!("the indexed Prop family must install"),
        }
    }

    /// **A non-positive occurrence is rejected**, not declined: `W` with a
    /// constructor field `(W → W) → W` puts the block in its own field's
    /// domain, which is official's "non positive occurrence".  The recogniser
    /// admits the block (con-leche task #220: the type and the constructors
    /// are checked first) and the install throws `.invalid`.
    #[test]
    fn a_non_positive_occurrence_is_rejected() {
        let t = nm("W");
        let w = expr::mk_const(name::dup(&t), Vec::new());
        let cv_t = cv(name::dup(&t), Vec::new(), sort1());
        // `Wmk : ∀ (_ : W → W), W`
        let cv_mk = cv(
            nm("Wmk"),
            Vec::new(),
            expr::forall_e(
                expr::forall_e(expr::dup(&w), expr::dup(&w), raw()),
                expr::dup(&w),
                raw(),
            ),
        );
        // a stub recursor: its pin is thrown at the recursor stage, which this
        // block never reaches
        let cv_r = cv(child(&t, "rec"), Vec::new(), expr::dup(&w));
        let mut rules: Vec<RecRule> = Vec::new();
        rules.push(env::rec_rule_parsed(nm("Wmk"), 1, expr::dup(&w)));
        let mut block: Vec<ConstantInfo> = Vec::new();
        block.push(ConstantInfo::IndInfo(cv_t, env::ind_caps_default()));
        block.push(ConstantInfo::CtorInfo(cv_mk, 0, 1));
        block.push(ConstantInfo::RecInfo(cv_r, 2, 2, rules));

        let p = native_parts::native_parts(0, &block).expect("the block is admitted");
        // the recogniser pins nothing of the recursor's *type* (con-leche task
        // #220), so this stub is admitted and the positivity reject comes out
        // before the recursor stage would look at it
        let fe: FEnv = fenv::mk_fenv(env::empty());
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        match check_native(&mode, &mut st, &fe, &p) {
            Err(CheckError::Invalid(_)) => {}
            Err(_) => panic!("a non-positive occurrence must be `.invalid`, not a decline"),
            Ok(_) => panic!("a non-positive occurrence must not install"),
        }
    }

    /// **A mutual and a multi-recursor block are refused by the recogniser**
    /// and fall through to the modeled path: `sumSplit` admits one type former
    /// and one closing recursor, and measuring that over Mathlib is how
    /// con-leche's task #219 settled that no direct block is mutual or nested.
    #[test]
    fn a_mutual_block_is_not_this_route() {
        let cv_a = cv(nm("Ma"), Vec::new(), sort1());
        let cv_b = cv(nm("Mb"), Vec::new(), sort1());
        let cv_c = cv(nm("Mc"), Vec::new(), expr::mk_const(nm("Ma"), Vec::new()));
        let cv_r = cv(child(&nm("Ma"), "rec"), Vec::new(), sort1());
        let cv_r2 = cv(child(&nm("Mb"), "rec"), Vec::new(), sort1());

        // two type formers: `sumSplit` stops at the second `.indInfo`
        let mut mutual: Vec<ConstantInfo> = Vec::new();
        mutual.push(ConstantInfo::IndInfo(
            env::constant_val_dup(&cv_a),
            env::ind_caps_default(),
        ));
        mutual.push(ConstantInfo::IndInfo(
            env::constant_val_dup(&cv_b),
            env::ind_caps_default(),
        ));
        mutual.push(ConstantInfo::CtorInfo(
            env::constant_val_dup(&cv_c),
            0,
            0,
        ));
        mutual.push(ConstantInfo::RecInfo(
            env::constant_val_dup(&cv_r),
            1,
            1,
            Vec::new(),
        ));
        assert!(native_parts::native_parts(0, &mutual).is_none());
        assert!(sum_parts::sum_split(&mutual).is_none());

        // two recursors: the first is not the block's last member
        let mut nested: Vec<ConstantInfo> = Vec::new();
        nested.push(ConstantInfo::IndInfo(cv_a, env::ind_caps_default()));
        nested.push(ConstantInfo::CtorInfo(cv_c, 0, 0));
        nested.push(ConstantInfo::RecInfo(cv_r, 1, 1, Vec::new()));
        nested.push(ConstantInfo::RecInfo(cv_r2, 1, 1, Vec::new()));
        assert!(native_parts::native_parts(0, &nested).is_none());

        // and a block that is not headed by a type former either
        let mut headless: Vec<ConstantInfo> = Vec::new();
        headless.push(ax(nm("Mx"), sort1()));
        assert!(native_parts::native_parts(0, &headless).is_none());
    }

    /// `mentionsFvar`'s memoized walk agrees with the `fvarLeaves`
    /// specification, annotations included.
    #[test]
    fn mentions_fvar_agrees_with_the_specification() {
        let a = expr::mk_const(nm("A"), Vec::new());
        let x = expr::fvar(3, expr::dup(&a));
        let y = expr::fvar(4, expr::dup(&x));
        // `y`'s annotation mentions `3`, so `y` does too
        assert!(mentions_fvar(3, &y));
        assert!(mentions_fvar(4, &y));
        assert!(!mentions_fvar(5, &y));
        assert_eq!(mentions_fvar(3, &y), mentions_fvar_spec(3, &y));
        assert_eq!(mentions_fvar(5, &y), mentions_fvar_spec(5, &y));
        // under binders and through a `.proj`
        let lam = expr::lam(expr::dup(&a), expr::proj(nm("S"), 0, expr::dup(&x)), raw());
        assert!(mentions_fvar(3, &lam));
        assert_eq!(mentions_fvar(3, &lam), mentions_fvar_spec(3, &lam));
        // a closed term mentions nothing
        assert!(!mentions_fvar(0, &a));
        assert!(!mentions_fvar(0, &expr::bvar(0)));
    }
}
