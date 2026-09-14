//! `ConLeche/Kernel/Inductives/NativeParts.lean` — the **direct recursive
//! class**: the positivity classification, the block recogniser, and the
//! generated recursor with its inductive-hypothesis binders.
//!
//! ## The generated recursor is built in the cited order, node for node
//!
//! `checkNativeRec` generates the recursor's type and compares it with the
//! stream's by one closed `isDefEq`, and `nativeRulesOk` compares the
//! stream's rule bodies with the generated ones by **structural equality**.
//! So every generator below reproduces con-leche's construction order
//! exactly: the same `liftLooseBVars` amounts and cutoffs at the same points,
//! the same binder data (`Level.zeronessOf ℓ` on every generated binder,
//! `.never` on the motive's own), the same append order in every argument
//! spine.  A deviation would not merely change a term the proof has to
//! relate — it would change a *verdict*.
//!
//! ## The two higher-order arguments are monomorphised (§3.4, task #18's
//! pattern 1)
//!
//! `structIhApp`, `structRuleBodyR`, `structIhPis`, `structMinorTyR` and
//! `structRecRhsR` take `teleOf : Nat → List (Expr × BinderMeta)` and
//! `idxOf : Nat → List Expr`.  Every call site in con-leche passes
//! `structFieldTeleOf cty nP nF` and `structFieldIdxOf cty nP nF` — the same
//! `cty`, `nP`, `nF` the caller already has — so the port passes those three
//! and calls the two readers by name.  Closures are out by §3.4 and a
//! one-method trait would put a dictionary in a recursion; this is the same
//! monomorphisation task #18 applied to `liftFueled`.
//!
//! The file's other 16 declarations are the `@[simp]` projection equations of
//! `NativeParts.complete` and `NativeParts.withKinds` plus
//! `nativeCaps_sortZ`; they are the *spec* this port will be proved against.

use crate::kernel::basis_names;
use crate::kernel::core_k;
use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprView};
use crate::kernel::expr_ops;
use crate::kernel::expr_ops::sub_nat;
use crate::kernel::inductives::struct_parts;
use crate::kernel::inductives::sum_parts;
use crate::kernel::inductives::sum_parts::InductiveShape;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The field kinds (`NativeParts.lean:61-81`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// The kind of a constructor field of a recursive block, in the cited
/// constructor order.  Deviation: `deriving Repr, DecidableEq, Inhabited` is
/// dropped (§3.4); the equality is `rec_field_kind_beq` and the `Inhabited`
/// default, which the `getD`s below read, is `.ordinary` as in every cited
/// `getD i .ordinary`.
pub enum RecFieldKind {
    Ordinary,
    Recursive,
    Reflexive,
    Negative,
    Unsupported,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// The copy; a `RecFieldKind` is a tag, so this is Lean's value semantics.
pub fn rec_field_kind_dup(k: &RecFieldKind) -> RecFieldKind {
    match k {
        RecFieldKind::Ordinary => RecFieldKind::Ordinary,
        RecFieldKind::Recursive => RecFieldKind::Recursive,
        RecFieldKind::Reflexive => RecFieldKind::Reflexive,
        RecFieldKind::Negative => RecFieldKind::Negative,
        RecFieldKind::Unsupported => RecFieldKind::Unsupported,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:60-76 RecFieldKind
/// The cited `deriving DecidableEq`, which every `k == .recursive` reads.
pub fn rec_field_kind_beq(a: &RecFieldKind, b: &RecFieldKind) -> bool {
    match a {
        RecFieldKind::Ordinary => match b {
            RecFieldKind::Ordinary => true,
            _ => false,
        },
        RecFieldKind::Recursive => match b {
            RecFieldKind::Recursive => true,
            _ => false,
        },
        RecFieldKind::Reflexive => match b {
            RecFieldKind::Reflexive => true,
            _ => false,
        },
        RecFieldKind::Negative => match b {
            RecFieldKind::Negative => true,
            _ => false,
        },
        RecFieldKind::Unsupported => match b {
            RecFieldKind::Unsupported => true,
            _ => false,
        },
    }
}

/// con-leche: none — `ks.getD i .ordinary` over a `Vec<RecFieldKind>`
/// The out-of-range fallback every cited read spells.
pub fn kind_get_d(ks: &Vec<RecFieldKind>, i: u64) -> RecFieldKind {
    if (i as usize) < ks.len() {
        rec_field_kind_dup(&ks[i as usize])
    } else {
        RecFieldKind::Ordinary
    }
}

/// con-leche: none — a `Vec<RecFieldKind>` copy; Lean shares the list
pub fn kinds_copy(ks: &Vec<RecFieldKind>) -> Vec<RecFieldKind> {
    kinds_copy_from(ks, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `kinds_copy`
pub fn kinds_copy_from(
    ks: &Vec<RecFieldKind>,
    i: usize,
    out: Vec<RecFieldKind>,
) -> Vec<RecFieldKind> {
    if i >= ks.len() {
        out
    } else {
        let mut out = out;
        out.push(rec_field_kind_dup(&ks[i]));
        kinds_copy_from(ks, i + 1, out)
    }
}

/// con-leche: none — a `Vec<Vec<RecFieldKind>>` copy; Lean shares the list
pub fn kindss_copy(kss: &Vec<Vec<RecFieldKind>>) -> Vec<Vec<RecFieldKind>> {
    kindss_copy_from(kss, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `kindss_copy`
pub fn kindss_copy_from(
    kss: &Vec<Vec<RecFieldKind>>,
    i: usize,
    out: Vec<Vec<RecFieldKind>>,
) -> Vec<Vec<RecFieldKind>> {
    if i >= kss.len() {
        out
    } else {
        let mut out = out;
        out.push(kinds_copy(&kss[i]));
        kindss_copy_from(kss, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// Positivity (`NativeParts.lean:83-148`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
/// Is `e` the family at the parameter variables (sitting `o` binders up)
/// followed by `nIdx` index expressions none of which mentions the block?
/// Official's `is_valid_ind_app` exactly.  Deviation: the `&&` cascade is an
/// `if` nest and the final `List.all` over a closure is
/// `args_free_of_from` below (§3.4).
pub fn rec_fam_ok(t: &Name, lps: &Vec<Name>, n_p: u64, n_idx: u64, o: u64, e: &Expr) -> bool {
    let head = expr_ops::get_app_fn(e);
    let expected = expr::mk_const(name::dup(t), struct_parts::params_of(lps));
    if expr::beq(&head, &expected) {
        let args: Vec<Expr> = expr_ops::get_app_args(e);
        if args.len() as u64 == n_p + n_idx {
            if expr::exprs_beq(
                &expr_ops::take_exprs(&args, n_p as usize),
                &struct_parts::struct_ps_at(o, n_p),
            ) {
                args_free_of_from(t, &args, n_p as usize)
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

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:78-87 recFamOk
/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// `(args.drop k).all fun a => !a.mentionsConst T`, as an index recursion
/// (task #3's pattern): the index arguments of a residual are free of the
/// block.  Shared by `recFamOk` and `recCtorKinds`' residual conjunct.
pub fn args_free_of_from(t: &Name, args: &Vec<Expr>, i: usize) -> bool {
    if i >= args.len() {
        true
    } else if struct_parts::mentions_const(t, &args[i]) {
        false
    } else {
        args_free_of_from(t, args, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:89-111 recPositivity
/// Official `check_positivity`'s telescope walk on a field domain that
/// mentions the block, syntactically: `k` binders of the field's own
/// telescope have been peeled (the parameters sit `o + k` binders up).
pub fn rec_positivity(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    e: &Expr,
    k: u64,
) -> RecFieldKind {
    match expr::view(&e) {
        ExprView::ForallE(dom, body, _) => {
            if struct_parts::mentions_const(t, dom) {
                RecFieldKind::Negative
            } else {
                rec_positivity(t, lps, n_p, n_idx, o, body, k + 1)
            }
        }
        _ => {
            if !struct_parts::mentions_const(t, e) {
                RecFieldKind::Ordinary
            } else {
                let head = expr_ops::get_app_fn(e);
                let expected = expr::mk_const(name::dup(t), struct_parts::params_of(lps));
                if expr::beq(&head, &expected) {
                    let args: Vec<Expr> = expr_ops::get_app_args(e);
                    let shape_ok = if args.len() as u64 == n_p + n_idx {
                        expr::exprs_beq(
                            &expr_ops::take_exprs(&args, n_p as usize),
                            &struct_parts::struct_ps_at(o + k, n_p),
                        )
                    } else {
                        false
                    };
                    if shape_ok {
                        if rec_fam_ok(t, lps, n_p, n_idx, o + k, e) {
                            if k == 0 {
                                RecFieldKind::Recursive
                            } else {
                                RecFieldKind::Reflexive
                            }
                        } else {
                            RecFieldKind::Negative
                        }
                    } else {
                        RecFieldKind::Negative
                    }
                } else {
                    match expr::view(&head) {
                        ExprView::Const(t2, _) => {
                            if name::beq(t2, t) {
                                RecFieldKind::Negative
                            } else {
                                RecFieldKind::Unsupported
                            }
                        }
                        _ => RecFieldKind::Unsupported,
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:113-116 recFieldKind
/// The kind of a field whose domain is `dom`, `o` fields into the
/// constructor's telescope.
pub fn rec_field_kind(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    o: u64,
    dom: &Expr,
) -> RecFieldKind {
    if struct_parts::mentions_const(t, dom) {
        rec_positivity(t, lps, n_p, n_idx, o, dom, 0)
    } else {
        RecFieldKind::Ordinary
    }
}

/// con-leche: none — `cbs.getD (nP + i) default` over a `Vec<(Expr, BinderMeta)>`
/// Only the `.1` of Lean's `default : Expr × BinderMeta` is ever read, and
/// that is the derived `Inhabited Expr` — `.bvar 0` (`env::default_expr`,
/// task #14's deviation 3).
pub fn binder_dom_get_d(bs: &Vec<(Expr, BinderMeta)>, i: u64) -> Expr {
    if (i as usize) < bs.len() {
        expr::dup(&bs[i as usize].0)
    } else {
        env::default_expr()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// The per-field `(List.range c.2).map` of `recCtorKinds`: a recursive or
/// reflexive field that a later binder or the residual mentions
/// (`structUsedLater`) is marked unsupported.
pub fn rec_ctor_kinds_at(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    cty: &Expr,
    cbs: &Vec<(Expr, BinderMeta)>,
    n_f: u64,
    i: u64,
    out: Vec<RecFieldKind>,
) -> Vec<RecFieldKind> {
    if i >= n_f {
        out
    } else {
        let dom: Expr = binder_dom_get_d(cbs, n_p + i);
        let k0 = rec_field_kind(t, lps, n_p, n_idx, i, &dom);
        let k = match k0 {
            RecFieldKind::Recursive => {
                if struct_parts::struct_used_later(cty, n_p, i) {
                    RecFieldKind::Unsupported
                } else {
                    RecFieldKind::Recursive
                }
            }
            RecFieldKind::Reflexive => {
                if struct_parts::struct_used_later(cty, n_p, i) {
                    RecFieldKind::Unsupported
                } else {
                    RecFieldKind::Reflexive
                }
            }
            other => other,
        };
        let mut out = out;
        out.push(k);
        rec_ctor_kinds_at(t, lps, n_p, n_idx, cty, cbs, n_f, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// The `ks.map fun _ => .negative` arm: a residual whose index expressions
/// mention the block is official's "invalid return type", so *every* field is
/// reported negative and the install rejects the block.
pub fn kinds_all_negative(n: usize, out: Vec<RecFieldKind>) -> Vec<RecFieldKind> {
    if n == 0 {
        out
    } else {
        let mut out = out;
        out.push(RecFieldKind::Negative);
        kinds_all_negative(n - 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:118-145 recCtorKinds
/// The kinds of one constructor's fields, off its (raw or annotated) type.
pub fn rec_ctor_kinds(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    c: &(ConstantVal, u64),
) -> Option<Vec<RecFieldKind>> {
    match expr_ops::strip_pis(n_p + c.1, &c.0.ty) {
        Some(q) => {
            let ks: Vec<RecFieldKind> = rec_ctor_kinds_at(
                t,
                lps,
                n_p,
                n_idx,
                &c.0.ty,
                &q.0,
                c.1,
                0,
                Vec::new(),
            );
            let resid: Vec<Expr> = expr_ops::get_app_args(&q.1);
            if args_free_of_from(t, &resid, n_p as usize) {
                Some(ks)
            } else {
                Some(kinds_all_negative(ks.len(), Vec::new()))
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
/// All leading `∀` binders of an expression (outermost first) and the body —
/// a recursive field's own telescope.  Deviation: the binder list is
/// accumulated on the way *in*, which is the same outermost-first order
/// (task #13's pattern 3).
pub fn pi_binders(e: &Expr) -> (Vec<(Expr, BinderMeta)>, Expr) {
    pi_binders_go(e, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:147-154 Expr.piBinders
/// The accumulator recursion behind `pi_binders`.
pub fn pi_binders_go(e: &Expr, out: Vec<(Expr, BinderMeta)>) -> (Vec<(Expr, BinderMeta)>, Expr) {
    match expr::view(&e) {
        ExprView::ForallE(ty, b, m) => {
            let mut out = out;
            out.push((expr::dup(ty), expr::binder_meta_dup(m)));
            pi_binders_go(b, out)
        }
        _ => (out, expr::dup(e)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:156-161 structFieldTeleOf
/// Field `i`'s own telescope `a⃗ : A⃗` (at the field's frame: the parameters
/// and the earlier fields), off the constructor's type.
pub fn struct_field_tele_of(cty: &Expr, n_p: u64, n_f: u64, i: u64) -> Vec<(Expr, BinderMeta)> {
    match expr_ops::strip_pis(n_p + n_f, cty) {
        Some(q) => pi_binders(&binder_dom_get_d(&q.0, n_p + i)).0,
        None => Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:163-169 structFieldIdxOf
/// The index expressions of field `i`'s domain `Π a⃗, T p⃗ e⃗` (under the
/// field's own telescope, at the field's frame), off the constructor's type;
/// `[]` when the field is not of that shape.
pub fn struct_field_idx_of(cty: &Expr, n_p: u64, n_f: u64, i: u64) -> Vec<Expr> {
    match expr_ops::strip_pis(n_p + n_f, cty) {
        Some(q) => {
            let body: Expr = pi_binders(&binder_dom_get_d(&q.0, n_p + i)).1;
            let args: Vec<Expr> = expr_ops::get_app_args(&body);
            core_k::drop_exprs(&args, n_p as usize)
        }
        None => Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
/// The positions of the recursive fields (finitary or reflexive: the ones
/// with an inductive hypothesis).  The `i = 0` wrapper of the recursion
/// below.
pub fn rec_idx_of(ks: &Vec<RecFieldKind>) -> Vec<u64> {
    rec_idx_of_from(ks, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:171-175 recIdxOf
/// The index recursion behind `rec_idx_of` (the cited
/// `(List.range ks.length).filter`).
pub fn rec_idx_of_from(ks: &Vec<RecFieldKind>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= ks.len() {
        out
    } else {
        let k = kind_get_d(ks, i as u64);
        let keep = if rec_field_kind_beq(&k, &RecFieldKind::Recursive) {
            true
        } else {
            rec_field_kind_beq(&k, &RecFieldKind::Reflexive)
        };
        let mut out = out;
        if keep {
            out.push(i as u64);
        }
        rec_idx_of_from(ks, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// `NativeParts` (`NativeParts.lean:178-231`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
/// The pieces of a recognised direct recursive block: the sum parts (with the
/// family's index count), the per-constructor field kinds, and the verdict of
/// the stream's recursor record's structural pin.
///
/// Deviation: Lean's `extends InductiveShape` gives a `toInductiveShape`
/// field; the port spells it `shape` and every reader goes through it
/// (`p.shape.cv_t` for `p.cvT`).  `deriving Repr` is dropped.
pub struct NativeParts {
    pub shape: InductiveShape,
    pub kinds: Vec<Vec<RecFieldKind>>,
    pub rec_pinned: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:177-192 NativeParts
/// The record copy.
pub fn native_parts_dup(p: &NativeParts) -> NativeParts {
    NativeParts {
        shape: sum_parts::inductive_shape_dup(&p.shape),
        kinds: kindss_copy(&p.kinds),
        rec_pinned: p.rec_pinned,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:194-199 NativeParts.complete
/// **The record completed by the former's stage**: the sum parts the former's
/// run returned (its result sort read through `whnf`) with the recogniser's
/// field kinds and its recursor verdict.
pub fn complete(p0: &NativeParts, p1: InductiveShape) -> NativeParts {
    NativeParts {
        shape: p1,
        kinds: kindss_copy(&p0.kinds),
        rec_pinned: p0.rec_pinned,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:616-622 NativeParts.withKinds
/// The record completed with the fields' kinds the install classified on the
/// constructors it stored.  Taken by value and returned, as the cited
/// `{ p with … }` is.
pub fn with_kinds(p: NativeParts, ks: Vec<Vec<RecFieldKind>>) -> NativeParts {
    let mut p = p;
    p.kinds = ks;
    p
}

// ---------------------------------------------------------------------------
// The generated recursor with inductive hypotheses
// (`NativeParts.lean:232-389`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
/// The parameter, motive and minor variables as seen from under the `nF`
/// fields (and `e` further binders): the recursor's leading spine
/// `p⃗ motive m⃗` at that frame.
pub fn struct_rec_prefix_at(n_p: u64, n: u64, n_f: u64, e: u64) -> Vec<Expr> {
    let mut out: Vec<Expr> = struct_parts::struct_ps_at(e + n_f + n + 1, n_p);
    out.push(expr::bvar(e + n_f + n));
    struct_rec_prefix_minors(n, e + n_f + n, 0, out)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:230-235 structRecPrefixAt
/// The minor half of the prefix spine,
/// `(List.range n).map fun l => .bvar (e + nF + n - 1 - l)`.
pub fn struct_rec_prefix_minors(n: u64, base: u64, l: u64, out: Vec<Expr>) -> Vec<Expr> {
    if l >= n {
        out
    } else {
        let mut out = out;
        out.push(expr::bvar(sub_nat(base, 1 + l)));
        struct_rec_prefix_minors(n, base, l + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
/// An expression of recursive field `i`'s domain sitting under `m` binders of
/// the field's own telescope, spelled at the field's frame, moved under all
/// `nF` fields, `l` further binders below them and `o` extras between the
/// parameters and the fields.  `nF - i` is Lean's truncated subtraction.
pub fn struct_idx_at(n_f: u64, o: u64, i: u64, l: u64, m: u64, e: &Expr) -> Expr {
    let step1: Expr = expr_ops::lift_loose_bvars(sub_nat(n_f, i) + l, m, e);
    expr_ops::lift_loose_bvars(o, n_f + l + m, &step1)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:237-244 structIdxAt
/// `idx.map (structIdxAt nF o i l m)` over a `Vec<Expr>`.
pub fn struct_idx_at_all(
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    m: u64,
    idx: &Vec<Expr>,
    j: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if j >= idx.len() {
        out
    } else {
        let mut out = out;
        out.push(struct_idx_at(n_f, o, i, l, m, &idx[j]));
        struct_idx_at_all(n_f, o, i, l, m, idx, j + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
/// Field `i`'s own telescope moved as `structIdxAt` moves its expressions
/// (binder `k` sits under `k` earlier telescope binders), every binder's
/// datum reset to `pw`.
pub fn struct_tele_at(
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    pw: &PropWhen,
    tele: &Vec<(Expr, BinderMeta)>,
) -> Vec<(Expr, BinderMeta)> {
    struct_tele_at_from(n_f, o, i, l, pw, tele, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:246-252 structTeleAt
/// The index recursion behind `struct_tele_at`.
pub fn struct_tele_at_from(
    n_f: u64,
    o: u64,
    i: u64,
    l: u64,
    pw: &PropWhen,
    tele: &Vec<(Expr, BinderMeta)>,
    k: usize,
    out: Vec<(Expr, BinderMeta)>,
) -> Vec<(Expr, BinderMeta)> {
    if k >= tele.len() {
        out
    } else {
        let dom: Expr = struct_idx_at(n_f, o, i, l, k as u64, &tele[k].0);
        let mut out = out;
        out.push((
            dom,
            expr::binder_meta(prop_when::dup(pw)),
        ));
        struct_tele_at_from(n_f, o, i, l, pw, tele, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:254-255 structTeleVars
/// The variables of an `m`-binder telescope, innermost last.  Identical to
/// `struct_parts::field_spine`, which is where the port spells the recursion
/// (the constructor spines need it and `StructParts.lean` is below this
/// file).
pub fn struct_tele_vars(m: u64) -> Vec<Expr> {
    struct_parts::field_spine(m)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
/// `∀ tele, body` over a binder list (outermost first).  Built on the way
/// out, as cited; the port walks the `Vec` by index.
pub fn mk_pis_of(tele: &Vec<(Expr, BinderMeta)>, body: Expr) -> Expr {
    mk_pis_of_from(tele, 0, body)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:257-260 Expr.mkPisOf
/// The index recursion behind `mk_pis_of`.
pub fn mk_pis_of_from(tele: &Vec<(Expr, BinderMeta)>, i: usize, body: Expr) -> Expr {
    if i >= tele.len() {
        body
    } else {
        let rest: Expr = mk_pis_of_from(tele, i + 1, body);
        expr::forall_e(
            expr::dup(&tele[i].0),
            rest,
            expr::binder_meta_dup(&tele[i].1),
        )
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
/// `λ tele, body` over a binder list (outermost first).
pub fn mk_lams_of(tele: &Vec<(Expr, BinderMeta)>, body: Expr) -> Expr {
    mk_lams_of_from(tele, 0, body)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:261-263 Expr.mkLamsOf
/// The index recursion behind `mk_lams_of`.
pub fn mk_lams_of_from(tele: &Vec<(Expr, BinderMeta)>, i: usize, body: Expr) -> Expr {
    if i >= tele.len() {
        body
    } else {
        let rest: Expr = mk_lams_of_from(tele, i + 1, body);
        expr::lam(
            expr::dup(&tele[i].0),
            rest,
            expr::binder_meta_dup(&tele[i].1),
        )
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:265-277 structIhApp
/// The inductive hypothesis' value for recursive field `i`:
/// `λ a⃗, T.rec p⃗ motive m⃗ e⃗_i(a⃗) (f_i a⃗)` — at a finitary field the
/// telescope is empty and this is the recursor at the prefix, the field's
/// indices and the field.
///
/// Deviation: `teleOf`/`idxOf` are `cty`/`nP`/`nF` (module note).
pub fn struct_ih_app(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    i: u64,
    cty: &Expr,
) -> Expr {
    let tele: Vec<(Expr, BinderMeta)> = struct_field_tele_of(cty, n_p, n_f, i);
    let idx: Vec<Expr> = struct_field_idx_of(cty, n_p, n_f, i);
    let m: u64 = tele.len() as u64;
    let head = expr::mk_const(name::dup(rec_c), env::levels_copy(rlvls));
    let mut args: Vec<Expr> = struct_rec_prefix_at(n_p, n, n_f, m);
    args = core_k::append_exprs(
        args,
        &struct_idx_at_all(n_f, n + 1, i, 0, m, &idx, 0, Vec::new()),
    );
    args.push(expr_ops::mk_app_n(
        expr::bvar(sub_nat(n_f, 1 + i) + m),
        &struct_tele_vars(m),
    ));
    mk_lams_of(
        &struct_tele_at(n_f, n + 1, i, 0, pw, &tele),
        expr_ops::mk_app_n(head, &args),
    )
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
/// The right-hand side body of rule `j` at a recursive block: minor `j` at
/// the fields, then at the inductive hypotheses of the recursive fields.
pub fn struct_rule_body_r(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    j: u64,
    rec_idx: &Vec<u64>,
    cty: &Expr,
) -> Expr {
    let mut args: Vec<Expr> = struct_tele_vars(n_f);
    args = struct_ih_apps(rec_c, rlvls, pw, n_p, n, n_f, rec_idx, cty, 0, args);
    expr_ops::mk_app_n(expr::bvar(sub_nat(n_f + n, 1 + j)), &args)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:279-288 structRuleBodyR
/// `recIdx.map fun i => structIhApp …`, as an index recursion.
pub fn struct_ih_apps(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    n_f: u64,
    rec_idx: &Vec<u64>,
    cty: &Expr,
    k: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if k >= rec_idx.len() {
        out
    } else {
        let mut out = out;
        out.push(struct_ih_app(
            rec_c,
            rlvls,
            pw,
            n_p,
            n,
            n_f,
            rec_idx[k],
            cty,
        ));
        struct_ih_apps(rec_c, rlvls, pw, n_p, n, n_f, rec_idx, cty, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:290-305 structIhPis
/// The `ih` binders of a minor premise: for each recursive field position (in
/// order), `∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗)` under the `l` earlier `ih` binders.
/// Built on the way out, as cited; `k` is the cursor into `recIdx` and `l`
/// the count already emitted.
pub fn struct_ih_pis(
    n_f: u64,
    o: u64,
    pw: &PropWhen,
    cty: &Expr,
    n_p: u64,
    rec_idx: &Vec<u64>,
    k: usize,
    l: u64,
    body: Expr,
) -> Expr {
    if k >= rec_idx.len() {
        body
    } else {
        let i: u64 = rec_idx[k];
        let tele: Vec<(Expr, BinderMeta)> = struct_field_tele_of(cty, n_p, n_f, i);
        let idx: Vec<Expr> = struct_field_idx_of(cty, n_p, n_f, i);
        let m: u64 = tele.len() as u64;
        let mut margs: Vec<Expr> =
            struct_idx_at_all(n_f, o, i, l, m, &idx, 0, Vec::new());
        margs.push(expr_ops::mk_app_n(
            expr::bvar(sub_nat(n_f, 1 + i) + l + m),
            &struct_tele_vars(m),
        ));
        let dom: Expr = mk_pis_of(
            &struct_tele_at(n_f, o, i, l, pw, &tele),
            expr_ops::mk_app_n(expr::bvar(sub_nat(n_f + o, 1) + l + m), &margs),
        );
        let rest: Expr =
            struct_ih_pis(n_f, o, pw, cty, n_p, rec_idx, k + 1, l + 1, body);
        expr::forall_e(
            dom,
            rest,
            expr::binder_meta(prop_when::dup(pw)),
        )
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
/// A constructor's minor premise at a recursive block: its field telescope
/// lifted under the `o` extras, every binder's datum reset to the elimination
/// datum, then the `ih` binders, ending in `motive e⃗ (C p⃗ f⃗)` lifted above
/// the `ih`s.
pub fn struct_minor_ty_r(
    c: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    o: u64,
    pw: &PropWhen,
    cty: &Expr,
    rec_idx: &Vec<u64>,
) -> Option<Expr> {
    match expr_ops::strip_pis(n_p, cty) {
        Some(q) => match expr_ops::strip_pis(n_f, &q.1) {
            Some(r) => {
                let resid: Vec<Expr> = expr_ops::get_app_args(&r.1);
                let idxs: Vec<Expr> = lift_all(
                    o,
                    n_f,
                    &core_k::drop_exprs(&resid, n_p as usize),
                    0,
                    Vec::new(),
                );
                let mut cargs: Vec<Expr> = idxs;
                cargs.push(struct_ctor_spine_at_o(c, lps, o, n_p, n_f));
                let concl: Expr = expr_ops::lift_loose_bvars(
                    rec_idx.len() as u64,
                    0,
                    &expr_ops::mk_app_n(expr::bvar(sub_nat(n_f + o, 1)), &cargs),
                );
                let inner: Expr =
                    struct_ih_pis(n_f, o, pw, cty, n_p, rec_idx, 0, 0, concl);
                let lifted: Expr = expr_ops::lift_loose_bvars(o, 0, &q.1);
                struct_parts::replace_pis_pw(pw, n_f, &lifted, &inner)
            }
            None => None,
        },
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:144-150 structCtorSpineAt
/// `structCtorSpineAt` under the name the minor-premise generator calls it
/// by; `struct_parts` holds the recursion.
pub fn struct_ctor_spine_at_o(c: &Name, lps: &Vec<Name>, o: u64, n_p: u64, n_f: u64) -> Expr {
    struct_parts::struct_ctor_spine_at(c, lps, o, n_p, n_f)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:307-320 structMinorTyR
/// `(r.2.getAppArgs.drop nP).map (Expr.liftLooseBVars o nF)`, as an index
/// recursion.
pub fn lift_all(o: u64, cut: u64, es: &Vec<Expr>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= es.len() {
        out
    } else {
        let mut out = out;
        out.push(expr_ops::lift_loose_bvars(o, cut, &es[i]));
        lift_all(o, cut, es, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:322-330 structMinorsPisR
/// The minor premises' `∀`-telescope at a recursive block, one per
/// constructor `(C, nF, cty, recIdx)`.  `k` is the cursor into `ctors` and
/// `o` the cited extras count, which grows by one per minor.
pub fn struct_minors_pis_r(
    lps: &Vec<Name>,
    n_p: u64,
    pw: &PropWhen,
    ctors: &Vec<(Name, u64, Expr, Vec<u64>)>,
    k: usize,
    o: u64,
    body: &Expr,
) -> Option<Expr> {
    if k >= ctors.len() {
        Some(expr::dup(body))
    } else {
        match struct_minor_ty_r(
            &ctors[k].0,
            lps,
            n_p,
            ctors[k].1,
            o,
            pw,
            &ctors[k].2,
            &ctors[k].3,
        ) {
            Some(mty) => match struct_minors_pis_r(lps, n_p, pw, ctors, k + 1, o + 1, body) {
                Some(rest) => Some(expr::forall_e(
                    mty,
                    rest,
                    expr::binder_meta(prop_when::dup(pw)),
                )),
                None => None,
            },
            None => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:332-339 structMinorsLamsR
/// The `λ` twin of `structMinorsPisR`.
pub fn struct_minors_lams_r(
    lps: &Vec<Name>,
    n_p: u64,
    pw: &PropWhen,
    ctors: &Vec<(Name, u64, Expr, Vec<u64>)>,
    k: usize,
    o: u64,
    body: &Expr,
) -> Option<Expr> {
    if k >= ctors.len() {
        Some(expr::dup(body))
    } else {
        match struct_minor_ty_r(
            &ctors[k].0,
            lps,
            n_p,
            ctors[k].1,
            o,
            pw,
            &ctors[k].2,
            &ctors[k].3,
        ) {
            Some(mty) => match struct_minors_lams_r(lps, n_p, pw, ctors, k + 1, o + 1, body) {
                Some(rest) => Some(expr::lam(
                    mty,
                    rest,
                    expr::binder_meta(prop_when::dup(pw)),
                )),
                None => None,
            },
            None => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:341-362 structRecTyR
/// **The generated recursor type at a recursive block**
///
/// ```text
/// ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
///   (minor_C : ∀ f⃗ (ih⃗ : motive e⃗_i f_i)…, motive e⃗ (C p⃗ f⃗))…
///   ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t
/// ```
///
/// Deviation: each cited `Option.bind`/`.map` over a closure is an explicit
/// `match` (§3.4); the construction order is the cited one node for node
/// (module note).
pub fn struct_rec_ty_r(
    t: &Name,
    lps: &Vec<Name>,
    elim: &Name,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &Expr,
    ctors: &Vec<(Name, u64, Expr, Vec<u64>)>,
) -> Option<Expr> {
    let l: Level = struct_parts::struct_elim_level(elim, large);
    let pw: PropWhen = level::zeroness_of(&l);
    let n: u64 = ctors.len() as u64;
    match expr_ops::strip_pis(n_p, tty) {
        Some(q) => match struct_parts::struct_motive_ty_i(t, lps, n_p, n_idx, &l, &q.1) {
            Some(motive_ty) => {
                let mut margs: Vec<Expr> = struct_parts::struct_ps_at(1, n_idx);
                margs.push(expr::bvar(0));
                let major_body: Expr = expr::forall_e(
                    struct_parts::struct_fam_i(t, lps, n_p, n_idx, n + 1, 0),
                    expr_ops::mk_app_n(expr::bvar(n_idx + n + 1), &margs),
                    expr::binder_meta(prop_when::dup(&pw)),
                );
                let itele: Expr = expr_ops::lift_loose_bvars(n + 1, 0, &q.1);
                match struct_parts::replace_pis_pw(&pw, n_idx, &itele, &major_body) {
                    Some(major) => {
                        match struct_minors_pis_r(lps, n_p, &pw, ctors, 0, 1, &major) {
                            Some(minors) => {
                                let body: Expr = expr::forall_e(
                                    motive_ty,
                                    minors,
                                    expr::binder_meta(prop_when::dup(&pw)),
                                );
                                struct_parts::replace_pis_pw(&pw, n_p, tty, &body)
                            }
                            None => None,
                        }
                    }
                    None => None,
                }
            }
            None => None,
        },
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:364-386 structRecRhsR
/// **The generated rule** for constructor `j` at a recursive block:
/// `λ p⃗ motive minor⃗ f⃗_j, minor_j f⃗_j (T.rec p⃗ motive minor⃗ e⃗_i f_i)…`.
pub fn struct_rec_rhs_r(
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
    j: u64,
) -> Option<Expr> {
    let l: Level = struct_parts::struct_elim_level(elim, large);
    let pw: PropWhen = level::zeroness_of(&l);
    let n: u64 = ctors.len() as u64;
    if (j as usize) >= ctors.len() {
        None
    } else {
        let n_f: u64 = ctors[j as usize].1;
        let cty: Expr = expr::dup(&ctors[j as usize].2);
        let rec_idx: Vec<u64> = u64s_copy(&ctors[j as usize].3);
        match expr_ops::strip_pis(n_p, tty) {
            Some(tq) => match struct_parts::struct_motive_ty_i(t, lps, n_p, n_idx, &l, &tq.1) {
                Some(motive_ty) => match expr_ops::strip_pis(n_p, &cty) {
                    Some(q) => {
                        let body: Expr = struct_rule_body_r(
                            rec_c, rlvls, &pw, n_p, n, n_f, j, &rec_idx, &cty,
                        );
                        let lifted: Expr = expr_ops::lift_loose_bvars(n + 1, 0, &q.1);
                        match struct_parts::pis_to_lams_pw(&pw, n_f, &lifted, &body) {
                            Some(inner) => {
                                match struct_minors_lams_r(lps, n_p, &pw, ctors, 0, 1, &inner) {
                                    Some(minors) => {
                                        let lam: Expr = expr::lam(
                                            motive_ty,
                                            minors,
                                            expr::binder_meta(prop_when::dup(&pw)),
                                        );
                                        struct_parts::pis_to_lams_pw(&pw, n_p, tty, &lam)
                                    }
                                    None => None,
                                }
                            }
                            None => None,
                        }
                    }
                    None => None,
                },
                None => None,
            },
            None => None,
        }
    }
}

/// con-leche: none — a `Vec<u64>` copy; Lean shares the `List Nat`
pub fn u64s_copy(xs: &Vec<u64>) -> Vec<u64> {
    u64s_copy_from(xs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `u64s_copy`
pub fn u64s_copy_from(xs: &Vec<u64>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= xs.len() {
        out
    } else {
        let mut out = out;
        out.push(xs[i]);
        u64s_copy_from(xs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
/// The constructors zipped with their recursive positions, as the generators
/// take them.  `List.zipWith` stops at the shorter list, as the port does.
pub fn native_ctors4(
    ctors_a: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
) -> Vec<(Name, u64, Expr, Vec<u64>)> {
    native_ctors4_from(ctors_a, kinds, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:388-392 nativeCtors4
/// The index recursion behind `native_ctors4`.
pub fn native_ctors4_from(
    ctors_a: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    i: usize,
    out: Vec<(Name, u64, Expr, Vec<u64>)>,
) -> Vec<(Name, u64, Expr, Vec<u64>)> {
    if i >= ctors_a.len() {
        out
    } else if i >= kinds.len() {
        out
    } else {
        let mut out = out;
        out.push((
            name::dup(&ctors_a[i].0.name),
            ctors_a[i].1,
            expr::dup(&ctors_a[i].0.ty),
            rec_idx_of(&kinds[i]),
        ));
        native_ctors4_from(ctors_a, kinds, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The rules against the generated ones (`NativeParts.lean:395-478`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// The leading `(List.range (nP + 1 + n)).all` of `nativeRulePrefixOk`: the
/// rule's first `nP + 1 + n` λ-domains are the recursor record's own Π-domains
/// at the same depths, up to the parse placeholder's binder data
/// (`resetMeta`).
pub fn native_rule_prefix_head(
    rbs: &Vec<(Expr, BinderMeta)>,
    tbs: &Vec<(Expr, BinderMeta)>,
    n: u64,
    i: u64,
) -> bool {
    if i >= n {
        true
    } else if (i as usize) >= rbs.len() {
        false
    } else if (i as usize) >= tbs.len() {
        false
    } else if expr::beq(
        &expr_ops::reset_meta(&rbs[i as usize].0),
        &expr_ops::reset_meta(&tbs[i as usize].0),
    ) {
        native_rule_prefix_head(rbs, tbs, n, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// The trailing `(List.range nF).all`: the rule's field λ-domains are the
/// `j`-th minor premise's first `nF` Π-domains, lifted by `n - j`.
pub fn native_rule_prefix_fields(
    rbs: &Vec<(Expr, BinderMeta)>,
    fbs: &Vec<(Expr, BinderMeta)>,
    base: u64,
    n_f: u64,
    i: u64,
) -> bool {
    if i >= n_f {
        true
    } else if ((base + i) as usize) >= rbs.len() {
        false
    } else if (i as usize) >= fbs.len() {
        false
    } else if expr::beq(
        &expr_ops::reset_meta(&rbs[(base + i) as usize].0),
        &expr_ops::reset_meta(&fbs[i as usize].0),
    ) {
        native_rule_prefix_fields(rbs, fbs, base, n_f, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:394-445 nativeRulePrefixOk
/// **The rule's `λ` prefix against the stream's own recursor type.**  The
/// comparison is deliberately NOT with `structRecRhsR`: the two are generated
/// from different data (this route generates from the STORED constructors,
/// official from the declared ones and from a whnf'd telescope), and
/// comparing the terms rejects 45 e2e fixtures official accepts — the cited
/// docstring says why.
pub fn native_rule_prefix_ok(
    rec_ty: &Expr,
    n_p: u64,
    n: u64,
    j: u64,
    n_f: u64,
    rhs: &Expr,
) -> bool {
    match expr_ops::strip_lams(n_p + 1 + n + n_f, rhs) {
        Some(rq) => match expr_ops::strip_pis(n_p + 1 + n, rec_ty) {
            Some(tq) => {
                if native_rule_prefix_head(&rq.0, &tq.0, n_p + 1 + n, 0) {
                    if ((n_p + 1 + j) as usize) < tq.0.len() {
                        let mty: Expr = expr_ops::lift_loose_bvars(
                            sub_nat(n, j),
                            0,
                            &tq.0[(n_p + 1 + j) as usize].0,
                        );
                        match expr_ops::strip_pis(n_f, &mty) {
                            Some(fq) => native_rule_prefix_fields(
                                &rq.0,
                                &fq.0,
                                n_p + 1 + n,
                                n_f,
                                0,
                            ),
                            None => false,
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            None => false,
        },
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// One rule of `nativeRulesOk`: the field count, the body against the
/// canonical right-hand side at the parse placeholder's binder data, and the
/// λ prefix.
pub fn native_rule_ok(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    rhs: &Expr,
    c_a: &(ConstantVal, u64),
    ks: &Vec<RecFieldKind>,
    rec_ty: &Expr,
    j: u64,
) -> bool {
    let n_f: u64 = c_a.1;
    if ks.len() as u64 == n_f {
        let body_ok = match expr_ops::strip_lams(n_p + 1 + n + n_f, rhs) {
            Some(q) => {
                let generated: Expr = struct_rule_body_r(
                    rec_c,
                    rlvls,
                    pw,
                    n_p,
                    n,
                    n_f,
                    j,
                    &rec_idx_of(ks),
                    &c_a.0.ty,
                );
                expr::beq(&q.1, &expr_ops::reset_meta(&generated))
            }
            None => false,
        };
        if body_ok {
            native_rule_prefix_ok(rec_ty, n_p, n, j, n_f, rhs)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// **The stream's rules against the generated ones**, at install: rule `j`
/// fires constructor `j` with its field count, and its body is the canonical
/// right-hand side with the inductive hypotheses.
pub fn native_rules_ok(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    cs: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    rhss: &Vec<Expr>,
    rec_ty: &Expr,
) -> bool {
    if rhss.len() as u64 == n {
        if kinds.len() as u64 == n {
            native_rules_ok_from(rec_c, rlvls, pw, n_p, n, cs, kinds, rhss, rec_ty, 0)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:447-475 nativeRulesOk
/// The `(List.range n).all` behind `native_rules_ok`.
pub fn native_rules_ok_from(
    rec_c: &Name,
    rlvls: &Vec<Level>,
    pw: &PropWhen,
    n_p: u64,
    n: u64,
    cs: &Vec<(ConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    rhss: &Vec<Expr>,
    rec_ty: &Expr,
    j: u64,
) -> bool {
    if j >= n {
        true
    } else if (j as usize) >= rhss.len() {
        false
    } else if (j as usize) >= cs.len() {
        false
    } else if (j as usize) >= kinds.len() {
        false
    } else if native_rule_ok(
        rec_c,
        rlvls,
        pw,
        n_p,
        n,
        &rhss[j as usize],
        &cs[j as usize],
        &kinds[j as usize],
        rec_ty,
        j,
    ) {
        native_rules_ok_from(rec_c, rlvls, pw, n_p, n, cs, kinds, rhss, rec_ty, j + 1)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Recognition (`NativeParts.lean:479-653`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:501-523 nativeCounts?
/// **The block's parameter and index counts**, read as official reads them:
/// `nP` is the count the DECLARATION carries and `nIdx` is what is left of
/// the type former's Π-telescope once those binders are peeled.  At a former
/// declared at a *definition* the syntactic telescope is not the one official
/// walks, so the recursor record's argument sums are the only reading
/// available.
pub fn native_counts(
    n_pd: u64,
    cv_t: &ConstantVal,
    cs: &Vec<(ConstantVal, u64, u64)>,
    m_i: u64,
    r_p: u64,
) -> Option<(u64, u64)> {
    let q = pi_binders(&cv_t.ty);
    match expr::view(&q.1 ) {
        ExprView::Sort(_) => {
            if n_pd <= q.0.len() as u64 {
                Some((n_pd, q.0.len() as u64 - n_pd))
            } else {
                None
            }
        }
        _ => {
            if r_p < cs.len() as u64 + 1 {
                None
            } else if m_i < r_p {
                None
            } else if r_p - (cs.len() as u64 + 1) == n_pd {
                Some((n_pd, m_i - r_p))
            } else {
                None
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
/// The `(List.range p.ctors.length).all` of `nativeRecPinOk`: rule `j` names
/// constructor `j` with its field count.
pub fn native_rec_pin_rules(
    rules: &Vec<env::RecRule>,
    cs: &Vec<(ConstantVal, u64, u64)>,
    n: u64,
    j: u64,
) -> bool {
    if j >= n {
        true
    } else if (j as usize) >= rules.len() {
        false
    } else if (j as usize) >= cs.len() {
        false
    } else if name::beq(&rules[j as usize].ctor, &cs[j as usize].0.name) {
        if rules[j as usize].nfields == cs[j as usize].2 {
            native_rec_pin_rules(rules, cs, n, j + 1)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:525-549 nativeRecPinOk
/// **The recursor record's structural pin**: the two argument sums the record
/// claims, one rule per constructor in constructor order, each rule naming its
/// constructor with its field count.  Official's replay compares the exported
/// recursor with the generated one by structural equality, so a `false` here
/// is a REJECT, thrown at the recursor stage.
pub fn native_rec_pin_ok(p: &InductiveShape, block: &Vec<ConstantInfo>) -> bool {
    if block.len() == 0 {
        false
    } else {
        match &block[0] {
            ConstantInfo::IndInfo(_, _) => {
                match sum_parts::sum_split_from(block, 1, Vec::new()) {
                    Some(q) => {
                        let n: u64 = p.ctors.len() as u64;
                        if q.3 == p.n_p + 1 + n {
                            if q.2 == p.n_p + 1 + n + p.n_idx {
                                if q.4.len() as u64 == n {
                                    native_rec_pin_rules(&q.4, &q.0, n, 0)
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
                    None => false,
                }
            }
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:551-560 nativeRecLpsOk
/// **The recursor record's level-parameter pin**: the recursor official
/// generates carries the block's own level parameters, with a fresh
/// elimination parameter in front at the LARGE eliminator.
pub fn native_rec_lps_ok(p: &InductiveShape) -> bool {
    if p.large {
        let mut expected: Vec<Name> = Vec::new();
        expected.push(name::dup(&p.elim));
        expected = prop_when::append_from(&p.cv_t.level_params, 0, expected);
        prop_when::names_beq(&p.cv_r.level_params, &expected)
    } else {
        prop_when::names_beq(&p.cv_r.level_params, &p.cv_t.level_params)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The `cs.all` front guard of `nativeShape?`: every constructor carries the
/// block's parameter count and level parameters and no reserved basis name.
pub fn native_ctors_ok_from(
    cs: &Vec<(ConstantVal, u64, u64)>,
    n_p: u64,
    lps: &Vec<Name>,
    reserved: &Vec<Name>,
    i: usize,
) -> bool {
    if i >= cs.len() {
        true
    } else if cs[i].1 == n_p {
        if prop_when::names_beq(&cs[i].0.level_params, lps) {
            if !name::contains(reserved, &cs[i].0.name) {
                native_ctors_ok_from(cs, n_p, lps, reserved, i + 1)
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

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The three reserved-name exclusions and the constructors' guard of
/// `nativeShape?`, as one function.  Its own function because the cited
/// `&&` cascade borrows the former and the split's constructors and
/// `nativeShape?` then reads them again: task #14's rule, *never hold a
/// container's borrow across a branch that touches the container* — Aeneas
/// answered *"Could not match the contexts"* at the joined `if`.
pub fn native_shape_names_ok(
    cv_t: &ConstantVal,
    cv_r: &ConstantVal,
    cs: &Vec<(ConstantVal, u64, u64)>,
    n_p: u64,
    reserved: &Vec<Name>,
) -> bool {
    if !name::contains(reserved, &cv_t.name) {
        if !name::contains(reserved, &cv_r.name) {
            native_ctors_ok_from(cs, n_p, &cv_t.level_params, reserved, 0)
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The `cs.map fun c => (c.1, c.2.2)` of `nativeShape?`: the constructors
/// with their *field* counts (the parameter count is the block's).
pub fn native_ctors_of(cs: &Vec<(ConstantVal, u64, u64)>) -> Vec<(ConstantVal, u64)> {
    native_ctors_of_from(cs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The index recursion behind `native_ctors_of`.
pub fn native_ctors_of_from(
    cs: &Vec<(ConstantVal, u64, u64)>,
    i: usize,
    out: Vec<(ConstantVal, u64)>,
) -> Vec<(ConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut out = out;
        out.push((env::constant_val_dup(&cs[i].0), cs[i].2));
        native_ctors_of_from(cs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The `rules.map (·.rhs)` of `nativeShape?`: the rules' right-hand sides as
/// exported.
pub fn native_rhss_of(rules: &Vec<env::RecRule>) -> Vec<Expr> {
    native_rhss_of_from(rules, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The index recursion behind `native_rhss_of`.
pub fn native_rhss_of_from(rules: &Vec<env::RecRule>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= rules.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&rules[i].rhs));
        native_rhss_of_from(rules, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The `large?` reading of `nativeShape?`: a fresh elimination level
/// parameter in front of the block's own.  A record that is neither shape is
/// read as the *small* eliminator with the pin failing (`nativeRecLpsOk`,
/// thrown at `checkNativeRec`) rather than refusing the block.
pub fn native_shape_large(cv_r: &ConstantVal, lps: &Vec<Name>) -> Option<Name> {
    if cv_r.level_params.len() == 0 {
        None
    } else {
        let elim = name::dup(&cv_r.level_params[0]);
        let relps: Vec<Name> = prop_when::append_from(&cv_r.level_params, 1, Vec::new());
        if prop_when::names_beq(&relps, lps) {
            if !name::contains(lps, &elim) {
                Some(elim)
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// The block's shape at a recursive block: the type former, the constructors
/// and the counts (`nativeCounts?`), with the rules' right-hand sides as
/// exported and the recursor's level-parameter shape.  Nothing else of the
/// recursor record is pinned here.
pub fn native_shape(n_pd: u64, block: &Vec<ConstantInfo>) -> Option<InductiveShape> {
    if block.len() == 0 {
        None
    } else {
        match &block[0] {
            ConstantInfo::IndInfo(cv_t, _) => {
                match sum_parts::sum_split_from(block, 1, Vec::new()) {
                    Some(q) => {
                        let reserved: Vec<Name> = basis_names::reserved_basis_names();
                        match native_counts(n_pd, cv_t, &q.0, q.2, q.3) {
                            None => None,
                            Some(counts) => {
                                let n_p: u64 = counts.0;
                                let n_idx: u64 = counts.1;
                                if native_shape_names_ok(
                                    cv_t, &q.1, &q.0, n_p, &reserved,
                                ) {
                                    let s: Level =
                                        match expr_ops::strip_pis(n_p + n_idx, &cv_t.ty) {
                                            Some(tq) => match expr::view(&tq.1 ) {
                                                ExprView::Sort(u) => level::dup(u),
                                                _ => level::zero(),
                                            },
                                            None => level::zero(),
                                        };
                                    let is_prop = struct_parts::level_is_prop(&s);
                                    let ctors: Vec<(ConstantVal, u64)> =
                                        native_ctors_of(&q.0);
                                    let rhss: Vec<Expr> = native_rhss_of(&q.4);
                                    match native_shape_large(&q.1, &cv_t.level_params) {
                                        Some(elim) => Some(InductiveShape {
                                            cv_t: env::constant_val_dup(cv_t),
                                            ctors,
                                            n_p,
                                            n_idx,
                                            cv_r: q.1,
                                            elim,
                                            res_sort: s,
                                            rhss,
                                            large: true,
                                            is_prop,
                                        }),
                                        None => Some(InductiveShape {
                                            cv_t: env::constant_val_dup(cv_t),
                                            ctors,
                                            n_p,
                                            n_idx,
                                            cv_r: q.1,
                                            elim: name::anonymous(),
                                            res_sort: s,
                                            rhss,
                                            large: false,
                                            is_prop,
                                        }),
                                    }
                                } else {
                                    None
                                }
                            }
                        }
                    }
                    None => None,
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:631-652 nativeParts?
/// Recognise a direct block — ONE ROUTE: its SHAPE (`nativeShape?`); the
/// fields' kinds are a PLACEHOLDER the install fills (`NativeParts.withKinds`)
/// after normalising every field domain by official's positivity walk.  A
/// **mutual or nested** block is never this route's: its export carries
/// several type formers, resp. several recursors, and `sumSplit` — one
/// former, one recursor — refuses both shapes outright.
pub fn native_parts(n_pd: u64, block: &Vec<ConstantInfo>) -> Option<NativeParts> {
    match native_shape(n_pd, block) {
        Some(p) => {
            let pinned = native_rec_pin_ok(&p, block);
            Some(NativeParts {
                shape: p,
                kinds: Vec::new(),
                rec_pinned: pinned,
            })
        }
        None => None,
    }
}
