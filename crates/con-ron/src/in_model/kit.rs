//! `ConLeche/Frontend/InModel/Kit.lean` — the in-process modeller's kit:
//! the naming scheme, telescope helpers over `Expr`, the family rewrite
//! `spec_fam`, the kernel-shape recursor of an indexed recursive family with
//! inductive hypotheses — the direct fixpoint route's own generators
//! (`native_parts::struct_rec_ty_r`/`struct_rec_rhs_r`), which read a
//! recursive field's own `∀`-telescope off the constructor, so a REFLEXIVE
//! field `f : ∀ a⃗, T p⃗ e⃗(a⃗)` gets the hypothesis `∀ a⃗, motive e⃗(a⃗) (f a⃗)`
//! and the rule passes `λ a⃗, T.rec … e⃗(a⃗) (f a⃗)` — a syntactic sort
//! inferer, and definitional heights.
//!
//! Three deviations, all of them local:
//!
//! 1. **`ConstTable` and the height table are `&dyn Fn`**, where con-leche's
//!    `Ctx` carries `Name → Option (List Name × Expr)` and `Name → Nat`
//!    directly.  The generators build *overlays* over them (`tbl'` adds the
//!    block's own generated types, `hOf` the heights of the definitions
//!    emitted so far), which is what a Lean function argument makes free; a
//!    trait object is the Rust spelling of the same thing, and this crate is
//!    outside DESIGN.md §3.4's Aeneas subset.
//! 2. **Every memo is keyed by the node's ADDRESS** (`ExprKey`), where
//!    con-leche's `Std.HashMap Expr _` keys by VALUE.  A memo entry is a
//!    function of the node, so an address key is a strictly coarser dedupe of
//!    the same answers — and it keeps `expr::beq` off the probe path, which
//!    task #37 measured as exponential on `tests/e2e/tower_beqpair.ndjson`.
//!    `nat_op_ground::ExprKey` carries the same argument for the same reason.
//! 3. **Nat subtraction is `saturating_sub`**, Lean's truncated `Nat`
//!    subtraction: `nF - 1 - i`, `M - 1 - m`, `args.length - nIdx` and their
//!    like are spelled with `sub` throughout, so an out-of-range index gives
//!    con-leche's `0` rather than a Rust underflow.

use std::collections::HashMap;

use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::env::ReducibilityHint;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Expr, ExprView, Literal};
use con_ron_core::kernel::expr_ops;
use con_ron_core::kernel::expr_ops::NameToName;
use con_ron_core::kernel::inductives::native_parts;
use con_ron_core::kernel::inductives::struct_parts;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::{Level, LevelKind};
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::{Name, NameKind};
use con_ron_core::kernel::prop_when;

use crate::keys::ExprKey;

/// con-leche: none — Lean's truncated `Nat` subtraction, which Rust's `u64`
/// does not have.  Every `a - b` of the cited Lean is spelled with this.
pub fn sub(a: u64, b: u64) -> u64 {
    a.saturating_sub(b)
}

/// con-leche: none — `Name.str` at a Rust `&str`; con-leche writes `n.str "s"`
/// and the code-point vector is Lean's string literal.
pub fn nstr(pre: Name, s: &str) -> Name {
    name::mk_str(pre, s.chars().map(|c| c as u32).collect())
}

/// con-leche: none — the `f : Name → Name` argument of `Expr.renameConsts` as
/// core's `NameToName` dictionary (task #9's pattern 1), wrapping a closure
/// because this crate is outside §3.4's Aeneas subset.
pub struct RenameFn<F: Fn(&Name) -> Name>(pub F);

/// con-leche: none — the one method of `RenameFn`.
impl<F: Fn(&Name) -> Name> NameToName for RenameFn<F> {
    /// con-leche: none — the `f` of `renameConsts f`.
    fn rename(&self, n: &Name) -> Name {
        (self.0)(n)
    }
}

/// con-leche: none — `lps.map .param`, the level arguments of a constant at
/// the block's own level parameters.
pub fn params_of(lps: &[Name]) -> Vec<Level> {
    lps.iter().map(|n| level::param(name::dup(n))).collect()
}

/// con-leche: none — `us == lps.map .param` without building the list.
pub fn levels_are_params(us: &[Level], lps: &[Name]) -> bool {
    us.len() == lps.len()
        && us.iter().zip(lps.iter()).all(|(u, n)| match &u.0.kind {
            LevelKind::Param(p) => name::beq(p, n),
            _ => false,
        })
}

/// con-leche: none — `es.getD i default` at `default : Expr = .bvar 0`
/// (`env::default_expr`), the out-of-range guard the cited Lean spells with
/// `getD`.
pub fn get_d(es: &[Expr], i: u64) -> Expr {
    match es.get(i as usize) {
        Some(e) => expr::dup(e),
        None => expr::bvar(0),
    }
}

/// con-leche: none — `xs.map (·.liftLooseBVars n 0)` over a slice.
pub fn lift_all_n(n: u64, es: &[Expr]) -> Vec<Expr> {
    es.iter()
        .map(|e| expr_ops::lift_loose_bvars(n, 0, e))
        .collect()
}

/// con-leche: none — `es₁ ++ es₂` over a `Vec` and a slice of `Expr`.
pub fn app2(a: Vec<Expr>, b: &[Expr]) -> Vec<Expr> {
    let mut out = a;
    for e in b {
        out.push(expr::dup(e));
    }
    out
}

/// con-leche: none — `es.map expr::dup`, a slice's element-wise copy (`Expr`
/// is deliberately not `Clone`, task #10's note).
pub fn dup_all(es: &[Expr]) -> Vec<Expr> {
    es.iter().map(expr::dup).collect()
}

/// con-leche: none — `ns.map name::dup`, a `Name` slice's element-wise copy.
pub fn dup_names(ns: &[Name]) -> Vec<Name> {
    ns.iter().map(name::dup).collect()
}

// ---------------------------------------------------------------------------
// Names (`Kit.lean:42-81`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:49-50 implName
/// `T._model._impl.<s>`.
pub fn impl_name(t: &Name, s: &str) -> Name {
    nstr(nstr(nstr(name::dup(t), "_model"), "_impl"), s)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:52-53 tagName
/// The tag family `T._model._impl.tag` of the block owned by `T`.
pub fn tag_name(t: &Name) -> Name {
    impl_name(t, "tag")
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:55-56 tagCtorName
/// The tag constructor of member `k`: `T._model._impl.tag.k`.
pub fn tag_ctor_name(t: &Name, k: u64) -> Name {
    name::mk_num(tag_name(t), k)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:58-59 auxName
/// The auxiliary family `T._model._impl.aux`.
pub fn aux_name(t: &Name) -> Name {
    impl_name(t, "aux")
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:61-67 auxCtorName
/// The auxiliary constructor of member `k`'s constructor `C`:
/// `T._model._impl.aux.k.<last component of C>`.
pub fn aux_ctor_name(t: &Name, k: u64, c: &Name) -> Name {
    let head = name::mk_num(aux_name(t), k);
    match &c.0.kind {
        NameKind::Str(_, s) => name::mk_str(head, expr::str_copy(s)),
        NameKind::Num(_, n) => name::mk_num(head, *n),
        NameKind::Anonymous => head,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:69-70 modelName
/// The model companion of a block member: `X._model`.
pub fn model_name(n: &Name) -> Name {
    nstr(name::dup(n), "_model")
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:72-74 iotaName
/// The iota theorem of rule `j` of a modeled recursor `R`: `R._model.iota_j`.
pub fn iota_name(r: &Name, j: u64) -> Name {
    nstr(model_name(r), &format!("iota_{}", j))
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:76-86 freshLevelName
/// A level-parameter name not among `lps`: `u`, then `u_1`, `u_2`, … — the
/// official kernel's `mk_fresh_lvl_name` convention for a recursor's
/// elimination level, so a generated recursor's level parameters are the ones
/// Lean's own kernel would mint for the same block.  The cited `where go`
/// recursion is the loop.
pub fn fresh_level_name(lps: &[Name]) -> Name {
    let n0 = nstr(name::anonymous(), "u");
    if !lps.iter().any(|x| name::beq(x, &n0)) {
        return n0;
    }
    let mut i: u64 = 1;
    loop {
        let n = nstr(name::anonymous(), &format!("u_{}", i));
        if !lps.iter().any(|x| name::beq(x, &n)) {
            return n;
        }
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// Binders and frames (`Kit.lean:83-122`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:90-93 bm
/// The default binder datum of a generated binder: `.never` — what the
/// frontend gives every parsed binder (the annotate pass recomputes the datum
/// before it is validated).
pub fn bm() -> BinderMeta {
    expr::binder_meta(prop_when::never())
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:95-97 mkLams
/// `λ`-telescope over domains (outermost first).
pub fn mk_lams(bs: &[Expr], body: Expr) -> Expr {
    let mut acc = body;
    for d in bs.iter().rev() {
        acc = expr::lam(expr::dup(d), acc, bm());
    }
    acc
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:99-101 mkPis
/// `∀`-telescope over domains (outermost first).
pub fn mk_pis(bs: &[Expr], body: Expr) -> Expr {
    let mut acc = body;
    for d in bs.iter().rev() {
        acc = expr::forall_e(expr::dup(d), acc, bm());
    }
    acc
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:103-105 varsAt
/// The variables `bvar (o + n - 1 - k)`, `k < n`: a telescope of `n` binders
/// seen from `o` binders below it (`structPsAt`).
pub fn vars_at(o: u64, n: u64) -> Vec<Expr> {
    struct_parts::struct_ps_at(o, n)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:107-108 constP
/// A constant at its level parameters.
pub fn const_p(n: &Name, lps: &[Name]) -> Expr {
    expr::mk_const(name::dup(n), params_of(lps))
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:110-112 piBinders
/// The domains of a `∀`-telescope's binder list.
pub fn pi_binders(bs: &[(Expr, BinderMeta)]) -> Vec<Expr> {
    bs.iter().map(|b| expr::dup(&b.0)).collect()
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:114-127 overFirstParams
/// A member's or constructor's telescope `ty` re-spelled over the FIRST
/// member's parameter binders: the first `nP` binders of `former` with `ty`'s
/// residual after its own `nP` parameter binders under them.  The re-spelling
/// is checked, not trusted: the fold's typing of the generated record is what
/// compares the domains.
pub fn over_first_params(n_p: u64, former: &Expr, ty: &Expr) -> Option<Expr> {
    let (_, q) = expr_ops::strip_pis(n_p, ty)?;
    expr_ops::replace_pi_body(n_p, former, &q)
}

// ---------------------------------------------------------------------------
// Family occurrences (`Kit.lean:124-270`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:133-204 specFamGo
/// Rewrite every occurrence `T_m a⃗` (exactly `nP + nIdx_m` arguments) of a
/// member of the block into `aux a⃗_P (tag.m a⃗_P a⃗_I)`.  `members` lists
/// `(T_m, m, nIdx_m)`.  An occurrence with any other arity is left alone (the
/// caller's field classification rejects such blocks).  One memoized DAG walk
/// (keyed by the node — the rewrite reads no binder cursor); without it the
/// rebuild runs once per path, which `tests/e2e/tower_mutual.ndjson` exposes.
pub fn spec_fam_go(
    t: &Name,
    lps: &[Name],
    n_p: u64,
    members: &[(Name, u64, u64)],
    memo: &mut HashMap<ExprKey, Expr>,
    e: &Expr,
) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(_) | ExprView::Sort(_) | ExprView::Fvar(_, _) | ExprView::Lit(_) => {
            expr::dup(e)
        }
        ExprView::Const(n, us) => match members.iter().find(|m| name::beq(&m.0, n)) {
            Some((_, m, n_idx)) => {
                if n_p + n_idx == 0 && levels_are_params(us, lps) {
                    expr_ops::mk_app_n(
                        const_p(&aux_name(t), lps),
                        &vec![const_p(&tag_ctor_name(t, *m), lps)],
                    )
                } else {
                    expr::dup(e)
                }
            }
            None => expr::dup(e),
        },
        _ => {
            if let Some(r) = memo.get(&ExprKey(expr::dup(e))) {
                return expr::dup(r);
            }
            let r = spec_fam_arm(t, lps, n_p, members, memo, e);
            memo.insert(ExprKey(expr::dup(e)), expr::dup(&r));
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:133-204 specFamGo
/// The compound arm of `spec_fam_go`, i.e. the body the memo wraps.
pub fn spec_fam_arm(
    t: &Name,
    lps: &[Name],
    n_p: u64,
    members: &[(Name, u64, u64)],
    memo: &mut HashMap<ExprKey, Expr>,
    e: &Expr,
) -> Expr {
    match expr::view(&e) {
        ExprView::App(_, _) => {
            let f = expr_ops::get_app_fn(e);
            let args = expr_ops::get_app_args(e);
            match expr::view(&f) {
                ExprView::Const(n, us) => match members.iter().find(|m| name::beq(&m.0, n)) {
                    Some((_, m, n_idx)) => {
                        if args.len() as u64 == n_p + n_idx && levels_are_params(us, lps) {
                            let cut = (n_p as usize).min(args.len());
                            let ps = spec_fam_go_list(t, lps, n_p, members, memo, &args[..cut]);
                            let is = spec_fam_go_list(t, lps, n_p, members, memo, &args[cut..]);
                            let tag_app = expr_ops::mk_app_n(
                                const_p(&tag_ctor_name(t, *m), lps),
                                &app2(dup_all(&ps), &is),
                            );
                            expr_ops::mk_app_n(
                                const_p(&aux_name(t), lps),
                                &app2(ps, &[tag_app]),
                            )
                        } else {
                            let f2 = spec_fam_go(t, lps, n_p, members, memo, &f);
                            let ar = spec_fam_go_list(t, lps, n_p, members, memo, &args);
                            expr_ops::mk_app_n(f2, &ar)
                        }
                    }
                    None => {
                        let ar = spec_fam_go_list(t, lps, n_p, members, memo, &args);
                        expr_ops::mk_app_n(f, &ar)
                    }
                },
                _ => {
                    let f2 = spec_fam_go(t, lps, n_p, members, memo, &f);
                    let ar = spec_fam_go_list(t, lps, n_p, members, memo, &args);
                    expr_ops::mk_app_n(f2, &ar)
                }
            }
        }
        ExprView::Lam(d, b, m) => {
            let d2 = spec_fam_go(t, lps, n_p, members, memo, d);
            let b2 = spec_fam_go(t, lps, n_p, members, memo, b);
            expr::lam(d2, b2, expr::binder_meta_dup(m))
        }
        ExprView::ForallE(d, b, m) => {
            let d2 = spec_fam_go(t, lps, n_p, members, memo, d);
            let b2 = spec_fam_go(t, lps, n_p, members, memo, b);
            expr::forall_e(d2, b2, expr::binder_meta_dup(m))
        }
        ExprView::LetE(ty, v, b) => {
            let ty2 = spec_fam_go(t, lps, n_p, members, memo, ty);
            let v2 = spec_fam_go(t, lps, n_p, members, memo, v);
            let b2 = spec_fam_go(t, lps, n_p, members, memo, b);
            expr::let_e(ty2, v2, b2)
        }
        ExprView::Proj(s, i, x) => {
            let x2 = spec_fam_go(t, lps, n_p, members, memo, x);
            expr::proj(name::dup(s), *i, x2)
        }
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:206-214 specFamGoList
/// `spec_fam_go` over a list, threading the memo.
pub fn spec_fam_go_list(
    t: &Name,
    lps: &[Name],
    n_p: u64,
    members: &[(Name, u64, u64)],
    memo: &mut HashMap<ExprKey, Expr>,
    es: &[Expr],
) -> Vec<Expr> {
    es.iter()
        .map(|e| spec_fam_go(t, lps, n_p, members, memo, e))
        .collect()
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:218-221 specFam
/// `spec_fam_go` at a fresh memo.
pub fn spec_fam(t: &Name, lps: &[Name], n_p: u64, members: &[(Name, u64, u64)], e: &Expr) -> Expr {
    let mut memo: HashMap<ExprKey, Expr> = HashMap::new();
    spec_fam_go(t, lps, n_p, members, &mut memo, e)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:223-275 substParams
/// Simultaneous substitution of a parameter block: under `d` binders,
/// `bvar (d + j)` (`j < n`, innermost first) becomes `vals[n - 1 - j]`
/// (`vals` outermost first, spelled at the frame `d` binders below the
/// block's, lifted past the binders passed on the way), and every loose
/// `bvar ≥ d + n` is lowered by `n`.  Unlike `instantiateList` the
/// replacements are never re-traversed, so they may mention variables of the
/// surrounding frame.
pub fn subst_params(d: u64, n: u64, vals: &[Expr], e: &Expr) -> Expr {
    let mut memo: HashMap<(ExprKey, u64), Expr> = HashMap::new();
    subst_params_go(d, n, vals, &mut memo, 0, e)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:223-275 substParams
/// The memoized rebuild behind `subst_params`, keyed by the node and the
/// binder cursor `k` (which shifts under binders).  As everywhere in the
/// modeller, no spec lemma: it is untrusted, and what it emits is checked.
pub fn subst_params_go(
    d: u64,
    n: u64,
    vals: &[Expr],
    memo: &mut HashMap<(ExprKey, u64), Expr>,
    k: u64,
    e: &Expr,
) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(i) => {
            if *i < d + k {
                expr::bvar(*i)
            } else if *i < d + k + n {
                expr_ops::lift_loose_bvars(k, 0, &get_d(vals, sub(sub(n, 1), sub(sub(*i, d), k))))
            } else {
                expr::bvar(sub(*i, n))
            }
        }
        ExprView::Sort(u) => expr::sort(level::dup(u)),
        ExprView::Const(nm, us) => {
            expr::mk_const(name::dup(nm), us.iter().map(level::dup).collect())
        }
        ExprView::Lit(l) => expr::lit(expr::literal_dup(l)),
        _ => {
            let key = (ExprKey(expr::dup(e)), k);
            if let Some(r) = memo.get(&key) {
                return expr::dup(r);
            }
            let r = match expr::view(&e) {
                ExprView::App(f, a) => {
                    let f2 = subst_params_go(d, n, vals, memo, k, f);
                    let a2 = subst_params_go(d, n, vals, memo, k, a);
                    expr::app(f2, a2)
                }
                ExprView::Lam(ty, b, m) => {
                    let t2 = subst_params_go(d, n, vals, memo, k, ty);
                    let b2 = subst_params_go(d, n, vals, memo, k + 1, b);
                    expr::lam(t2, b2, expr::binder_meta_dup(m))
                }
                ExprView::ForallE(ty, b, m) => {
                    let t2 = subst_params_go(d, n, vals, memo, k, ty);
                    let b2 = subst_params_go(d, n, vals, memo, k + 1, b);
                    expr::forall_e(t2, b2, expr::binder_meta_dup(m))
                }
                ExprView::LetE(ty, v, b) => {
                    let t2 = subst_params_go(d, n, vals, memo, k, ty);
                    let v2 = subst_params_go(d, n, vals, memo, k, v);
                    let b2 = subst_params_go(d, n, vals, memo, k + 1, b);
                    expr::let_e(t2, v2, b2)
                }
                ExprView::Proj(s, i, x) => {
                    let x2 = subst_params_go(d, n, vals, memo, k, x);
                    expr::proj(name::dup(s), *i, x2)
                }
                ExprView::Fvar(i, ty) => {
                    let t2 = subst_params_go(d, n, vals, memo, k, ty);
                    expr::fvar(*i, t2)
                }
                _ => expr::dup(e),
            };
            memo.insert(key, expr::dup(&r));
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:277-320 mentionsAnyGo
/// Does `e` mention any of the names?  One memoized DAG walk: the answer at a
/// node is a function of the node and `ns`, and `ns` is fixed for the walk, so
/// the memo is keyed by the node alone and dropped after each call.  No spec
/// lemma, and none is owed: the modeller is untrusted.
pub fn mentions_any_go(ns: &[Name], memo: &mut HashMap<ExprKey, bool>, e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Bvar(_) | ExprView::Sort(_) | ExprView::Lit(_) => false,
        ExprView::Const(n, _) => ns.iter().any(|m| name::beq(m, n)),
        _ => {
            if let Some(r) = memo.get(&ExprKey(expr::dup(e))) {
                return *r;
            }
            let r = match expr::view(&e) {
                ExprView::Fvar(_, ty) => mentions_any_go(ns, memo, ty),
                ExprView::App(f, a) => {
                    mentions_any_go(ns, memo, f) || mentions_any_go(ns, memo, a)
                }
                ExprView::Lam(ty, b, _) | ExprView::ForallE(ty, b, _) => {
                    mentions_any_go(ns, memo, ty) || mentions_any_go(ns, memo, b)
                }
                ExprView::LetE(ty, v, b) => {
                    mentions_any_go(ns, memo, ty)
                        || mentions_any_go(ns, memo, v)
                        || mentions_any_go(ns, memo, b)
                }
                ExprView::Proj(s, _, x) => {
                    if ns.iter().any(|m| name::beq(m, s)) {
                        true
                    } else {
                        mentions_any_go(ns, memo, x)
                    }
                }
                _ => false,
            };
            memo.insert(ExprKey(expr::dup(e)), r);
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:322-323 mentionsAny
/// `mentions_any_go` at a fresh memo.
pub fn mentions_any(ns: &[Name], e: &Expr) -> bool {
    let mut memo: HashMap<ExprKey, bool> = HashMap::new();
    mentions_any_go(ns, &mut memo, e)
}

// ---------------------------------------------------------------------------
// The kernel-shape recursor of an indexed recursive family (`Kit.lean:325-356`)
// ---------------------------------------------------------------------------

/// con-leche: none — a constructor of a generated family as the cited Lean's
/// `List (Name × Nat × Expr × List Nat)` entry: name, field count, type, the
/// recursive field positions (ascending).  A named struct instead of a
/// four-component Lean tuple read as `·.2.2.2` (`proj_rec`'s deviation 3).
pub struct KCtor {
    pub name: Name,
    pub n_f: u64,
    pub ty: Expr,
    pub rec_idx: Vec<u64>,
}

/// con-leche: none — the other half of `KCtor`'s deviation: the core's
/// generators take the cited four-component tuples, so the list is handed
/// back in that shape at the two call sites below.
pub fn ctor_tuples(ctors: &[KCtor]) -> Vec<(Name, u64, Expr, Vec<u64>)> {
    let mut out: Vec<(Name, u64, Expr, Vec<u64>)> = Vec::new();
    for c in ctors.iter() {
        out.push((
            name::dup(&c.name),
            c.n_f,
            expr::dup(&c.ty),
            c.rec_idx.to_vec(),
        ));
    }
    out
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:341-344 recTy
/// **The recursor type** of a recursive family — the direct fixpoint route's
/// own generator `native_parts::struct_rec_ty_r`, not a private copy:
///
/// ```text
/// ∀ p⃗ {motive : ∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ}
///   (minor_C : ∀ f⃗ (ih⃗ : ∀ a⃗, motive e⃗_i(a⃗) (f_i a⃗))…, motive e⃗_C (C p⃗ f⃗))…
///   ı⃗ (t : T p⃗ ı⃗), motive ı⃗ t
/// ```
///
/// over the former's type `tty = ∀ p⃗ ı⃗, Sort w`.  Each `ih` runs over the
/// recursive field's OWN `∀`-telescope `a⃗` (empty at a finitary field, where
/// it is the old `motive e⃗_i f_i`), its index expressions read off the
/// domain `∀ a⃗, T p⃗ e⃗_i(a⃗)` — which is what a REFLEXIVE field needs, and
/// what the private copy this replaced could not spell.  The route
/// regenerates the auxiliary family's recursor and compares it against
/// exactly these generators by one `isDefEq`, so emitting their output makes
/// that comparison hold by construction.
pub fn rec_ty(
    t: &Name,
    lps: &[Name],
    elim: &Name,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &Expr,
    ctors: &[KCtor],
) -> Option<Expr> {
    native_parts::struct_rec_ty_r(
        t,
        &dup_names(lps),
        elim,
        large,
        n_p,
        n_idx,
        tty,
        &ctor_tuples(ctors),
    )
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:346-356 recRhs
/// **The rule** of constructor `j`:
/// `λ p⃗ motive m⃗ f⃗, minor_j f⃗ (λ a⃗, T.rec p⃗ motive m⃗ e⃗_i(a⃗) (f_i a⃗))…`
/// (`native_parts::struct_rec_rhs_r`; `rec_c`, `rlvls`: the recursor's name
/// and its level parameters as levels), at the parse placeholder's binder
/// data throughout (`expr_ops::reset_meta`): the route compares a stream
/// rule's body SYNTACTICALLY with the generator's output reset to the
/// placeholder, as a parsed stream carries it everywhere — and a reflexive
/// hypothesis `λ a⃗, T.rec … (f a⃗)` is where a generated body has binders of
/// its own.
pub fn rec_rhs(
    t: &Name,
    lps: &[Name],
    elim: &Name,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &Expr,
    ctors: &[KCtor],
    rec_c: &Name,
    rlvls: &[Level],
    j: u64,
) -> Option<Expr> {
    let rhs = native_parts::struct_rec_rhs_r(
        t,
        &dup_names(lps),
        elim,
        large,
        n_p,
        n_idx,
        tty,
        &ctor_tuples(ctors),
        rec_c,
        &rlvls.iter().map(level::dup).collect(),
        j,
    )?;
    Some(expr_ops::reset_meta(&rhs))
}

// ---------------------------------------------------------------------------
// A syntactic sort inferer (`Kit.lean:358-471`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:368-369 ConstTable
/// The declared type of a constant: its level parameters and type.  A trait
/// object where con-leche has a `Name → Option (List Name × Expr)` (the module
/// note's deviation 1).
pub type ConstTable<'a> = &'a dyn Fn(&Name) -> Option<(Vec<Name>, Expr)>;

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:371-377 betaHead
/// Head β-reduction only.
pub fn beta_head(e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::App(f, a) => {
            let f2 = beta_head(f);
            match expr::view(&f2) {
                ExprView::Lam(_, b, _) => beta_head(&expr_ops::instantiate1(b, a, 0)),
                _ => expr::app(f2, expr::dup(a)),
            }
        }
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:379-404 inferTy
/// `infer_ty tbl ctx e` computes the type of `e` from the declared types of
/// the constants it mentions (`tbl`) and the binder domains of the context
/// (`ctx`, innermost first, each spelled at its own frame), β-reducing only
/// what instantiating a `∀` produces.  No `whnf`, no definitional unfolding:
/// an application whose function type is not syntactically a `∀` after
/// instantiation fails.
pub fn infer_ty(tbl: ConstTable, ctx: &[Expr], e: &Expr) -> Option<Expr> {
    match expr::view(&e) {
        ExprView::Bvar(i) => ctx
            .get(*i as usize)
            .map(|d| expr_ops::lift_loose_bvars(*i + 1, 0, d)),
        ExprView::Sort(u) => Some(expr::sort(level::succ(level::dup(u)))),
        ExprView::Const(n, us) => {
            let (lps, ty) = tbl(n)?;
            if lps.len() == us.len() {
                Some(expr_ops::instantiate_level_params(
                    &lps,
                    &us.iter().map(level::dup).collect(),
                    &ty,
                ))
            } else {
                None
            }
        }
        ExprView::App(f, a) => {
            let ft = infer_ty(tbl, ctx, f)?;
            match expr::view(&beta_head(&ft)) {
                ExprView::ForallE(_, b, _) => Some(expr_ops::instantiate1(b, a, 0)),
                _ => None,
            }
        }
        ExprView::Lam(d, b, m) => {
            let bt = infer_ty(tbl, &cons_ctx(d, ctx), b)?;
            Some(expr::forall_e(expr::dup(d), bt, expr::binder_meta_dup(m)))
        }
        ExprView::ForallE(d, b, _) => {
            let u = sort_of(tbl, ctx, d)?;
            let v = sort_of(tbl, &cons_ctx(d, ctx), b)?;
            Some(expr::sort(level::imax(u, v)))
        }
        ExprView::LetE(_, v, b) => infer_ty(tbl, ctx, &expr_ops::instantiate1(b, v, 0)),
        ExprView::Lit(Literal::NatVal(_)) => Some(expr::mk_const(bnm::nat_name(), Vec::new())),
        ExprView::Lit(Literal::StrVal(_)) => {
            Some(expr::mk_const(bnm::string_name(), Vec::new()))
        }
        _ => None,
    }
}

/// con-leche: none — `d :: ctx`, the inferer's context extension (Lean's list
/// cons is sharing; a Rust `Vec` is copied).
pub fn cons_ctx(d: &Expr, ctx: &[Expr]) -> Vec<Expr> {
    let mut out: Vec<Expr> = Vec::with_capacity(ctx.len() + 1);
    out.push(expr::dup(d));
    for x in ctx {
        out.push(expr::dup(x));
    }
    out
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:406-408 sortOf
/// The sort of a type at a context.  `inferTy`'s own `where`-clause
/// `sortOf` (`Kit.lean:484-490`, inside `inferTy`'s cited block) is this same
/// function: the public wrapper there just calls it, and the two are one here.
pub fn sort_of(tbl: ConstTable, ctx: &[Expr], e: &Expr) -> Option<Level> {
    let t = infer_ty(tbl, ctx, e)?;
    match expr::view(&beta_head(&t)) {
        ExprView::Sort(u) => Some(level::dup(u)),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:448-465 sortCeil
/// A level at least the sort of `d` (the cited section header's four cases).
/// Nothing here is trusted: a ceiling for an ill-sorted domain is a level like
/// any other, and the tag family the modeller then emits fails the fold's own
/// type check.  `fuel` bounds the walk — up the type tower and down a `∀`
/// telescope — and only keeps the function total.
pub fn sort_ceil(tbl: ConstTable, fuel: u64, ctx: &[Expr], d: &Expr) -> Option<Level> {
    if fuel == 0 {
        return None;
    }
    match infer_ty(tbl, ctx, d) {
        Some(t) => {
            let t2 = beta_head(&t);
            match expr::view(&t2) {
                ExprView::Sort(u) => Some(level::dup(u)),
                _ => sort_ceil(tbl, fuel - 1, ctx, &t2),
            }
        }
        None => {
            let d2 = beta_head(d);
            match expr::view(&d2) {
                ExprView::ForallE(dom, body, _) => {
                    let a = sort_ceil(tbl, fuel - 1, ctx, dom)?;
                    let b = sort_ceil(tbl, fuel - 1, &cons_ctx(dom, ctx), body)?;
                    Some(level::max(a, b))
                }
                ExprView::LetE(_, v, b) => {
                    sort_ceil(tbl, fuel - 1, ctx, &expr_ops::instantiate1(b, v, 0))
                }
                _ => {
                    let f = infer_ty(tbl, ctx, &expr_ops::get_app_fn(&d2))?;
                    sort_ceil(tbl, fuel - 1, ctx, &f)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:467-471 idxSort
/// A ceiling for the sort of an index domain at a context (`sort_ceil`), at a
/// fuel no `∀` telescope or type tower of a real stream reaches.
pub fn idx_sort(tbl: ConstTable, ctx: &[Expr], e: &Expr) -> Option<Level> {
    sort_ceil(tbl, 128, ctx, e)
}

// ---------------------------------------------------------------------------
// Definitional heights (`Kit.lean:473-527`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:475-510 maxHeightGo
/// The highest definitional height of a constant mentioned by `e` (`heights`:
/// the height of every definition declared so far; `0` for anything else).
/// One memoized DAG walk, keyed by the node — and, like `mentionsAnyGo`, with
/// no spec lemma, since the modeller is untrusted and the hint it computes is
/// checked with the declaration it rides on.
pub fn max_height_go(
    heights: &dyn Fn(&Name) -> u64,
    memo: &mut HashMap<ExprKey, u64>,
    e: &Expr,
) -> u64 {
    match expr::view(&e) {
        ExprView::Const(n, _) => heights(n),
        ExprView::Bvar(_) | ExprView::Sort(_) | ExprView::Lit(_) => 0,
        _ => {
            if let Some(r) = memo.get(&ExprKey(expr::dup(e))) {
                return *r;
            }
            let r = match expr::view(&e) {
                ExprView::Fvar(_, ty) => max_height_go(heights, memo, ty),
                ExprView::App(f, a) => {
                    let rf = max_height_go(heights, memo, f);
                    let ra = max_height_go(heights, memo, a);
                    rf.max(ra)
                }
                ExprView::Lam(ty, b, _) | ExprView::ForallE(ty, b, _) => {
                    let rt = max_height_go(heights, memo, ty);
                    let rb = max_height_go(heights, memo, b);
                    rt.max(rb)
                }
                ExprView::LetE(ty, v, b) => {
                    let rt = max_height_go(heights, memo, ty);
                    let rv = max_height_go(heights, memo, v);
                    let rb = max_height_go(heights, memo, b);
                    rt.max(rv.max(rb))
                }
                ExprView::Proj(_, _, x) => max_height_go(heights, memo, x),
                _ => 0,
            };
            memo.insert(ExprKey(expr::dup(e)), r);
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:512-514 maxHeight
/// `max_height_go` at a fresh memo.
pub fn max_height(heights: &dyn Fn(&Name) -> u64, e: &Expr) -> u64 {
    let mut memo: HashMap<ExprKey, u64> = HashMap::new();
    max_height_go(heights, &mut memo, e)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:516-520 hintFor
/// The reducibility hint of a generated definition: one above the highest
/// constant its value mentions (the kernel's `getMaxHeight` rule).
pub fn hint_for(heights: &dyn Fn(&Name) -> u64, value: &Expr) -> ReducibilityHint {
    ReducibilityHint::Regular(max_height(heights, value) + 1)
}

/// con-leche: ConLeche/Frontend/InModel/Kit.lean:522-525 hintHeight
/// The height a hint records.
pub fn hint_height(h: &ReducibilityHint) -> u64 {
    match h {
        ReducibilityHint::Regular(n) => *n,
        _ => 0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::render::name_str;

    fn n(s: &str) -> Name {
        nstr(name::anonymous(), s)
    }

    /// The naming scheme is lean-inductive-models' `_impl` scheme, component
    /// for component: none of these names is special to the checker (only the
    /// public `_model` slots are consumed), but the two generators' streams
    /// have to be diffable.
    #[test]
    fn the_naming_scheme_is_the_impl_one() {
        let t = nstr(n("Lean"), "Syntax");
        assert_eq!(name_str(&tag_name(&t)), "Lean.Syntax._model._impl.tag");
        assert_eq!(name_str(&tag_ctor_name(&t, 3)), "Lean.Syntax._model._impl.tag.3");
        assert_eq!(name_str(&aux_name(&t)), "Lean.Syntax._model._impl.aux");
        assert_eq!(
            name_str(&aux_ctor_name(&t, 2, &nstr(n("List"), "cons"))),
            "Lean.Syntax._model._impl.aux.2.cons"
        );
        assert_eq!(name_str(&model_name(&t)), "Lean.Syntax._model");
        assert_eq!(
            name_str(&iota_name(&nstr(t, "rec"), 1)),
            "Lean.Syntax.rec._model.iota_1"
        );
        assert_eq!(name_str(&impl_name(&n("T"), "pack_0")), "T._model._impl.pack_0");
    }

    /// A `.num` last component keeps its number and an anonymous constructor
    /// keeps neither: the three arms of `auxCtorName`.
    #[test]
    fn aux_ctor_name_follows_the_last_component() {
        let t = n("T");
        assert_eq!(
            name_str(&aux_ctor_name(&t, 0, &name::mk_num(n("C"), 7))),
            "T._model._impl.aux.0.7"
        );
        assert_eq!(
            name_str(&aux_ctor_name(&t, 1, &name::anonymous())),
            "T._model._impl.aux.1"
        );
    }

    /// `freshLevelName` is the official kernel's `mk_fresh_lvl_name`
    /// convention: `u`, then `u_1`, `u_2`, …
    #[test]
    fn fresh_level_name_walks_the_kernel_convention() {
        assert_eq!(name_str(&fresh_level_name(&[])), "u");
        assert_eq!(name_str(&fresh_level_name(&[n("v")])), "u");
        assert_eq!(name_str(&fresh_level_name(&[n("u")])), "u_1");
        assert_eq!(
            name_str(&fresh_level_name(&[n("u"), n("u_1"), n("u_2")])),
            "u_3"
        );
    }

    /// `substParams d n vals` replaces the parameter block innermost-first
    /// and lowers everything above it, and unlike `instantiateList` never
    /// re-traverses a replacement.
    #[test]
    fn subst_params_replaces_a_block_and_lowers_above_it() {
        // `d = 0`, `n = 2`, `vals = [A, B]` (outermost first), so `bvar 1` is
        // the outer parameter (A) and `bvar 0` the inner (B); `bvar 2` is
        // above the block and drops by 2.
        let a = expr::mk_const(n("A"), Vec::new());
        let b = expr::mk_const(n("B"), Vec::new());
        let vals = vec![expr::dup(&a), expr::dup(&b)];
        let e = expr_ops::mk_app_n(
            expr::bvar(2),
            &vec![expr::bvar(1), expr::bvar(0), expr::bvar(5)],
        );
        let got = subst_params(0, 2, &vals, &e);
        let want = expr_ops::mk_app_n(
            expr::bvar(0),
            &vec![a, b, expr::bvar(3)],
        );
        assert!(expr::beq(&got, &want));
        // under one binder the cursor shifts: `bvar 1` there is the block's
        // INNERMOST parameter, i.e. `vals[n - 1] = B`, and the replacement is
        // lifted past the binder passed on the way (it is closed here)
        let under = expr::lam(expr::sort(level::zero()), expr::bvar(1), bm());
        let got = subst_params(0, 2, &vals, &under);
        let want = expr::lam(
            expr::sort(level::zero()),
            expr::mk_const(n("B"), Vec::new()),
            bm(),
        );
        assert!(expr::beq(&got, &want));
    }

    /// `specFam` rewrites a whole member application at the parameters into
    /// the auxiliary family at the member's tag, and leaves an occurrence of
    /// the wrong arity alone (the caller's field classification rejects such
    /// blocks).
    #[test]
    fn spec_fam_rewrites_whole_member_occurrences_only() {
        let t = n("T");
        let u = n("U");
        // a two-member index-free block with no parameters
        let members = vec![(name::dup(&t), 0u64, 0u64), (name::dup(&u), 1u64, 0u64)];
        let occ = expr::mk_const(name::dup(&u), Vec::new());
        let got = spec_fam(&t, &[], 0, &members, &occ);
        let want = expr_ops::mk_app_n(
            expr::mk_const(aux_name(&t), Vec::new()),
            &vec![expr::mk_const(tag_ctor_name(&t, 1), Vec::new())],
        );
        assert!(expr::beq(&got, &want));
        // a member applied to one argument too many: `nP + nIdx = 0`, so the
        // spine is not a member occurrence and only its parts are rewritten
        let over = expr::app(expr::mk_const(name::dup(&u), Vec::new()), expr::bvar(0));
        let got = spec_fam(&t, &[], 0, &members, &over);
        assert!(expr::beq(&got, &expr::app(expr::dup(&want), expr::bvar(0))));
        // a constant outside the block is untouched
        let other = expr::mk_const(n("Nat"), Vec::new());
        assert!(expr::beq(&spec_fam(&t, &[], 0, &members, &other), &other));
    }

    /// `mentionsAny` answers over a DAG, `.proj`'s structure name included.
    #[test]
    fn mentions_any_sees_proj_structure_names() {
        let e = expr::proj(n("S"), 0, expr::bvar(0));
        assert!(mentions_any(&[n("S")], &e));
        assert!(!mentions_any(&[n("T")], &e));
        let f = expr::forall_e(
            expr::mk_const(n("Nat"), Vec::new()),
            expr::mk_const(n("T"), Vec::new()),
            bm(),
        );
        assert!(mentions_any(&[n("T")], &f));
        assert!(mentions_any(&[n("Nat")], &f));
        assert!(!mentions_any(&[n("U")], &f));
    }

    /// `betaHead` reduces the head and nothing else.
    #[test]
    fn beta_head_reduces_the_head_only() {
        let id = expr::lam(expr::sort(level::zero()), expr::bvar(0), bm());
        let arg = expr::mk_const(n("A"), Vec::new());
        let e = expr::app(id, expr::dup(&arg));
        assert!(expr::beq(&beta_head(&e), &arg));
        // an argument that is itself a redex is left alone
        let inner = expr::app(
            expr::lam(expr::sort(level::zero()), expr::bvar(0), bm()),
            expr::dup(&arg),
        );
        let e = expr::app(expr::mk_const(n("f"), Vec::new()), expr::dup(&inner));
        assert!(expr::beq(&beta_head(&e), &e));
    }

    /// `hintFor` is the kernel's `getMaxHeight` rule: one above the highest
    /// constant the value mentions.
    #[test]
    fn hint_for_is_one_above_the_highest_constant() {
        let heights = |x: &Name| -> u64 {
            if name::beq(x, &n("A")) {
                5
            } else if name::beq(x, &n("B")) {
                9
            } else {
                0
            }
        };
        let e = expr_ops::mk_app_n(
            expr::mk_const(n("A"), Vec::new()),
            &vec![
                expr::mk_const(n("B"), Vec::new()),
                expr::mk_const(n("C"), Vec::new()),
            ],
        );
        assert_eq!(max_height(&heights, &e), 9);
        assert_eq!(hint_height(&hint_for(&heights, &e)), 10);
    }
}
