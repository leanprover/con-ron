//! `ConLeche/Kernel/Inductives/StructParts.lean` — the **pure recognition and
//! generation layer** every direct install reads: the type-former family, the
//! constructor spines, the recursor rule bodies, the Π→Π/λ rewrites that
//! re-datum a telescope, `StructParts` with its recogniser, the projection
//! table's bodies and guard levels, and two `@[csimp]` walk families.
//!
//! ## The three `@[csimp]` families are one Rust function each (task #13)
//!
//! con-leche writes `Expr.hasLooseBVarB`, `structProjGuards` and
//! `Expr.mentionsConst` twice — a plain structural `def` that every proof
//! consumes, and a memoized `*Go`/`*Fast` pair that a `@[csimp]` lemma
//! substitutes into compiled code.  The port implements the **`*Fast`**
//! member, because that is what con-leche *executes* (§3.1 is about the
//! executed program); the `@[csimp]` lemma is a kernel-checked equation
//! `@f = @fFast`, so the Rust function refines the logical definition by that
//! equation and no proof downstream ever sees the memo.  The plain `def`s are
//! ported too, unmemoized and uncalled, so that the provenance gate stays in
//! step with their source (task #11's `beqRecursive` rule).
//!
//! Every memo here is **local**: created empty inside the `*Fast` wrapper and
//! dropped on return, because the answer also depends on parameters that are
//! not in the key (`i`, `T`).  As in task #13 the port creates a
//! `crate::ron::hashmap::HashMap` in the wrapper and hands it down as `&mut`,
//! which Aeneas translates into con-leche's own threaded-map signature.

use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
use crate::kernel::expr_ops;
use crate::kernel::expr_ops::{sub_nat, ExprNatKey};
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::HashMap;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// Small list helpers (Lean's value semantics, spelled out)
// ---------------------------------------------------------------------------

/// con-leche: none — `lps.map .param`, the level spine of a block's own constant
/// Every generator below writes `.const T (lps.map .param)`; this is that
/// list.  The entry point of the index recursion below.
pub fn params_of(lps: &Vec<Name>) -> Vec<Level> {
    params_of_from(lps, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `params_of`
pub fn params_of_from(lps: &Vec<Name>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= lps.len() {
        out
    } else {
        let mut out = out;
        out.push(level::param(name::dup(&lps[i])));
        params_of_from(lps, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The generators (`StructParts.lean:82-211`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/SumParts.lean:112-119 InductiveShape.withSort
/// con-leche: ConLeche/Kernel/Inductives/NativeParts.lean:562-614 nativeShape?
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// `Level.isEquiv s .zero == some true` — "the result sort is provably
/// `Prop`", the `isProp` flag all three recognisers compute.  Its own function
/// because the `Option Bool` match borrows the level and the caller then moves
/// it into the record it is building (task #14's rule; Aeneas answered *"Could
/// not match the contexts"* at the joined `let`).
pub fn level_is_prop(s: &Level) -> bool {
    match level::is_equiv(s, &level::zero()) {
        Some(true) => true,
        Some(false) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
/// The parameter variables as seen from under `o` extra binders:
/// `p_k = bvar (o + nP - 1 - k)` — `structFam`'s argument spine.  The `i = 0`
/// wrapper of the index recursion below.
pub fn struct_ps_at(o: u64, n_p: u64) -> Vec<Expr> {
    struct_ps_at_from(o, n_p, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:134-137 structPsAt
/// The index recursion behind `struct_ps_at` (`(List.range nP).map`).
pub fn struct_ps_at_from(o: u64, n_p: u64, k: u64, out: Vec<Expr>) -> Vec<Expr> {
    if k >= n_p {
        out
    } else {
        let mut out = out;
        out.push(expr::bvar(o + n_p - 1 - k));
        struct_ps_at_from(o, n_p, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:82-86 structFam
/// The type former applied to its parameter variables, `bvar` indices offset
/// by `o` (the number of binders crossed since the parameters).
pub fn struct_fam(t: &Name, lps: &Vec<Name>, n_p: u64, o: u64) -> Expr {
    let head = expr::mk_const(name::dup(t), params_of(lps));
    expr_ops::mk_app_n(head, &struct_ps_at(o, n_p))
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:96-99 structRuleBody
/// The field spine `(List.range m).map fun j => .bvar (m - 1 - j)` that every
/// constructor spine and rule body below appends — and, at `m` the length of
/// a reflexive field's own telescope, `NativeParts.lean`'s `structTeleVars`
/// (`native_parts::struct_tele_vars` is this function under that name and
/// citation).  The `k = 0` wrapper of the index recursion below.
pub fn field_spine(m: u64) -> Vec<Expr> {
    field_spine_from(m, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
/// The index recursion behind `field_spine`.
pub fn field_spine_from(m: u64, k: u64, out: Vec<Expr>) -> Vec<Expr> {
    if k >= m {
        out
    } else {
        let mut out = out;
        out.push(expr::bvar(m - 1 - k));
        field_spine_from(m, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:88-94 structCtorSpine
/// The constructor applied to the parameter and field variables, as spelled
/// inside the recursor's minor premise (parameters sit above the motive
/// binder) — `structCtorSpineAt` at `o = 1` (`structCtorSpine_eq_at`).
pub fn struct_ctor_spine(c: &Name, lps: &Vec<Name>, n_p: u64, n_f: u64) -> Expr {
    struct_ctor_spine_at(c, lps, 1, n_p, n_f)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:144-150 structCtorSpineAt
/// The constructor applied to the parameter and field variables, as spelled
/// under `o` binders between the parameters and the fields (the motive and
/// the earlier minor premises).
pub fn struct_ctor_spine_at(c: &Name, lps: &Vec<Name>, o: u64, n_p: u64, n_f: u64) -> Expr {
    let head = expr::mk_const(name::dup(c), params_of(lps));
    let args: Vec<Expr> = crate::kernel::core_k::append_exprs(
        struct_ps_at(o + n_f, n_p),
        &field_spine(n_f),
    );
    expr_ops::mk_app_n(head, &args)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:96-99 structRuleBody
/// The recursor rule's right-hand side body: the minor premise applied to the
/// field variables.
pub fn struct_rule_body(n_f: u64) -> Expr {
    expr_ops::mk_app_n(expr::bvar(n_f), &field_spine(n_f))
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:139-142 structElimLevel
/// The recursor's elimination level: the fresh parameter at the large
/// eliminator, `zero` at the small one.
pub fn struct_elim_level(elim: &Name, large: bool) -> Level {
    if large {
        level::param(name::dup(elim))
    } else {
        level::zero()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:152-158 Expr.replacePisPw
/// Replace the body under the first `k` `∀`-binders, resetting their codomain
/// data to `pw` (the domains are kept).  Built on the way *out* of the
/// recursion, as cited — there is nothing to accumulate.
pub fn replace_pis_pw(pw: &PropWhen, k: u64, e: &Expr, b: &Expr) -> Option<Expr> {
    if k == 0 {
        Some(expr::dup(b))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(ty, rest, _) => match replace_pis_pw(pw, k - 1, rest, b) {
                Some(r) => Some(expr::forall_e(
                    expr::dup(ty),
                    r,
                    expr::binder_meta(prop_when::dup(pw)),
                )),
                None => None,
            },
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:160-167 Expr.pisToLamsPw
/// Convert the first `k` `∀`-binders into `λ`-binders with datum `pw` over a
/// body (`pisToLams` with the datum supplied instead of the `.never`
/// placeholder).
pub fn pis_to_lams_pw(pw: &PropWhen, k: u64, e: &Expr, b: &Expr) -> Option<Expr> {
    if k == 0 {
        Some(expr::dup(b))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(ty, rest, _) => match pis_to_lams_pw(pw, k - 1, rest, b) {
                Some(r) => Some(expr::lam(
                    expr::dup(ty),
                    r,
                    expr::binder_meta(prop_when::dup(pw)),
                )),
                None => None,
            },
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:189-194 structFamI
/// The family applied to its parameter variables and its index variables:
/// `e` extra binders sit between the parameters and the indices (the motive
/// and the minors), `o` binders below the index frame.
pub fn struct_fam_i(t: &Name, lps: &Vec<Name>, n_p: u64, n_idx: u64, e: u64, o: u64) -> Expr {
    let head = expr::mk_const(name::dup(t), params_of(lps));
    let args: Vec<Expr> = crate::kernel::core_k::append_exprs(
        struct_ps_at(o + e + n_idx, n_p),
        &struct_ps_at(o, n_idx),
    );
    expr_ops::mk_app_n(head, &args)
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:196-202 structCtorResidOk
/// A constructor residual's shape at an indexed family: the family at exactly
/// the parameter variables (`o` binders below the parameter frame) followed
/// by `nIdx` index expressions.  Deviation: the `&&` cascade is an `if` nest
/// (task #3's pattern 9), keeping the cited short-circuit order.
pub fn struct_ctor_resid_ok(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    o: u64,
    n_idx: u64,
    cbody: &Expr,
) -> bool {
    let head = expr_ops::get_app_fn(cbody);
    let expected = expr::mk_const(name::dup(t), params_of(lps));
    if expr::beq(&head, &expected) {
        let args: Vec<Expr> = expr_ops::get_app_args(cbody);
        if args.len() as u64 == n_p + n_idx {
            expr::exprs_beq(
                &expr_ops::take_exprs(&args, n_p as usize),
                &struct_ps_at(o, n_p),
            )
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:204-211 structMotiveTyI
/// The motive's type `∀ ı⃗ (t : T p⃗ ı⃗), Sort ℓ` at the parameters' frame,
/// over the former's index telescope `itele = ∀ ı⃗, Sort w` (scoped at the
/// parameters); every binder's codomain is a type former, never a
/// proposition.
pub fn struct_motive_ty_i(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_idx: u64,
    l: &Level,
    itele: &Expr,
) -> Option<Expr> {
    let body = expr::forall_e(
        struct_fam_i(t, lps, n_p, n_idx, 0, 0),
        expr::sort(level::dup(l)),
        expr::binder_meta(prop_when::never()),
    );
    replace_pis_pw(&prop_when::never(), n_idx, itele, &body)
}

// ---------------------------------------------------------------------------
// `StructParts` and its recogniser (`StructParts.lean:213-333`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:213-244 StructParts
/// The pieces of a recognised simple-structure block.  Deviations as for
/// `InductiveShape` (`deriving Repr` dropped, counts `u64`).
///
/// Nothing in the shipped install path consumes this record — the simple
/// structure route was deleted at con-leche's task #210 Part C and the
/// in-process modeller (`Frontend/InModel/Kit.lean`, outside the verified
/// core) is its one reader.  It is ported so that the provenance gate stays
/// in step with its source and so that `structShape`/`structPartsCore?`,
/// which the modeller's kit calls, have a record to return.
pub struct StructParts {
    pub cv_t: ConstantVal,
    pub cv_c: ConstantVal,
    pub n_p: u64,
    pub n_f: u64,
    pub cv_r: ConstantVal,
    pub elim: Name,
    pub res_sort: Level,
    pub rhs: Expr,
    pub large: bool,
    pub is_prop: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// The motive binder's clause of `structShape`: the motive's codomain is
/// `Sort elim` at the large eliminator and `Prop` at the small one, and its
/// own major domain is the family at the parameters.  Split off so that every
/// `else` arm of the cited `&&` cascade stays a tail position (task #18's
/// pattern 3).
pub fn struct_shape_motive(
    t: &Name,
    lps: &Vec<Name>,
    elim: &Name,
    large: bool,
    n_p: u64,
    rbs: &Vec<(Expr, BinderMeta)>,
) -> bool {
    if (n_p as usize) < rbs.len() {
        match &rbs[n_p as usize].0 .0.kind {
            ExprKind::ForallE(mmaj, cod, _) => match &cod.0.kind {
                ExprKind::Sort(s2) => {
                    let ok = if large {
                        level::beq(s2, &level::param(name::dup(elim)))
                    } else {
                        level::beq(s2, &level::zero())
                    };
                    if ok {
                        expr::beq(mmaj, &struct_fam(t, lps, n_p, 0))
                    } else {
                        false
                    }
                }
                _ => false,
            },
            _ => false,
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// The minor binder's clause: the minor's own `nF`-binder telescope ends in
/// `motive (C p⃗ f⃗)`.
pub fn struct_shape_minor(
    c: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    rbs: &Vec<(Expr, BinderMeta)>,
) -> bool {
    if (n_p as usize + 1) < rbs.len() {
        match expr_ops::strip_pis(n_f, &rbs[n_p as usize + 1].0) {
            Some(q) => expr::beq(
                &q.1,
                &expr::app(expr::bvar(n_f), struct_ctor_spine(c, lps, n_p, n_f)),
            ),
            None => false,
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// The major binder's clause: its domain is the family at the parameters,
/// two binders down.
pub fn struct_shape_major(
    t: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    rbs: &Vec<(Expr, BinderMeta)>,
) -> bool {
    if (n_p as usize + 2) < rbs.len() {
        expr::beq(&rbs[n_p as usize + 2].0, &struct_fam(t, lps, n_p, 2))
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:246-281 structShape
/// The *shape* facts the model reads off the stored (annotated) types —
/// everything annotation cannot change, checked on both the raw block
/// (recognition) and the annotated constants (install).
pub fn struct_shape(
    t: &Name,
    c: &Name,
    lps: &Vec<Name>,
    elim: &Name,
    large: bool,
    n_p: u64,
    n_f: u64,
    tty: &Expr,
    cty: &Expr,
    rty: &Expr,
) -> bool {
    match expr_ops::strip_pis(n_p, tty) {
        Some(tq) => match &tq.1 .0.kind {
            ExprKind::Sort(_) => match expr_ops::strip_pis(n_p + n_f, cty) {
                Some(cq) => match expr_ops::strip_pis(n_p + 3, rty) {
                    Some(rq) => {
                        if expr::beq(&cq.1, &struct_fam(t, lps, n_p, n_f)) {
                            if expr::beq(
                                &rq.1,
                                &expr::app(expr::bvar(2), expr::bvar(0)),
                            ) {
                                if struct_shape_motive(t, lps, elim, large, n_p, &rq.0) {
                                    if struct_shape_minor(c, lps, n_p, n_f, &rq.0) {
                                        struct_shape_major(t, lps, n_p, &rq.0)
                                    } else {
                                        false
                                    }
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
                },
                None => false,
            },
            _ => false,
        },
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// The block-independent front guards of `structPartsCore?`: the recursor's
/// name, the shared level parameters, the three reserved-name exclusions, the
/// two argument sums and the single rule's constructor, field count and
/// λ-stripped body.  Split off so that the cited `&&` cascade's arms stay
/// tail positions.
pub fn struct_parts_front_ok(
    cv_t: &ConstantVal,
    cv_c: &ConstantVal,
    cv_r: &ConstantVal,
    n_p: u64,
    n_f: u64,
    m_i: u64,
    r_p: u64,
    rule: &env::RecRule,
) -> bool {
    const REC: [u32; 3] = [114, 101, 99];
    let t = name::dup(&cv_t.name);
    let expected_rec = name::mk_str(t, crate::kernel::core_types::code_points(&REC));
    let reserved = crate::kernel::basis_names::reserved_basis_names();
    if name::beq(&cv_r.name, &expected_rec) {
        if prop_when::names_beq(&cv_c.level_params, &cv_t.level_params) {
            if !name::contains(&reserved, &cv_t.name) {
                if !name::contains(&reserved, &cv_c.name) {
                    if !name::contains(&reserved, &cv_r.name) {
                        if m_i == n_p + 2 {
                            if r_p == n_p + 2 {
                                if name::beq(&rule.ctor, &cv_c.name) {
                                    if rule.nfields == n_f {
                                        match expr_ops::strip_lams(n_p + 2 + n_f, &rule.rhs) {
                                            Some(q) => {
                                                expr::beq(&q.1, &struct_rule_body(n_f))
                                            }
                                            None => false,
                                        }
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
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

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// The `large?` reading: a fresh elimination level parameter in front of the
/// block's own, with the large-eliminator shape confirmed.  `none` falls
/// through to the small-eliminator branch in the caller.
pub fn struct_parts_large(
    cv_t: &ConstantVal,
    cv_c: &ConstantVal,
    cv_r: &ConstantVal,
    n_p: u64,
    n_f: u64,
) -> Option<Name> {
    if cv_r.level_params.len() == 0 {
        None
    } else {
        let elim = name::dup(&cv_r.level_params[0]);
        let relps: Vec<Name> =
            prop_when::append_from(&cv_r.level_params, 1, Vec::new());
        if prop_when::names_beq(&relps, &cv_t.level_params) {
            if !name::contains(&cv_t.level_params, &elim) {
                if struct_shape(
                    &cv_t.name,
                    &cv_c.name,
                    &cv_t.level_params,
                    &elim,
                    true,
                    n_p,
                    n_f,
                    &cv_t.ty,
                    &cv_c.ty,
                    &cv_r.ty,
                ) {
                    Some(elim)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// The `large? = none` branch's guard: the recursor carries the block's own
/// level parameters and the small-eliminator shape holds.  Its own function
/// for the same reason as `struct_parts_large` above — the cited conjunction
/// borrows all three constants and the caller reads them again, which Aeneas
/// answered with an internal error at the joined `if` (task #14's rule).
pub fn struct_parts_small_ok(
    cv_t: &ConstantVal,
    cv_c: &ConstantVal,
    cv_r: &ConstantVal,
    n_p: u64,
    n_f: u64,
) -> bool {
    if prop_when::names_beq(&cv_r.level_params, &cv_t.level_params) {
        struct_shape(
            &cv_t.name,
            &cv_c.name,
            &cv_t.level_params,
            &name::anonymous(),
            false,
            n_p,
            n_f,
            &cv_t.ty,
            &cv_c.ty,
            &cv_r.ty,
        )
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:283-329 structPartsCore?
/// Recognise a direct simple-structure block (see the module docs).  `none`
/// means "not this class" — the caller falls through to the modeled path, so
/// this is never an error source.
///
/// Deviations: the three-element list pattern is an index match on a `Vec`,
/// the `&&` cascade is `struct_parts_front_ok` above, and Lean's
/// `match cvR.levelParams with | elim :: relps` is `struct_parts_large`
/// (the cons pattern over a `Vec` is a length test and a spine copy).
pub fn struct_parts_core(block: &Vec<ConstantInfo>) -> Option<StructParts> {
    if block.len() != 3 {
        None
    } else {
        match (&block[0], &block[1], &block[2]) {
            (
                ConstantInfo::IndInfo(cv_t, _),
                ConstantInfo::CtorInfo(cv_c, n_p, n_f),
                ConstantInfo::RecInfo(cv_r, m_i, r_p, rules),
            ) => {
                if rules.len() != 1 {
                    None
                } else if struct_parts_front_ok(
                    cv_t, cv_c, cv_r, *n_p, *n_f, *m_i, *r_p, &rules[0],
                ) {
                    match expr_ops::strip_pis(*n_p, &cv_t.ty) {
                        Some(q) => match &q.1 .0.kind {
                            ExprKind::Sort(s) => {
                                let is_prop = level_is_prop(s);
                                match struct_parts_large(cv_t, cv_c, cv_r, *n_p, *n_f) {
                                    Some(elim) => Some(StructParts {
                                        cv_t: env::constant_val_dup(cv_t),
                                        cv_c: env::constant_val_dup(cv_c),
                                        n_p: *n_p,
                                        n_f: *n_f,
                                        cv_r: env::constant_val_dup(cv_r),
                                        elim,
                                        res_sort: level::dup(s),
                                        rhs: expr::dup(&rules[0].rhs),
                                        large: true,
                                        is_prop,
                                    }),
                                    None => {
                                        if struct_parts_small_ok(
                                            cv_t, cv_c, cv_r, *n_p, *n_f,
                                        ) {
                                            Some(StructParts {
                                                cv_t: env::constant_val_dup(cv_t),
                                                cv_c: env::constant_val_dup(cv_c),
                                                n_p: *n_p,
                                                n_f: *n_f,
                                                cv_r: env::constant_val_dup(cv_r),
                                                elim: name::anonymous(),
                                                res_sort: level::dup(s),
                                                rhs: expr::dup(&rules[0].rhs),
                                                large: false,
                                                is_prop,
                                            })
                                        } else {
                                            None
                                        }
                                    }
                                }
                            }
                            _ => None,
                        },
                        None => None,
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// The projection table's pieces (`StructParts.lean:335-356`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
/// The parameter spine of the generated projection types, spelled at the
/// frame of the final `∀ p⃗ (t : T p⃗), _` telescope: `p_k = bvar (nP - k)`.
pub fn struct_proj_ps(n_p: u64) -> Vec<Expr> {
    struct_proj_ps_from(n_p, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:331-337 structProjPs
/// The index recursion behind `struct_proj_ps`.
pub fn struct_proj_ps_from(n_p: u64, k: u64, out: Vec<Expr>) -> Vec<Expr> {
    if k >= n_p {
        out
    } else {
        let mut out = out;
        out.push(expr::bvar(n_p - k));
        struct_proj_ps_from(n_p, k + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:339-345 structProjArgP
/// The `j`-th earlier-field substitute in a tower entry's generated type: the
/// first-class node `t.j` (`.proj T j` of the subject `t = bvar 0`).
pub fn struct_proj_arg_p(t: &Name, j: u64) -> Expr {
    expr::proj(name::dup(t), j, expr::bvar(0))
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:347-354 structProjResidP
/// The constructor telescope peeled at the parameters and the first `i`
/// subject projections, threaded incrementally (step `i → i + 1` is a single
/// `instantiate1Lift`).  Deviation: the `Option.bind` over a closure is an
/// explicit `match` (§3.4).
pub fn struct_proj_resid_p(t: &Name, n_p: u64, cty: &Expr, i: u64) -> Option<Expr> {
    if i == 0 {
        expr_ops::inst_pis_at_lift(&struct_proj_ps(n_p), cty)
    } else {
        match struct_proj_resid_p(t, n_p, cty, i - 1) {
            Some(r) => {
                let args: Vec<Expr> =
                    crate::kernel::core_k::expr_singleton(&struct_proj_arg_p(t, i - 1));
                expr_ops::inst_pis_at_lift(&args, &r)
            }
            None => None,
        }
    }
}

// ---------------------------------------------------------------------------
// `hasLooseBVar`, `hasLooseBVarB` and the memoized walk
// (`StructParts.lean:357-636`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:356-369 Expr.hasLooseBVar
/// Does `bvar i` occur loose in `e`?  (Not through fvar type annotations —
/// the generated telescopes are fvar-free.)  The *specification* of the
/// bounded walk below; nothing executable calls it, and it is ported so the
/// provenance gate stays in step with its source.
pub fn has_loose_bvar(i: u64, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(j) => i == *j,
        ExprKind::Fvar(_, _) => false,
        ExprKind::Sort(_) => false,
        ExprKind::Const(_, _) => false,
        ExprKind::Lit(_) => false,
        ExprKind::App(f, a) => {
            if has_loose_bvar(i, f) {
                true
            } else {
                has_loose_bvar(i, a)
            }
        }
        ExprKind::Lam(ty, b, _) => {
            if has_loose_bvar(i, ty) {
                true
            } else {
                has_loose_bvar(i + 1, b)
            }
        }
        ExprKind::ForallE(ty, b, _) => {
            if has_loose_bvar(i, ty) {
                true
            } else {
                has_loose_bvar(i + 1, b)
            }
        }
        ExprKind::LetE(t, v, b) => {
            if has_loose_bvar(i, t) {
                true
            } else if has_loose_bvar(i, v) {
                true
            } else {
                has_loose_bvar(i + 1, b)
            }
        }
        ExprKind::Proj(_, _, sub) => has_loose_bvar(i, sub),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:371-390 Expr.hasLooseBVarB
/// `hasLooseBVar` with the packed bound's cutoff: a node whose loose-bvar
/// bound is at or below `i` has no `bvar i`, so the walk stops there without
/// descending.  The *logical* definition; the executed one is
/// `has_loose_bvar_b` below (the `@[csimp]` family, module note).  Ported so
/// the gate stays in step with its source.
pub fn has_loose_bvar_b_spec(i: u64, e: &Expr) -> bool {
    if expr_ops::bvar_b(e) <= i {
        false
    } else {
        match &e.0.kind {
            ExprKind::Bvar(j) => i == *j,
            ExprKind::Fvar(_, _) => false,
            ExprKind::Sort(_) => false,
            ExprKind::Const(_, _) => false,
            ExprKind::Lit(_) => false,
            ExprKind::App(f, a) => {
                if has_loose_bvar_b_spec(i, f) {
                    true
                } else {
                    has_loose_bvar_b_spec(i, a)
                }
            }
            ExprKind::Lam(ty, b, _) => {
                if has_loose_bvar_b_spec(i, ty) {
                    true
                } else {
                    has_loose_bvar_b_spec(i + 1, b)
                }
            }
            ExprKind::ForallE(ty, b, _) => {
                if has_loose_bvar_b_spec(i, ty) {
                    true
                } else {
                    has_loose_bvar_b_spec(i + 1, b)
                }
            }
            ExprKind::LetE(t, v, b) => {
                if has_loose_bvar_b_spec(i, t) {
                    true
                } else if has_loose_bvar_b_spec(i, v) {
                    true
                } else {
                    has_loose_bvar_b_spec(i + 1, b)
                }
            }
            ExprKind::Proj(_, _, sub) => has_loose_bvar_b_spec(i, sub),
        }
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `(Expr × Nat)` key, `Bool` values
/// An owning memo probe, so the map's borrow ends with the lookup: the
/// `none` branch of the cited `match memo[(e, i)]? with` needs the map
/// mutably again (task #13's pattern 1).
pub fn memo_b_get(memo: &HashMap<ExprNatKey, bool>, k: &ExprNatKey) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:435-440 Expr.hasLooseBVarBIns
/// Record one answer for `(e, i)` in the memo the walk hands back.
pub fn has_loose_bvar_b_ins(memo: &mut HashMap<ExprNatKey, bool>, e: &Expr, i: u64, r: bool) {
    memo.insert(expr_ops::expr_nat_key(e, i), r);
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
/// The memoized `hasLooseBVarB` walk.  The cutoff and the memo are
/// complementary: the cutoff stops the walk where the variable *cannot*
/// occur, the memo stops the re-entry of a shared node whose answer is
/// `false`.  The five leaf arms answer *before* the probe, exactly as cited.
///
/// Deviation: the memo is a `&mut HashMap` rather than a threaded value
/// (task #13); Aeneas turns the `&mut` back into con-leche's own threaded
/// return, so the generated Lean carries the cited signature.
pub fn has_loose_bvar_b_go(memo: &mut HashMap<ExprNatKey, bool>, i: u64, e: &Expr) -> bool {
    if expr_ops::bvar_b(e) <= i {
        false
    } else {
        match &e.0.kind {
            ExprKind::Bvar(j) => i == *j,
            ExprKind::Fvar(_, _) => false,
            ExprKind::Sort(_) => false,
            ExprKind::Const(_, _) => false,
            ExprKind::Lit(_) => false,
            _ => {
                let key = expr_ops::expr_nat_key(e, i);
                match memo_b_get(memo, &key) {
                    Some(r) => r,
                    None => {
                        let r = has_loose_bvar_b_node(memo, i, e);
                        has_loose_bvar_b_ins(memo, e, i, r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:442-478 Expr.hasLooseBVarBGo
/// The inner `match e with` of `hasLooseBVarBGo`'s miss branch, split off so
/// that the probe's borrow dies before the descent mutates the memo (task
/// #14's rule: never hold a container's borrow across a branch that touches
/// the container).  The `_ => (false, memo)` arm is the cited unreachable
/// one — the five leaf kinds answered above.
pub fn has_loose_bvar_b_node(memo: &mut HashMap<ExprNatKey, bool>, i: u64, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::App(f, a) => {
            if has_loose_bvar_b_go(memo, i, f) {
                true
            } else {
                has_loose_bvar_b_go(memo, i, a)
            }
        }
        ExprKind::Lam(ty, b, _) => {
            if has_loose_bvar_b_go(memo, i, ty) {
                true
            } else {
                has_loose_bvar_b_go(memo, i + 1, b)
            }
        }
        ExprKind::ForallE(ty, b, _) => {
            if has_loose_bvar_b_go(memo, i, ty) {
                true
            } else {
                has_loose_bvar_b_go(memo, i + 1, b)
            }
        }
        ExprKind::LetE(t, v, b) => {
            if has_loose_bvar_b_go(memo, i, t) {
                true
            } else if has_loose_bvar_b_go(memo, i, v) {
                true
            } else {
                has_loose_bvar_b_go(memo, i + 1, b)
            }
        }
        ExprKind::Proj(_, _, sub) => has_loose_bvar_b_go(memo, i, sub),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:624-626 Expr.hasLooseBVarBFast
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:371-390 Expr.hasLooseBVarB
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:628-631 Expr.hasLooseBVarB_eq_hasLooseBVarBFast
/// **The executed `hasLooseBVarB`** — one memoized DAG walk with an empty,
/// per-call memo.  The cited `@[csimp]` lemma is what makes this the port of
/// the logical definition too (module note).
pub fn has_loose_bvar_b(i: u64, e: &Expr) -> bool {
    let mut memo: HashMap<ExprNatKey, bool> = HashMap::new();
    has_loose_bvar_b_go(&mut memo, i, e)
}

// ---------------------------------------------------------------------------
// `structUsedLater` and the guard table (`StructParts.lean:634-759`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:633-641 structUsedLater
/// **Field `j` is used by a later field** — the official `infer_proj`'s
/// `has_loose_bvars(binding_body(r))` at step `j`: the field's variable
/// occurs in the constructor telescope's remainder after binder `j`.
pub fn struct_used_later(cty: &Expr, n_p: u64, j: u64) -> bool {
    match expr_ops::strip_pis(n_p + j + 1, cty) {
        Some(q) => has_loose_bvar_b(0, &q.1),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:669-674 structUsedLaterGo
/// Memoized `structUsedLater`, taking the shared memo (and, in the port,
/// mutating it in place rather than handing it back).
pub fn struct_used_later_go(
    memo: &mut HashMap<ExprNatKey, bool>,
    cty: &Expr,
    n_p: u64,
    j: u64,
) -> bool {
    match expr_ops::strip_pis(n_p + j + 1, cty) {
        Some(q) => has_loose_bvar_b_go(memo, 0, &q.1),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:685-692 structUsedLaterList
/// `structUsedLater cty nP j` for `j = base, …, base + n - 1`, in order,
/// through one shared memo.  Lean conses on the way out; the port pushes on
/// the way in, which is the same order (task #13's pattern 3).
pub fn struct_used_later_list(
    memo: &mut HashMap<ExprNatKey, bool>,
    cty: &Expr,
    n_p: u64,
    n: u64,
    base: u64,
    out: Vec<bool>,
) -> Vec<bool> {
    if n == 0 {
        out
    } else {
        let r = struct_used_later_go(memo, cty, n_p, base);
        let mut out = out;
        out.push(r);
        struct_used_later_list(memo, cty, n_p, n - 1, base + 1, out)
    }
}

/// con-leche: none — `sorts.getD i .zero` over a `Vec<Level>`
/// The out-of-range fallback the guard fold spells at every read.
pub fn sort_get_d(sorts: &Vec<Level>, i: u64) -> Level {
    if (i as usize) < sorts.len() {
        level::dup(&sorts[i as usize])
    } else {
        level::zero()
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
/// The inner `(List.range i).foldl` of the guard table: field `i`'s own sort
/// joined with the sorts of the earlier fields a later field uses.
pub fn struct_proj_guard_at(used: &Vec<bool>, sorts: &Vec<Level>, i: u64, j: u64, acc: Level) -> Level {
    if j >= i {
        acc
    } else {
        let u = if (j as usize) < used.len() {
            used[j as usize]
        } else {
            false
        };
        let acc2 = if u {
            level::max(acc, sort_get_d(sorts, j))
        } else {
            acc
        };
        struct_proj_guard_at(used, sorts, i, j + 1, acc2)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:643-656 structProjGuards
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:734-746 structProjGuards_eq_structProjGuardsFast
/// **The projection guard levels**, as con-leche executes them: the `nF`
/// `structUsedLater` answers first, through *one* shared
/// `hasLooseBVarBGo` memo, then the fold.  The pure `structProjGuards`
/// asks `structUsedLater` once per pair `j < i < nF` (O(nF²) telescope
/// walks); the cited `@[csimp]` lemma is what lets the port implement the
/// fast form and still refine the definition the model stage tables consume.
pub fn struct_proj_guards(cty: &Expr, n_p: u64, n_f: u64, sorts: &Vec<Level>) -> Vec<Level> {
    let mut memo: HashMap<ExprNatKey, bool> = HashMap::new();
    let used: Vec<bool> =
        struct_used_later_list(&mut memo, cty, n_p, n_f, 0, Vec::new());
    struct_proj_guards_from(&used, sorts, n_f, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:722-732 structProjGuardsFast
/// The outer `(List.range nF).map` of the guard table.
pub fn struct_proj_guards_from(
    used: &Vec<bool>,
    sorts: &Vec<Level>,
    n_f: u64,
    i: u64,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= n_f {
        out
    } else {
        let mut out = out;
        out.push(struct_proj_guard_at(used, sorts, i, 0, sort_get_d(sorts, i)));
        struct_proj_guards_from(used, sorts, n_f, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The projection bodies (`StructParts.lean:761-773`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:748-766 structProjBodiesGo
/// con-leche: ConLeche/Cached/CheckerC.lean:37-43 structProjBodiesGoC
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove struct_parts::struct_proj_bodies_go_refines, then delete this line
/// The projection bodies' one walk of the constructor telescope: field `i`'s
/// domain is body `i`, and the field is replaced by the subject's projection
/// `.proj T i (bvar 0)` before the walk continues.  Lean conses `fdom` on the
/// way out; the port pushes it on the way in, which is the same
/// outermost-first list (task #13's pattern 3).
///
/// The cached driver's walker (`structProjBodiesGoC`, the second citation) is
/// the same walk at `ExprC.instantiate1Lift`, which is this substitution
/// (`structProjBodiesC_eq`); `struct_proj_bodies` below records the ruling.
pub fn struct_proj_bodies_go(
    t: &Name,
    k: u64,
    i: u64,
    e: &Expr,
    out: Vec<Expr>,
) -> Option<Vec<Expr>> {
    if k == 0 {
        Some(out)
    } else {
        match &e.0.kind {
            ExprKind::ForallE(fdom, body, _) => {
                let mut out = out;
                out.push(expr::dup(fdom));
                let next: Expr =
                    expr_ops::instantiate1_lift(body, &struct_proj_arg_p(t, i), 0);
                struct_proj_bodies_go(t, k - 1, i + 1, &next, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:768-771 structProjBodies
/// con-leche: ConLeche/Cached/CheckerC.lean:45-50 structProjBodiesC
/// **The projection bodies of a recognised block.**  Deviation: `Array Expr`
/// is `Vec<Expr>` (the port has one list type), so the cited
/// `List.toArray` is the identity here.
///
/// The cached driver's walker (`structProjBodiesC`, the second citation)
/// differs only in taking `ExprC.instantiate1Lift` — con-leche's *interned*
/// substitution — where this takes `Expr.instantiate1Lift`; since con-leche's
/// task #172 B3a there is one expression type, and `structProjBodiesC_eq` is
/// the equation.  The port has one spelling, as §3.1's "the environment is
/// the index" ruling has for the `F` twins.
pub fn struct_proj_bodies(t: &Name, n_p: u64, n_f: u64, cty: &Expr) -> Option<Vec<Expr>> {
    match expr_ops::inst_pis_at_lift(&struct_proj_ps(n_p), cty) {
        Some(r) => struct_proj_bodies_go(t, n_f, 0, &r, Vec::new()),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// `mentionsConst` and its memoized walk (`StructParts.lean:775-930`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:773-782 Expr.mentionsConst
/// Does the constant `T` occur in `e`?  A syntactic walk (`fvar` annotations
/// included; a `.proj` node names its structure).  The *logical* definition;
/// the executed one is `mentions_const` below.
pub fn mentions_const_spec(t: &Name, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => false,
        ExprKind::Sort(_) => false,
        ExprKind::Lit(_) => false,
        ExprKind::Const(n, _) => name::beq(n, t),
        ExprKind::Fvar(_, ty) => mentions_const_spec(t, ty),
        ExprKind::App(f, a) => {
            if mentions_const_spec(t, f) {
                true
            } else {
                mentions_const_spec(t, a)
            }
        }
        ExprKind::Lam(ty, b, _) => {
            if mentions_const_spec(t, ty) {
                true
            } else {
                mentions_const_spec(t, b)
            }
        }
        ExprKind::ForallE(ty, b, _) => {
            if mentions_const_spec(t, ty) {
                true
            } else {
                mentions_const_spec(t, b)
            }
        }
        ExprKind::LetE(ty, v, b) => {
            if mentions_const_spec(t, ty) {
                true
            } else if mentions_const_spec(t, v) {
                true
            } else {
                mentions_const_spec(t, b)
            }
        }
        ExprKind::Proj(s, _, sub) => {
            if name::beq(s, t) {
                true
            } else {
                mentions_const_spec(t, sub)
            }
        }
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `Expr` key, `Bool` values
/// The owning memo probe of `mentionsConstGo` (task #13's pattern 1).
pub fn memo_eb_get(memo: &HashMap<Expr, bool>, k: &Expr) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
/// The memoized `mentionsConst` walk: the four leaf arms answer before the
/// probe, every other node is probed, walked and recorded.
///
/// Deviation: the cited walk does **not** short-circuit — `let (b₁, memo) :=
/// go f; let (b₂, memo) := go a; (b₁ || b₂, memo)` walks *both* children even
/// when the first answers `true`, because the memo it hands back must hold
/// both answers.  The port keeps that, so the memo contents agree node for
/// node with con-leche's.
pub fn mentions_const_go(t: &Name, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => false,
        ExprKind::Sort(_) => false,
        ExprKind::Lit(_) => false,
        ExprKind::Const(n, _) => name::beq(n, t),
        _ => match memo_eb_get(memo, e) {
            Some(r) => r,
            None => {
                let r = mentions_const_node(t, memo, e);
                memo.insert(expr::dup(e), r);
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:814-849 Expr.mentionsConstGo
/// The inner `match e with` of the miss branch, split off so the probe's
/// borrow dies before the descent mutates the memo (task #14's rule).  The
/// final `| e => (e.mentionsConst T, memo)` arm is the cited unreachable one
/// — the four leaf kinds answered above.
pub fn mentions_const_node(t: &Name, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Fvar(_, ty) => mentions_const_go(t, memo, ty),
        ExprKind::App(f, a) => {
            let b1 = mentions_const_go(t, memo, f);
            let b2 = mentions_const_go(t, memo, a);
            if b1 {
                true
            } else {
                b2
            }
        }
        ExprKind::Lam(ty, body, _) => {
            let b1 = mentions_const_go(t, memo, ty);
            let b2 = mentions_const_go(t, memo, body);
            if b1 {
                true
            } else {
                b2
            }
        }
        ExprKind::ForallE(ty, body, _) => {
            let b1 = mentions_const_go(t, memo, ty);
            let b2 = mentions_const_go(t, memo, body);
            if b1 {
                true
            } else {
                b2
            }
        }
        ExprKind::LetE(ty, val, body) => {
            let b1 = mentions_const_go(t, memo, ty);
            let b2 = mentions_const_go(t, memo, val);
            let b3 = mentions_const_go(t, memo, body);
            if b1 {
                true
            } else if b2 {
                true
            } else {
                b3
            }
        }
        ExprKind::Proj(s, _, sub) => {
            let b = mentions_const_go(t, memo, sub);
            if name::beq(s, t) {
                true
            } else {
                b
            }
        }
        _ => mentions_const_spec(t, e),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:922-924 Expr.mentionsConstFast
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:773-782 Expr.mentionsConst
/// con-leche: ConLeche/Kernel/Inductives/StructParts.lean:926-929 Expr.mentionsConst_eq_mentionsConstFast
/// **The executed `mentionsConst`** — one memoized DAG walk.  The
/// recogniser's positivity walk asks this of every field domain and index
/// argument, and on a DAG-shared field type the tree walk does not finish.
pub fn mentions_const(t: &Name, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    mentions_const_go(t, &mut memo, e)
}

/// con-leche: none — `sub_nat`, re-exported so the generators below read as the Lean
/// Lean's `Nat` subtraction truncates at zero; `u64`'s underflows into an
/// Aeneas `fail`.  Task #13's helper is the port's spelling of it.
pub fn nat_sub(a: u64, b: u64) -> u64 {
    sub_nat(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn raw() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn bvars(xs: &Vec<Expr>) -> Vec<u64> {
        let mut out: Vec<u64> = Vec::new();
        for e in xs {
            match &e.0.kind {
                ExprKind::Bvar(i) => out.push(*i),
                _ => out.push(9999),
            }
        }
        out
    }

    /// The three de Bruijn spines the generators are built from, at the
    /// indices the cited definitions name.
    #[test]
    fn the_generator_spines_are_at_the_cited_indices() {
        // `structPsAt o nP = (range nP).map fun k => bvar (o + nP - 1 - k)`
        assert_eq!(bvars(&struct_ps_at(0, 3)), vec![2, 1, 0]);
        assert_eq!(bvars(&struct_ps_at(2, 3)), vec![4, 3, 2]);
        assert_eq!(bvars(&struct_ps_at(5, 0)), Vec::<u64>::new());
        // the field spine, innermost last
        assert_eq!(bvars(&field_spine(3)), vec![2, 1, 0]);
        // `structProjPs nP = (range nP).map fun k => bvar (nP - k)`
        assert_eq!(bvars(&struct_proj_ps(3)), vec![3, 2, 1]);
        // `structRuleBody nF = bvar nF applied to the field spine`
        let body = struct_rule_body(2);
        assert!(expr::beq(
            &body,
            &expr_ops::mk_app_n(expr::bvar(2), &field_spine(2))
        ));
        // `structCtorSpine` is `structCtorSpineAt` at `o = 1`
        let c = nm("C");
        assert!(expr::beq(
            &struct_ctor_spine(&c, &Vec::new(), 2, 3),
            &struct_ctor_spine_at(&c, &Vec::new(), 1, 2, 3)
        ));
        // and the elimination level is the fresh parameter, or `zero`
        assert!(level::beq(
            &struct_elim_level(&nm("u"), true),
            &level::param(nm("u"))
        ));
        assert!(level::beq(&struct_elim_level(&nm("u"), false), &level::zero()));
    }

    /// The two memoized walks answer what their unmemoized specifications do,
    /// on a term with sharing, binders and a `.proj` node — and `replacePisPw`
    /// / `pisToLamsPw` re-datum exactly the binders they are given.
    #[test]
    fn the_csimp_walks_agree_with_their_specifications() {
        let a = expr::mk_const(nm("A"), Vec::new());
        // `∀ (x : A) (y : bvar 0), bvar 1` — `bvar 0` is loose in the body at
        // depth 0 only after two binders are crossed
        let inner = expr::forall_e(expr::bvar(0), expr::bvar(1), raw());
        let tele = expr::forall_e(expr::dup(&a), inner, raw());
        let mut i: u64 = 0;
        while i < 4 {
            assert_eq!(
                has_loose_bvar_b(i, &tele),
                has_loose_bvar_b_spec(i, &tele),
                "the memoized walk must agree at index {}",
                i
            );
            assert_eq!(has_loose_bvar_b(i, &tele), has_loose_bvar(i, &tele));
            i += 1;
        }
        // `mentionsConst` sees an `fvar` annotation and a `.proj` structure
        let x = expr::fvar(0, expr::mk_const(nm("B"), Vec::new()));
        let pj = expr::proj(nm("S"), 0, expr::dup(&x));
        assert!(mentions_const(&nm("B"), &x));
        assert!(mentions_const(&nm("S"), &pj));
        assert!(mentions_const(&nm("B"), &pj));
        assert!(!mentions_const(&nm("C"), &pj));
        assert_eq!(
            mentions_const(&nm("B"), &pj),
            mentions_const_spec(&nm("B"), &pj)
        );
        assert_eq!(
            mentions_const(&nm("C"), &pj),
            mentions_const_spec(&nm("C"), &pj)
        );
        // the two re-datum rewrites
        let pw = prop_when::if_all_zero(Vec::new());
        match replace_pis_pw(&pw, 1, &tele, &expr::bvar(7)) {
            Some(r) => match &r.0.kind {
                ExprKind::ForallE(dom, body, m) => {
                    assert!(expr::beq(dom, &a), "the domain is kept");
                    assert!(expr::beq(body, &expr::bvar(7)));
                    assert!(prop_when::beq(&m.pw, &pw), "the datum is reset");
                }
                _ => panic!("a ∀ comes out"),
            },
            None => panic!("one binder is there to replace"),
        }
        match pis_to_lams_pw(&pw, 1, &tele, &expr::bvar(7)) {
            Some(r) => match &r.0.kind {
                ExprKind::Lam(_, _, m) => assert!(prop_when::beq(&m.pw, &pw)),
                _ => panic!("a λ comes out"),
            },
            None => panic!("one binder is there to convert"),
        }
        assert!(replace_pis_pw(&pw, 3, &tele, &expr::bvar(0)).is_none());
    }

    /// **The projection table's bodies and guard levels.**  For a
    /// two-field structure `C : ∀ (p : A) (f0 : p) (f1 : f0), T p` the bodies
    /// are the field domains with the earlier fields replaced by the subject's
    /// projections, and field `0`'s guard joins its own sort with nothing
    /// (`structUsedLater` is asked only about *earlier* fields).
    #[test]
    fn the_projection_bodies_and_guards() {
        let t = nm("T");
        let a = expr::mk_const(nm("A"), Vec::new());
        // `∀ (p : A) (f0 : p) (f1 : f0), T p`
        let mut tp: Vec<Expr> = Vec::new();
        tp.push(expr::bvar(2));
        let cty = expr::forall_e(
            expr::dup(&a),
            expr::forall_e(
                expr::bvar(0),
                expr::forall_e(
                    expr::bvar(0),
                    expr_ops::mk_app_n(expr::mk_const(name::dup(&t), Vec::new()), &tp),
                    raw(),
                ),
                raw(),
            ),
            raw(),
        );
        match struct_proj_bodies(&t, 1, 2, &cty) {
            Some(bodies) => {
                assert_eq!(bodies.len(), 2);
                // field 0's type is the parameter, at `bvar 1` under the subject
                assert!(expr::beq(&bodies[0], &expr::bvar(1)));
                // field 1's type is field 0, i.e. `.proj T 0 (bvar 0)`
                assert!(expr::beq(&bodies[1], &struct_proj_arg_p(&t, 0)));
            }
            None => panic!("the bodies must build"),
        }
        // field 0 *is* used later (field 1's domain is it), field 1 is not
        assert!(struct_used_later(&cty, 1, 0));
        assert!(!struct_used_later(&cty, 1, 1));
        // the guards: field 0's own sort; field 1's own sort joined with
        // field 0's, because field 0 is used later
        let mut sorts: Vec<Level> = Vec::new();
        sorts.push(level::succ(level::zero()));
        sorts.push(level::zero());
        let guards = struct_proj_guards(&cty, 1, 2, &sorts);
        assert_eq!(guards.len(), 2);
        assert!(level::beq(&guards[0], &level::succ(level::zero())));
        assert!(level::beq(
            &guards[1],
            &level::max(level::zero(), level::succ(level::zero()))
        ));
    }
}
