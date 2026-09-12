//! `ConLeche/Frontend/ProjRec.lean` — projection functions of non-direct
//! structure-likes, rewritten as recursor applications.
//!
//! The elaborator spells a structure's projection function as
//! `fun p⃗ self => .proj T i self`.  The official kernel types `.proj T i` on
//! every *structure-like* type; this checker serves `.proj` only on the class
//! its direct install recognises, so on the Mathlib stream the first
//! projection function of a mutual member declines the run.  The user's
//! design (2026-09-06, verbatim): *"replace these projection functions, only
//! for mutual (not direct) inductives, by recursor applications, before
//! installation.  Completely transparent to the verified code."*  This module
//! is that rewrite, a pure function on the parsed declaration.
//!
//! **It cannot fire yet, and that is deliberate** (task #37).  The
//! elimination level `ℓ` is not syntactic in the projection's codomain: it is
//! read off the model family's own artifact `T._model.proj_i.iota`, and since
//! con-leche task #219 the ONLY source of that artifact is the in-process
//! modeller (`ConLeche/Frontend/InModel/Mutual.lean`).  con-ron declines
//! every stream that needs the modeller until task #38, so
//! `export_c::StateD::proj_levels` is always empty and `proj_rewrite_d`
//! always answers `None` — the declaration stays as parsed and declines as
//! before, which is exactly con-leche's "no artifact, no rewrite".  The
//! module is ported now so that #38 is the modeller and nothing else; its
//! unit tests below exercise the shape recognisers and the owner census,
//! which DO run on every inductive record of every stream.
//!
//! Two deviations.  `occursConst`'s budgeted descent (`occursConstB`) is not
//! ported: it exists so that the common case allocates no `Std.HashSet` in
//! Lean, and a Rust `HashSet::new()` allocates nothing until its first
//! insert, so `occurs_const_fast` is the memoised walk alone (all four Lean
//! declarations are cited on it).  And the three tuple types `projRecOwners`
//! takes become named structs, because a seven-component Lean tuple read as
//! `·.2.2.2.2.2.2` is not something to transliterate.

use std::collections::HashSet;

use con_ron_core::cached::expr_ops_c;
use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::ConstantInfo;
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Expr, ExprKind};
use con_ron_core::kernel::expr_ops;
use con_ron_core::kernel::inductives::native_parts;
use con_ron_core::kernel::inductives::struct_parts;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::{Name, NameKind};

use crate::frontend::nat_op_ground::ExprKey;

/// con-leche: ConLeche/Frontend/ProjRec.lean:83-104 ProjRecOwner
/// What the rewrite needs to know about one structure-like owner `T` of a
/// parsed inductive block that the direct install does not serve.
pub struct ProjRecOwner {
    /// the type former
    pub t: Name,
    /// the block's level parameters
    pub lps: Vec<Name>,
    /// parameter count
    pub n_p: u64,
    /// the single constructor
    pub ctor: Name,
    /// its field count
    pub n_f: u64,
    /// the owner's recursor `T.rec`: name, level parameters, type
    pub rec_name: Name,
    pub rec_lps: Vec<Name>,
    pub rec_type: Expr,
    /// the recursor's motive and minor counts (the export's own)
    pub num_motives: u64,
    pub num_minors: u64,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:106-111 projIotaName
/// The name of the model family's constructor-reduction theorem for field `i`
/// of `T`: `T._model.proj_i.iota`.
pub fn proj_iota_name(t: &Name, i: u64) -> Name {
    let a = name::mk_str(name::dup(t), "_model".chars().map(|c| c as u32).collect());
    let b = name::mk_str(a, format!("proj_{}", i).chars().map(|c| c as u32).collect());
    name::mk_str(b, "iota".chars().map(|c| c as u32).collect())
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:113-118 isProjIotaName
/// Is `n` of the shape `X._model.proj_i.iota`?  Cheap pre-filter for the
/// theorem records (the last component decides before anything is compared).
pub fn is_proj_iota_name(n: &Name) -> bool {
    match &n.0.kind {
        NameKind::Str(p1, last) => {
            if last.iter().copied().ne("iota".chars().map(|c| c as u32)) {
                return false;
            }
            match &p1.0.kind {
                NameKind::Str(p2, s) => match &p2.0.kind {
                    NameKind::Str(_, m) => {
                        m.iter().copied().eq("_model".chars().map(|c| c as u32))
                            && s.len() >= 5
                            && s[..5].iter().copied().eq("proj_".chars().map(|c| c as u32))
                    }
                    _ => false,
                },
                _ => false,
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:120-125 projIotaLevel
/// The `Eq` level of an artifact iota statement `∀ …, @Eq.{ℓ} α a b`: the
/// field's sort.  `None` on any other shape.
pub fn proj_iota_level(ty: &Expr) -> Option<Level> {
    let head = expr_ops::get_app_fn(&expr_ops::pi_result(ty));
    match &head.0.kind {
        ExprKind::Const(n, us) => {
            if us.len() == 1 && name::beq(n, &bnm::eq_name()) {
                Some(level::dup(&us[0]))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:227-231 occursConstFast
/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// con-leche: ConLeche/Frontend/ProjRec.lean:151-178 occursConstB
/// con-leche: ConLeche/Frontend/ProjRec.lean:127-136 occursConst
/// Does the constant `n` occur in `e`?  (Not through fvar type annotations —
/// parsed declarations are fvar-free.)  Memoised: the set holds the subterms
/// already shown NOT to mention `n`, so only `false` is recorded — a `true`
/// aborts the walk and no `true` is ever re-queried.  `projRecOwners` runs
/// this over every constructor binder domain of every inductive block in the
/// stream, and structural recursion means `O(tree)` on a shared DAG.
pub fn occurs_const_fast(n: &Name, e: &Expr) -> bool {
    let mut seen: HashSet<ExprKey> = HashSet::new();
    occurs_const_go(n, &mut seen, e)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:180-225 occursConstGo
/// The memoised descent's body.
pub fn occurs_const_go(n: &Name, seen: &mut HashSet<ExprKey>, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Const(m, _) => name::beq(m, n),
        ExprKind::Bvar(_) | ExprKind::Fvar(_, _) | ExprKind::Sort(_) | ExprKind::Lit(_) => false,
        _ => {
            if seen.contains(&ExprKey(expr::dup(e))) {
                return false;
            }
            let hit = match &e.0.kind {
                ExprKind::App(f, a) => occurs_const_go(n, seen, f) || occurs_const_go(n, seen, a),
                ExprKind::Lam(ty, b, _) | ExprKind::ForallE(ty, b, _) => {
                    occurs_const_go(n, seen, ty) || occurs_const_go(n, seen, b)
                }
                ExprKind::LetE(t, v, b) => {
                    occurs_const_go(n, seen, t)
                        || occurs_const_go(n, seen, v)
                        || occurs_const_go(n, seen, b)
                }
                ExprKind::Proj(_, _, sub) => occurs_const_go(n, seen, sub),
                _ => false,
            };
            if !hit {
                seen.insert(ExprKey(expr::dup(e)));
            }
            hit
        }
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:233-237 lamBody
/// The body under every leading `λ` (the projection shape's pre-filter: the
/// node under the value's binders).
pub fn lam_body(e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Lam(_, b, _) => lam_body(b),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:239-245 stripPisAll
/// Strip every leading `∀`: the binder list (outermost first) and the body.
pub fn strip_pis_all(e: &Expr) -> (Vec<(Expr, BinderMeta)>, Expr) {
    let mut bs: Vec<(Expr, BinderMeta)> = Vec::new();
    let mut cur = expr::dup(e);
    loop {
        let next = match &cur.0.kind {
            ExprKind::ForallE(ty, b, m) => {
                bs.push((expr::dup(ty), expr::binder_meta_dup(m)));
                expr::dup(b)
            }
            _ => return (bs, cur),
        };
        cur = next;
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:247-249 mkLams
/// Rebuild a `λ`-telescope over a binder list (outermost first).
pub fn mk_lams(bs: &[(Expr, BinderMeta)], body: Expr) -> Expr {
    let mut acc = body;
    for (ty, m) in bs.iter().rev() {
        acc = expr::lam(expr::dup(ty), acc, expr::binder_meta_dup(m));
    }
    acc
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:251-257 instPisOpen
/// Instantiate the leading `∀`-binders at *open* arguments (the body-frame
/// variables and the built motives/minors), one binder per argument,
/// returning the residual telescope.
pub fn inst_pis_open(e: &Expr, args: &[Expr]) -> Option<Expr> {
    let mut cur = expr::dup(e);
    for a in args {
        let next = match &cur.0.kind {
            ExprKind::ForallE(_, body, _) => expr_ops_c::instantiate1_lift(body, a, 0),
            _ => return None,
        };
        cur = next;
    }
    Some(cur)
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:259-269 buildBinders
/// Peel `k` binders of a telescope, building one term per binder from its
/// (progressively instantiated) domain, and instantiating the telescope with
/// that term before the next binder is read.
pub fn build_binders(
    mk: &dyn Fn(&Expr) -> Option<Expr>,
    k: u64,
    e: &Expr,
) -> Option<(Vec<Expr>, Expr)> {
    let mut out: Vec<Expr> = Vec::new();
    let mut cur = expr::dup(e);
    for _ in 0..k {
        let next = match &cur.0.kind {
            ExprKind::ForallE(dom, body, _) => {
                let t = mk(dom)?;
                let b = expr_ops_c::instantiate1_lift(body, &t, 0);
                out.push(t);
                b
            }
            _ => return None,
        };
        cur = next;
    }
    Some((out, cur))
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:271-277 headIs
/// Is `T` the head of the owner's own carrier: the motive domain
/// `∀ (t : T p⃗), Sort ℓ` (exactly one binder) or the major-premise domain.
pub fn head_is(t: &Name, e: &Expr) -> bool {
    match &expr_ops::get_app_fn(e).0.kind {
        ExprKind::Const(n, _) => name::beq(n, t),
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:279-330 projRecValue
/// **The rewrite.**  `ty`/`val` are the definition's declared type and value,
/// `i` the projected field, `l` the field's sort (from the artifact).  `None`
/// = the value is not of the projection shape (the caller keeps the
/// declaration unchanged).
pub fn proj_rec_value(o: &ProjRecOwner, l: &Level, ty: &Expr, val: &Expr, i: u64) -> Option<Expr> {
    let (lbs, body) = expr_ops::strip_lams(o.n_p + 1, val)?;
    if !expr::beq(
        &body,
        &expr::proj(name::dup(&o.t), i, expr::mk_bvar(0)),
    ) {
        return None;
    }
    if i >= o.n_f {
        return None;
    }
    let (_, r) = expr_ops::strip_pis(o.n_p + 1, ty)?;
    let us: Vec<Level> = o.lps.iter().map(|n| level::param(name::dup(n))).collect();
    // the recursor's type at the chosen elimination level; the body frame is
    // the value's own `nP + 1` binders: parameter `k` is `bvar (nP - k)`, the
    // subject `bvar 0`
    let mut lus: Vec<Level> = vec![level::dup(l)];
    for u in us.iter() {
        lus.push(level::dup(u));
    }
    let rty = expr_ops::instantiate_level_params(&o.rec_lps, &lus, &o.rec_type);
    let params: Vec<Expr> = (0..o.n_p).map(|k| expr::mk_bvar(o.n_p - k)).collect();
    let rty = inst_pis_open(&rty, &params)?;
    // motives: the owner's is `fun (t : T p⃗) => R` (R's parameter references
    // skip the new binder; its subject reference IS the new binder); every
    // other one is the constant `PUnit.{ℓ}` over its telescope
    let mk_motive = |dom: &Expr| -> Option<Expr> {
        let (bs, cod) = strip_pis_all(dom);
        match &cod.0.kind {
            ExprKind::Sort(_) => {}
            _ => return None,
        }
        if bs.len() == 1 {
            let (d, m) = &bs[0];
            if head_is(&o.t, d) {
                Some(expr::lam(
                    expr::dup(d),
                    expr_ops::lift_loose_bvars(1, 1, &r),
                    expr::binder_meta_dup(m),
                ))
            } else {
                Some(expr::lam(
                    expr::dup(d),
                    expr::mk_const(bnm::punit_name(), vec![level::dup(l)]),
                    expr::binder_meta_dup(m),
                ))
            }
        } else {
            Some(mk_lams(
                &bs,
                expr::mk_const(bnm::punit_name(), vec![level::dup(l)]),
            ))
        }
    };
    let (motives, rty) = build_binders(&mk_motive, o.num_motives, &rty)?;
    // minors: the owner constructor's returns field `i` of its telescope
    // (fields first, then the inductive hypotheses); every other one returns
    // `PUnit.unit.{ℓ}`.  The owner's minor is the one whose codomain applies
    // a motive to the owner constructor
    let mk_minor = |dom: &Expr| -> Option<Expr> {
        let (bs, cod) = strip_pis_all(dom);
        let args = expr_ops::get_app_args(&cod);
        let major = args.last()?;
        if head_is(&o.ctor, major) {
            if i < bs.len() as u64 {
                Some(mk_lams(
                    &bs,
                    expr::mk_bvar(bs.len() as u64 - 1 - i),
                ))
            } else {
                None
            }
        } else {
            Some(mk_lams(
                &bs,
                expr::mk_const(bnm::punit_unit_name(), vec![level::dup(l)]),
            ))
        }
    };
    let (minors, rty) = build_binders(&mk_minor, o.num_minors, &rty)?;
    // the major premise: the owner has no indices, so the next binder is the
    // subject itself
    match &rty.0.kind {
        ExprKind::ForallE(maj_dom, _, _) => {
            if !head_is(&o.t, maj_dom) {
                return None;
            }
            let mut args: Vec<Expr> = Vec::new();
            for p in params.iter() {
                args.push(expr::dup(p));
            }
            for m in motives.iter() {
                args.push(expr::dup(m));
            }
            for m in minors.iter() {
                args.push(expr::dup(m));
            }
            args.push(expr::mk_bvar(0));
            let app = expr_ops::mk_app_n(
                expr::mk_const(name::dup(&o.rec_name), lus),
                &args,
            );
            Some(mk_lams(&lbs, app))
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `types`' component of the export record's own shape data (Lean's
/// `(name, levelParams, type, numParams, numIndices, ctors, isRec)`).
pub struct ProjTypeRec {
    pub name: Name,
    pub lps: Vec<Name>,
    pub ty: Expr,
    pub n_p: u64,
    pub n_i: u64,
    pub ctors: Vec<Name>,
    pub is_rec: bool,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `ctors`' component (Lean's `(name, numFields, type)`).
pub struct ProjCtorRec {
    pub name: Name,
    pub n_f: u64,
    pub ty: Expr,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// `recs`' component (Lean's `(name, levelParams, type, numMotives,
/// numMinors)`).
pub struct ProjRecRec {
    pub name: Name,
    pub lps: Vec<Name>,
    pub ty: Expr,
    pub n_m: u64,
    pub nm: u64,
}

/// con-leche: ConLeche/Frontend/ProjRec.lean:332-370 projRecOwners
/// Which block members the rewrite serves: the officially structure-like ones
/// (one constructor, zero indices) of a block the direct install does not
/// recognise — `structPartsCore?` rejects it (mutual, multi-constructor,
/// indexed, shape mismatch) or it is recursive (the export's `isRec`, or a
/// block name occurring in a constructor's binder domains).  Propositional
/// owners and owners whose recursor carries no elimination level parameter
/// are left out.
pub fn proj_rec_owners(
    block: &Vec<ConstantInfo>,
    types: &[ProjTypeRec],
    ctors: &[ProjCtorRec],
    recs: &[ProjRecRec],
) -> Vec<ProjRecOwner> {
    let block_names: Vec<Name> = types.iter().map(|t| name::dup(&t.name)).collect();
    // a block name in a constructor's binder *domains* (its result names the
    // owner by definition)
    let recursive = types.iter().any(|t| t.is_rec)
        || ctors.iter().any(|c| {
            strip_pis_all(&c.ty)
                .0
                .iter()
                .any(|(d, _)| block_names.iter().any(|n| occurs_const_fast(n, d)))
        });
    if struct_parts::struct_parts_core(block).is_some() && !recursive {
        return Vec::new();
    }
    // a block the fixpoint route takes serves its structure-like member's
    // `.proj` nodes natively, so no rewrite (the block's DECLARED parameter
    // count, task #228: the first type record's)
    let n_pd = match types.first() {
        Some(t) => t.n_p,
        None => 0,
    };
    if native_parts::native_parts(n_pd, block).is_some() {
        return Vec::new();
    }
    let mut out: Vec<ProjRecOwner> = Vec::new();
    for t in types.iter() {
        if t.ctors.len() != 1 {
            continue;
        }
        let c_name = &t.ctors[0];
        if t.n_i != 0 {
            continue;
        }
        let s = match expr_ops::strip_pis(t.n_p, &t.ty) {
            None => continue,
            Some((_, body)) => match &body.0.kind {
                ExprKind::Sort(s) => level::dup(s),
                _ => continue,
            },
        };
        if level::is_equiv(&s, &level::zero()) == Some(true) {
            continue;
        }
        let c = match ctors.iter().find(|c| name::beq(&c.name, c_name)) {
            None => continue,
            Some(c) => c,
        };
        let want_rec = name::mk_str(
            name::dup(&t.name),
            "rec".chars().map(|c| c as u32).collect(),
        );
        let r = match recs.iter().find(|r| name::beq(&r.name, &want_rec)) {
            None => continue,
            Some(r) => r,
        };
        if r.lps.len() != t.lps.len() + 1 {
            continue;
        }
        out.push(ProjRecOwner {
            t: name::dup(&t.name),
            lps: t.lps.iter().map(name::dup).collect(),
            n_p: t.n_p,
            ctor: name::dup(c_name),
            n_f: c.n_f,
            rec_name: name::dup(&r.name),
            rec_lps: r.lps.iter().map(name::dup).collect(),
            rec_type: expr::dup(&r.ty),
            num_motives: r.n_m,
            num_minors: r.nm,
        });
    }
    out
}

/// con-leche: none — `env::to_constant_val(ci).name`, spelled here so
/// `export_c`'s owner registration reads like the Lean.
pub fn info_name(ci: &ConstantInfo) -> Name {
    env::constant_info_name(ci)
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_builder::{bn, cnst, pi, prop, srt, type1};

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    fn dotted(p: Name, s: &str) -> Name {
        name::mk_str(p, s.chars().map(|c| c as u32).collect())
    }

    /// The artifact name and its pre-filter.
    #[test]
    fn proj_iota_names() {
        let n = proj_iota_name(&nm("T"), 3);
        assert!(is_proj_iota_name(&n));
        assert!(!is_proj_iota_name(&nm("T")));
        assert!(!is_proj_iota_name(&dotted(nm("T"), "iota")));
        // `_model.notproj_0.iota` is not one
        let bad = dotted(
            dotted(dotted(nm("T"), "_model"), "notproj_0"),
            "iota",
        );
        assert!(!is_proj_iota_name(&bad));
        // and neither is `_model.proj_0.other`
        let bad2 = dotted(dotted(dotted(nm("T"), "_model"), "proj_0"), "other");
        assert!(!is_proj_iota_name(&bad2));
    }

    /// The `Eq` level of an artifact statement is the field's sort.
    #[test]
    fn the_iota_statement_names_the_field_sort() {
        let u = level::param(nm("u"));
        let stmt = pi(
            type1(),
            expr_ops::mk_app_n(
                cnst(bnm::eq_name(), vec![level::dup(&u)]),
                &vec![expr::mk_bvar(0), expr::mk_bvar(0), expr::mk_bvar(0)],
            ),
        );
        match proj_iota_level(&stmt) {
            Some(l) => assert!(level::beq(&l, &u)),
            None => panic!("no level"),
        }
        // any other head is `None`
        assert!(proj_iota_level(&pi(type1(), cnst(nm("X"), Vec::new()))).is_none());
    }

    /// `occursConst`, memoised: a constant under a shared DAG is found, and a
    /// term that does not mention it answers `false` without revisiting.
    #[test]
    fn occurs_const_walks_a_dag() {
        let c = cnst(nm("C"), Vec::new());
        let shared = expr::app(cnst(nm("D"), Vec::new()), expr::dup(&c));
        let e = expr::app(expr::dup(&shared), expr::dup(&shared));
        assert!(occurs_const_fast(&nm("C"), &e));
        assert!(occurs_const_fast(&nm("D"), &e));
        assert!(!occurs_const_fast(&nm("E"), &e));
    }

    /// `stripPisAll`/`mkLams` round-trip a telescope, and `lamBody` reaches
    /// the node under every `λ`.
    #[test]
    fn telescope_helpers() {
        let t = pi(type1(), pi(prop(), expr::mk_bvar(0)));
        let (bs, body) = strip_pis_all(&t);
        assert_eq!(bs.len(), 2);
        let lams = mk_lams(&bs, expr::dup(&body));
        assert!(expr::beq(&lam_body(&lams), &body));
    }

    /// A one-constructor, index-free, non-`Prop`, non-recursive block whose
    /// direct install DOES serve it gets no owner; the same block made mutual
    /// (two type records) gets one.
    #[test]
    fn owner_census_skips_the_direct_shapes() {
        // `S (a : Type) : Type` with one constructor `S.mk (a : Type) (x : a)
        // : S a` and a recursor `S.rec.{u,?}`
        let s = nm("S");
        let mk = dotted(name::dup(&s), "mk");
        let rec = dotted(name::dup(&s), "rec");
        let ty_s = pi(type1(), type1());
        let ty_mk = pi(
            type1(),
            pi(expr::mk_bvar(0), expr::app(cnst(name::dup(&s), Vec::new()), expr::mk_bvar(1))),
        );
        let ty_rec = pi(type1(), srt(level::param(nm("u"))));
        let types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: expr::dup(&ty_s),
            n_p: 1,
            n_i: 0,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        let ctors = vec![ProjCtorRec {
            name: name::dup(&mk),
            n_f: 1,
            ty: expr::dup(&ty_mk),
        }];
        let recs = vec![ProjRecRec {
            name: name::dup(&rec),
            lps: vec![nm("u")],
            ty: expr::dup(&ty_rec),
            n_m: 1,
            nm: 1,
        }];
        // The block as `ConstantInfo`s, so `structPartsCore?`/`nativeParts?`
        // see something of the right length; whatever they answer, a
        // PROPOSITIONAL owner is never an owner, which is the clause this
        // asserts.
        let block: Vec<ConstantInfo> = Vec::new();
        let prop_types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: pi(type1(), prop()),
            n_p: 1,
            n_i: 0,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        assert!(proj_rec_owners(&block, &prop_types, &ctors, &recs).is_empty());
        // an indexed owner is never one either
        let idx_types = vec![ProjTypeRec {
            name: name::dup(&s),
            lps: Vec::new(),
            ty: expr::dup(&ty_s),
            n_p: 1,
            n_i: 1,
            ctors: vec![name::dup(&mk)],
            is_rec: false,
        }];
        assert!(proj_rec_owners(&block, &idx_types, &ctors, &recs).is_empty());
        // the well-shaped one IS an owner (the block is empty, so neither
        // recogniser claims it)
        let got = proj_rec_owners(&block, &types, &ctors, &recs);
        assert_eq!(got.len(), 1);
        assert!(name::beq(&got[0].t, &s));
        assert_eq!(got[0].n_f, 1);
    }
}
