//! `ConLeche/Frontend/InModel/Mutual.lean` — in-process models of a MUTUAL
//! inductive block (B1 index-free, B2 indexed): the tag enumeration, the
//! auxiliary family, the public `_model` slots the modeled install consumes,
//! the iota theorems, and the projection artifacts.
//!
//! The block's records are ordinary inductive records; every record below is
//! checked by the fold as a stream declaration, and a wrong one rejects or
//! declines, never accepts.  Declines name the residual.
//!
//! Deviations beyond `kit`'s three:
//!
//! * `Except String` becomes `Result<_, String>`, and the `throw`n message is
//!   the cited one verbatim (it is the decline text the driver prints, and
//!   `CON_LECHE_INMODEL_CENSUS` records it).
//! * `Ctx`'s three Lean function fields are `&dyn Fn` (`kit`'s note 1), and
//!   the generator's `heights` accumulator is a `Vec<(Name, u64)>` scanned
//!   front-to-back, which is con-leche's `List (Name × Nat)` with `find?`.
//! * The four-component tuples of `Kit.recTy`/`recRhs` are `kit::KCtor`.

use con_ron_core::kernel::env::Declaration;
use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, RecRule};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprView};
use con_ron_core::kernel::expr_ops;
use con_ron_core::kernel::inductives::struct_parts;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

use crate::render::name_str;
use con_ron_core::frontend::proj_rec;
use crate::in_model::kit;
use crate::in_model::kit::{
    app2, bm, const_p, dup_all, get_d, iota_name, mentions_any, mk_lams, mk_pis, model_name,
    pi_binders, sub, tag_ctor_name, vars_at, KCtor,
};

// The four block records of `InModel/Mutual.lean:65-99` are **the verified
// core's** since task #84: the parse builds them (`export_c::block_rec_of`)
// and the parse is in `crates/con-ron-core`, so they are inside the
// extraction and the modeller reads the core's copy rather than a twin.  The
// citations travel with the definitions, in
// `crates/con-ron-core/src/frontend/in_model_rec.rs`; the field names and
// order are unchanged, so nothing below this line had to move.
pub use con_ron_core::frontend::in_model_rec::{BlockRec, IndCtorRec, IndRecRec, IndTypeRec};

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:101-108 Ctx
/// What the generator reads besides the block: the declared types of the
/// constants so far, the definitional heights, and the parsed inductive
/// blocks so far by member type name (the nested rung reads a container's
/// shape off it).
pub struct Ctx<'a> {
    pub tbl: kit::ConstTable<'a>,
    pub heights: &'a dyn Fn(&Name) -> u64,
    pub blocks: &'a dyn Fn(&Name) -> Option<&'a BlockRec>,
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:110-116 MCtor
/// A constructor of member `m`, classified: its record, its recursive field
/// positions with the target member of each.
pub struct MCtor<'a> {
    pub m: u64,
    pub c: &'a IndCtorRec,
    pub rec_fields: Vec<(u64, u64)>,
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:118-131 memberApp?
/// Is `e` member `m'` of the block applied to the parameter variables (`o`
/// binders below the parameter frame) and `nIdx_{m'}` index expressions?
/// Returns the member.
pub fn member_app(
    members: &[(Name, u64, u64)],
    lps: &[Name],
    n_p: u64,
    o: u64,
    e: &Expr,
) -> Option<u64> {
    let f = expr_ops::get_app_fn(e);
    match expr::view(&f) {
        ExprView::Const(x, us) => {
            let (_, m2, n_idx) = members.iter().find(|m| name::beq(&m.0, x))?;
            let args = expr_ops::get_app_args(e);
            if kit::levels_are_params(us, lps)
                && args.len() as u64 == n_p + n_idx
                && expr::exprs_beq(
                    &dup_all(&args[..(n_p as usize).min(args.len())]),
                    &vars_at(o, n_p),
                )
            {
                Some(*m2)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:133-153 classifyCtor
/// Classify one constructor's fields: each domain is ordinary (no member
/// mentioned) or exactly a member at the parameters and some index
/// expressions (`T_{m'} p⃗ e⃗`); anything else is not this rung's (nested,
/// reflexive, non-positive).  `members` lists `(T, m, nIdx)`.
pub fn classify_ctor<'a>(
    members: &[(Name, u64, u64)],
    lps: &[Name],
    n_p: u64,
    m: u64,
    c: &'a IndCtorRec,
) -> Result<MCtor<'a>, String> {
    let member_names: Vec<Name> = members.iter().map(|x| name::dup(&x.0)).collect();
    let (bs, resid) = expr_ops::strip_pis(n_p + c.n_f, &c.cv.ty)
        .ok_or_else(|| format!("constructor {} is not a telescope", name_str(&c.cv.name)))?;
    if member_app(members, lps, n_p, c.n_f, &resid) != Some(m) {
        return Err(format!(
            "constructor {} does not return its member at the parameters",
            name_str(&c.cv.name)
        ));
    }
    let mut rec_fields: Vec<(u64, u64)> = Vec::new();
    for i in 0..c.n_f {
        let d = get_d(&pi_binders(&bs), n_p + i);
        match member_app(members, lps, n_p, i, &d) {
            Some(m2) => rec_fields.push((i, m2)),
            None => {
                if mentions_any(&member_names, &d) {
                    return Err(format!(
                        "field {} of {} mentions the block other than as a plain \
                         member application (nested, reflexive or non-positive occurrence)",
                        i,
                        name_str(&c.cv.name)
                    ));
                }
            }
        }
    }
    Ok(MCtor {
        m,
        c,
        rec_fields,
    })
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:155-158 need
/// Unwrap a generator step that cannot fail on a well-formed block.
pub fn need<T>(what: &str, o: Option<T>) -> Result<T, String> {
    o.ok_or_else(|| format!("internal shape failure: {}", what))
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:160-452 genMutual
/// **The mutual rung** (B1 index-free, B2 indexed).  The records, in stream
/// order: the tag block, the auxiliary block, the member/constructor/recursor
/// models, the iota theorems, the projection artifacts.
pub fn gen_mutual(ctx: &Ctx, b: &BlockRec) -> Result<Vec<Declaration>, String> {
    let t0 = b.types.first().ok_or_else(|| "empty block".to_string())?;
    let t_name = name::dup(&t0.cv.name);
    let lps: Vec<Name> = t0.cv.level_params.iter().map(name::dup).collect();
    let n_p = t0.n_p;
    let k = b.types.len() as u64;
    if k < 2 {
        return Err("not a mutual block".to_string());
    }
    for t in b.types.iter() {
        if t.num_nested != 0 {
            return Err(format!("nested member {} (B3)", name_str(&t.cv.name)));
        }
        if t.is_reflexive {
            return Err(format!("reflexive member {}", name_str(&t.cv.name)));
        }
        if !con_ron_core::frontend::export::names_beq(&t.cv.level_params, &lps) || t.n_p != n_p {
            return Err(format!(
                "member {}: level parameters or parameter count differ",
                name_str(&t.cv.name)
            ));
        }
    }
    let (pbs0, resid0) = expr_ops::strip_pis(n_p + t0.n_idx, &t0.cv.ty).ok_or_else(|| {
        format!(
            "former {} is not a telescope ending in a sort",
            name_str(&t_name)
        )
    })?;
    let u: Level = match expr::view(&resid0) {
        ExprView::Sort(u) => level::dup(u),
        _ => {
            return Err(format!(
                "former {} is not a telescope ending in a sort",
                name_str(&t_name)
            ))
        }
    };
    // the first member's parameter binders: the telescope of the tag, the
    // auxiliary family and all their constructors (the other members'
    // telescopes and sorts are not compared here — the fold's typing of the
    // public slots is official's `is_def_eq` / `is_equivalent` check)
    let pbs: Vec<Expr> = pi_binders(&pbs0[..(n_p as usize).min(pbs0.len())]);
    for t in b.types.iter() {
        let ok = match expr_ops::strip_pis(n_p + t.n_idx, &t.cv.ty) {
            Some((_, r)) => matches!(expr::view(&r), ExprView::Sort(_)),
            None => false,
        };
        if !ok {
            return Err(format!(
                "former {} is not a telescope ending in a sort",
                name_str(&t.cv.name)
            ));
        }
    }
    let member_names: Vec<Name> = b.types.iter().map(|t| name::dup(&t.cv.name)).collect();
    let members: Vec<(Name, u64, u64)> = (0..k)
        .map(|m| {
            (
                match member_names.get(m as usize) {
                    Some(n) => name::dup(n),
                    None => name::anonymous(),
                },
                m,
                b.types[m as usize].n_idx,
            )
        })
        .collect();
    let n_idx_of = |m: u64| -> u64 { b.types[m as usize].n_idx };
    // the constructors, per member, classified
    let mut mctors: Vec<MCtor> = Vec::new();
    for m in 0..k {
        let t = &b.types[m as usize];
        for cn in t.ctors.iter() {
            let c = b
                .ctors
                .iter()
                .find(|c| name::beq(&c.cv.name, cn))
                .ok_or_else(|| {
                    format!(
                        "constructor {} of {} is not in the block",
                        name_str(cn),
                        name_str(&t.cv.name)
                    )
                })?;
            if c.n_p != n_p || !con_ron_core::frontend::export::names_beq(&c.cv.level_params, &lps) {
                return Err(format!(
                    "constructor {}: parameter count or level parameters differ",
                    name_str(cn)
                ));
            }
            mctors.push(classify_ctor(&members, &lps, n_p, m, c)?);
        }
    }
    let n = mctors.len() as u64;
    if b.ctors.len() as u64 != n {
        return Err("constructors not all owned by a member".to_string());
    }
    // the recursors: `T_m.rec`, one per member, `k` motives, `n` minors, one
    // eliminator shape
    if b.recs.len() as u64 != k {
        return Err("recursor count differs from member count".to_string());
    }
    // the member's recursor, by name (the export's `recs` order is not the
    // members' in general)
    let rec_of = |m: u64| -> Result<&IndRecRec, String> {
        let t = &b.types[m as usize];
        let want = kit::nstr(name::dup(&t.cv.name), "rec");
        b.recs
            .iter()
            .find(|r| name::beq(&r.cv.name, &want))
            .ok_or_else(|| {
                format!(
                    "member {} has no recursor {}",
                    name_str(&t.cv.name),
                    name_str(&want)
                )
            })
    };
    let large_opt: Option<Name> = {
        let r0 = rec_of(0)?;
        match r0.cv.level_params.split_first() {
            Some((e, rest)) => {
                if con_ron_core::frontend::export::names_beq(&kit::dup_names(rest), &lps)
                    && !lps.iter().any(|x| name::beq(x, e))
                {
                    Some(name::dup(e))
                } else {
                    None
                }
            }
            None => None,
        }
    };
    let large = large_opt.is_some();
    let elim: Name = match &large_opt {
        Some(e) => name::dup(e),
        None => kit::fresh_level_name(&lps),
    };
    let rlps: Vec<Name> = if large {
        let mut v = vec![name::dup(&elim)];
        for x in lps.iter() {
            v.push(name::dup(x));
        }
        v
    } else {
        lps.iter().map(name::dup).collect()
    };
    for m in 0..k {
        let r = rec_of(m)?;
        if r.n_p != n_p || r.n_m != k || r.nm != n || r.n_i != n_idx_of(m) {
            return Err(format!(
                "recursor {}: unexpected telescope",
                name_str(&r.cv.name)
            ));
        }
        if !con_ron_core::frontend::export::names_beq(&r.cv.level_params, &rlps) {
            return Err(format!(
                "recursor {}: eliminator shape differs",
                name_str(&r.cv.name)
            ));
        }
        let own: Vec<&MCtor> = mctors.iter().filter(|mc| mc.m == m).collect();
        let ok = r.rules.len() == own.len()
            && (0..own.len()).all(|j| name::beq(&r.rules[j].ctor, &own[j].c.cv.name));
        if !ok {
            return Err(format!(
                "recursor {}: rules do not list the member's constructors",
                name_str(&r.cv.name)
            ));
        }
    }
    let is_prop = level::is_equiv(&u, &level::zero()) == Some(true);
    if is_prop && large {
        return Err(
            "Prop block with a large eliminator (the auxiliary family eliminates into Prop only)"
                .to_string(),
        );
    }
    let l_elim = struct_parts::struct_elim_level(&elim, large);
    let rlvls: Vec<Level> = if large {
        let mut v = vec![level::dup(&l_elim)];
        for x in kit::params_of(&lps) {
            v.push(x);
        }
        v
    } else {
        kit::params_of(&lps)
    };
    let elim_tag: Name = if large {
        name::dup(&elim)
    } else {
        kit::fresh_level_name(&lps)
    };
    // the block renaming of the modeled install (types, constructors, recursors)
    let mut block_names: Vec<Name> = member_names.iter().map(name::dup).collect();
    for c in b.ctors.iter() {
        block_names.push(name::dup(&c.cv.name));
    }
    for r in b.recs.iter() {
        block_names.push(name::dup(&r.cv.name));
    }
    let rn = |e: &Expr| -> Expr {
        expr_ops::rename_consts(
            &kit::RenameFn(|x: &Name| {
                if block_names.iter().any(|y| name::beq(y, x)) {
                    model_name(x)
                } else {
                    name::dup(x)
                }
            }),
            e,
        )
    };
    let tag = kit::tag_name(&t_name);
    let aux = kit::aux_name(&t_name);
    let ps0 = vars_at(0, n_p);
    let mut out: Vec<Declaration> = Vec::new();
    let mut heights: Vec<(Name, u64)> = Vec::new();
    // 1. the tag block: `tag : ∀ p⃗, Sort W`, `tag.m : ∀ p⃗ ı⃗_m, tag p⃗` with
    // `W = max 1 (the sorts of the index domains)` (B2; `Type` at an
    // index-free block)
    let mut w: Level = level::succ(level::zero());
    for t in b.types.iter() {
        let (ibs, _) = expr_ops::strip_pis(n_p + t.n_idx, &t.cv.ty)
            .ok_or_else(|| "unreachable".to_string())?;
        // the member's index binders at the FIRST member's parameter binders
        // (the tag constructor's own telescope, below)
        let idx_bs: Vec<Expr> = pi_binders(&ibs[(n_p as usize).min(ibs.len())..]);
        for j in 0..t.n_idx {
            let mut ctx_j: Vec<Expr> = app2(dup_all(&pbs), &idx_bs[..(j as usize).min(idx_bs.len())]);
            ctx_j.reverse();
            let dom = get_d(&idx_bs, j);
            let lj = kit::idx_sort(ctx.tbl, &ctx_j, &dom).ok_or_else(|| {
                format!(
                    "cannot bound the sort of index {} of {} (the tag's universe)",
                    j,
                    name_str(&t.cv.name)
                )
            })?;
            w = level::max(w, lj);
        }
    }
    let tag_ty = need(
        "tag type",
        expr_ops::replace_pi_body(n_p, &t0.cv.ty, &expr::sort(level::dup(&w))),
    )?;
    let mut tag_ctors: Vec<KCtor> = Vec::new();
    for m in 0..k {
        let t = &b.types[m as usize];
        // `tag.m : ∀ p⃗_1 ı⃗_m, tag p⃗` — the member's index telescope over the
        // first member's parameter binders
        let ty = need(
            "tag constructor type",
            kit::over_first_params(n_p, &t0.cv.ty, &t.cv.ty).and_then(|ty2| {
                expr_ops::replace_pi_body(
                    n_p + t.n_idx,
                    &ty2,
                    &expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(t.n_idx, n_p)),
                )
            }),
        )?;
        tag_ctors.push(KCtor {
            name: tag_ctor_name(&t_name, m),
            n_f: t.n_idx,
            ty,
            rec_idx: Vec::new(),
        });
    }
    let tag_rec_name = kit::nstr(name::dup(&tag), "rec");
    let tag_rec_ty = need(
        "tag recursor type",
        kit::rec_ty(
            &tag, &lps, &elim_tag, true, n_p, 0, &tag_ty, &tag_ctors,
        ),
    )?;
    let mut tag_rlvls: Vec<Level> = vec![level::param(name::dup(&elim_tag))];
    for x in kit::params_of(&lps) {
        tag_rlvls.push(x);
    }
    let mut tag_rules: Vec<RecRule> = Vec::new();
    for m in 0..k {
        let rhs = need(
            "tag rule",
            kit::rec_rhs(
                &tag,
                &lps,
                &elim_tag,
                true,
                n_p,
                0,
                &tag_ty,
                &tag_ctors,
                &tag_rec_name,
                &tag_rlvls,
                m,
            ),
        )?;
        tag_rules.push(env::rec_rule_parsed(
            tag_ctor_name(&t_name, m),
            n_idx_of(m),
            rhs,
        ));
    }
    let mut tag_block: Vec<ConstantInfo> = vec![ConstantInfo::IndInfo(
        ConstantVal {
            name: name::dup(&tag),
            level_params: lps.iter().map(name::dup).collect(),
            ty: tag_ty,
        },
        env::ind_caps_default(),
    )];
    for c in tag_ctors.iter() {
        tag_block.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: name::dup(&c.name),
                level_params: lps.iter().map(name::dup).collect(),
                ty: expr::dup(&c.ty),
            },
            n_p,
            c.n_f,
        ));
    }
    {
        let mut trlps: Vec<Name> = vec![name::dup(&elim_tag)];
        for x in lps.iter() {
            trlps.push(name::dup(x));
        }
        tag_block.push(ConstantInfo::RecInfo(
            ConstantVal {
                name: name::dup(&tag_rec_name),
                level_params: trlps,
                ty: tag_rec_ty,
            },
            n_p + 1 + k,
            n_p + 1 + k,
            tag_rules,
        ));
    }
    out.push(Declaration::IndDecl(tag_block, n_p));
    // 2. the auxiliary family
    let aux_ty = need(
        "aux type",
        expr_ops::replace_pi_body(
            n_p,
            &t0.cv.ty,
            &expr::forall_e(
                expr_ops::mk_app_n(const_p(&tag, &lps), &ps0),
                expr::sort(level::dup(&u)),
                bm(),
            ),
        ),
    )?;
    // `aux.m.C : ∀ p⃗_1 f⃗', aux p⃗ (tag.m p⃗ e⃗)` — the constructor's telescope
    // over the first member's parameter binders, every member occurrence
    // rewritten to the auxiliary family
    let mut aux_ctors: Vec<KCtor> = Vec::new();
    for mc in mctors.iter() {
        let ty = need(
            "aux constructor type",
            kit::over_first_params(
                n_p,
                &t0.cv.ty,
                &kit::spec_fam(&t_name, &lps, n_p, &members, &mc.c.cv.ty),
            ),
        )?;
        aux_ctors.push(KCtor {
            name: kit::aux_ctor_name(&t_name, mc.m, &mc.c.cv.name),
            n_f: mc.c.n_f,
            ty,
            rec_idx: mc.rec_fields.iter().map(|f| f.0).collect(),
        });
    }
    let aux_rec_name = kit::nstr(name::dup(&aux), "rec");
    let aux_rec_ty = need(
        "aux recursor type",
        kit::rec_ty(&aux, &lps, &elim, large, n_p, 1, &aux_ty, &aux_ctors),
    )?;
    let mut aux_rules: Vec<RecRule> = Vec::new();
    for j in 0..n {
        let rhs = need(
            "aux rule",
            kit::rec_rhs(
                &aux,
                &lps,
                &elim,
                large,
                n_p,
                1,
                &aux_ty,
                &aux_ctors,
                &aux_rec_name,
                &rlvls,
                j,
            ),
        )?;
        aux_rules.push(env::rec_rule_parsed(
            name::dup(&aux_ctors[j as usize].name),
            aux_ctors[j as usize].n_f,
            rhs,
        ));
    }
    let mut aux_block: Vec<ConstantInfo> = vec![ConstantInfo::IndInfo(
        ConstantVal {
            name: name::dup(&aux),
            level_params: lps.iter().map(name::dup).collect(),
            ty: aux_ty,
        },
        env::ind_caps_default(),
    )];
    for c in aux_ctors.iter() {
        aux_block.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: name::dup(&c.name),
                level_params: lps.iter().map(name::dup).collect(),
                ty: expr::dup(&c.ty),
            },
            n_p,
            c.n_f,
        ));
    }
    aux_block.push(ConstantInfo::RecInfo(
        ConstantVal {
            name: name::dup(&aux_rec_name),
            level_params: rlps.iter().map(name::dup).collect(),
            ty: aux_rec_ty,
        },
        n_p + 1 + n + 1,
        n_p + 1 + n,
        aux_rules,
    ));
    out.push(Declaration::IndDecl(aux_block, n_p));
    // 3. the member models `T_m._model := λ p⃗ ı⃗, aux p⃗ (tag.m p⃗ ı⃗)`
    for m in 0..k {
        let t = &b.types[m as usize];
        let n_i = t.n_idx;
        let value = need(
            "member model",
            expr_ops::pis_to_lams(
                n_p + n_i,
                &t.cv.ty,
                &expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(
                        vars_at(n_i, n_p),
                        &[expr_ops::mk_app_n(
                            const_p(&tag_ctor_name(&t_name, m), &lps),
                            &app2(vars_at(n_i, n_p), &vars_at(0, n_i)),
                        )],
                    ),
                ),
            ),
        )?;
        let h = {
            let hof = |x: &Name| -> u64 { h_of(&heights, ctx, x) };
            kit::hint_for(&hof, &value)
        };
        heights.insert(0, (model_name(&t.cv.name), kit::hint_height(&h)));
        out.push(Declaration::DefnDecl(
            ConstantVal {
                name: model_name(&t.cv.name),
                level_params: lps.iter().map(name::dup).collect(),
                ty: expr::dup(&t.cv.ty),
            },
            value,
            h,
        ));
    }
    // 4. the constructor models `C._model := λ p⃗ f⃗, aux.m.C p⃗ f⃗`
    for mc in mctors.iter() {
        let n_f = mc.c.n_f;
        let ty = rn(&mc.c.cv.ty);
        let value = need(
            "constructor model",
            expr_ops::pis_to_lams(
                n_p + n_f,
                &ty,
                &expr_ops::mk_app_n(
                    const_p(&kit::aux_ctor_name(&t_name, mc.m, &mc.c.cv.name), &lps),
                    &app2(
                        vars_at(n_f, n_p),
                        &(0..n_f)
                            .map(|i| expr::bvar(sub(sub(n_f, 1), i)))
                            .collect::<Vec<Expr>>(),
                    ),
                ),
            ),
        )?;
        let h = {
            let hof = |x: &Name| -> u64 { h_of(&heights, ctx, x) };
            kit::hint_for(&hof, &value)
        };
        heights.insert(0, (model_name(&mc.c.cv.name), kit::hint_height(&h)));
        out.push(Declaration::DefnDecl(
            ConstantVal {
                name: model_name(&mc.c.cv.name),
                level_params: lps.iter().map(name::dup).collect(),
                ty,
            },
            value,
            h,
        ));
    }
    // 5. the recursor models
    let r_p = n_p + k + n;
    let l_prime: Level = level::imax(level::dup(&u), level::succ(level::dup(&l_elim)));
    for m in 0..k {
        let r = rec_of(m)?;
        let ty = rn(&r.cv.ty);
        let n_i = n_idx_of(m);
        // the body frame: `p⃗ M⃗ S⃗ ı⃗ t` — `rP + nI + 1` binders
        let d = r_p + n_i + 1;
        let e = n_i + 1;
        // `Mot := λ (i : tag p⃗) (s : aux p⃗ i), tag.rec p⃗ (λ i', ∀ s, aux p⃗ i' → Sort ℓ) M⃗ i s`
        let mot_tag: Expr = expr::lam(
            expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(k + n + e + 2, n_p)),
            expr::forall_e(
                expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(vars_at(k + n + e + 3, n_p), &[expr::bvar(0)]),
                ),
                expr::sort(level::dup(&l_elim)),
                bm(),
            ),
            bm(),
        );
        let mut tag_rec_lvls: Vec<Level> = vec![level::dup(&l_prime)];
        for x in kit::params_of(&lps) {
            tag_rec_lvls.push(x);
        }
        let tag_rec_app = expr_ops::mk_app_n(
            expr::mk_const(name::dup(&tag_rec_name), tag_rec_lvls),
            &app2(
                app2(
                    app2(vars_at(k + n + e + 2, n_p), &[mot_tag]),
                    &vars_at(n + e + 2, k),
                ),
                &[expr::bvar(1), expr::bvar(0)],
            ),
        );
        let mot: Expr = expr::lam(
            expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(k + n + e, n_p)),
            expr::lam(
                expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(vars_at(k + n + e + 1, n_p), &[expr::bvar(0)]),
                ),
                tag_rec_app,
                bm(),
            ),
            bm(),
        );
        let body = expr_ops::mk_app_n(
            expr::mk_const(name::dup(&aux_rec_name), rlvls.iter().map(level::dup).collect()),
            &app2(
                app2(
                    app2(vars_at(k + n + e, n_p), &[mot]),
                    &vars_at(e, n),
                ),
                &[
                    expr_ops::mk_app_n(
                        const_p(&tag_ctor_name(&t_name, m), &lps),
                        &app2(vars_at(k + n + e, n_p), &vars_at(1, n_i)),
                    ),
                    expr::bvar(0),
                ],
            ),
        );
        let value = need("recursor model", expr_ops::pis_to_lams(d, &ty, &body))?;
        let h = {
            let hof = |x: &Name| -> u64 { h_of(&heights, ctx, x) };
            kit::hint_for(&hof, &value)
        };
        heights.insert(0, (model_name(&r.cv.name), kit::hint_height(&h)));
        out.push(Declaration::DefnDecl(
            ConstantVal {
                name: model_name(&r.cv.name),
                level_params: rlps.iter().map(name::dup).collect(),
                ty,
            },
            value,
            h,
        ));
    }
    // 6. the iota theorems, by `Eq.refl`
    for m in 0..k {
        let r = rec_of(m)?;
        let (prefix_bs, _) = expr_ops::strip_pis(r_p, &rn(&r.cv.ty)).ok_or_else(|| {
            format!(
                "recursor {}: type is not the expected telescope",
                name_str(&r.cv.name)
            )
        })?;
        let own: Vec<&MCtor> = mctors.iter().filter(|mc| mc.m == m).collect();
        for j in 0..own.len() as u64 {
            let mc = own[j as usize];
            let n_f = mc.c.n_f;
            // the constructor's global minor index
            let big_j: u64 = mctors
                .iter()
                .position(|x| name::beq(&x.c.cv.name, &mc.c.cv.name))
                .map(|p| p as u64)
                .unwrap_or(0);
            let (_, ctele) = expr_ops::strip_pis(n_p, &rn(&mc.c.cv.ty)).ok_or_else(|| {
                format!(
                    "constructor {}: type is not a telescope",
                    name_str(&mc.c.cv.name)
                )
            })?;
            // the field telescope at the statement frame: the parameters sit
            // above the `k + n` motive and minor binders
            let (field_bs, cresid) =
                expr_ops::strip_pis(n_f, &expr_ops::lift_loose_bvars(k + n, 0, &ctele))
                    .ok_or_else(|| {
                        format!("constructor {}: field telescope", name_str(&mc.c.cv.name))
                    })?;
            let doms = pi_binders(&field_bs);
            let fields: Vec<Expr> = (0..n_f).map(|i| expr::bvar(sub(sub(n_f, 1), i))).collect();
            let prefix_vars = app2(
                app2(vars_at(n_f + k + n, n_p), &vars_at(n_f + n, k)),
                &vars_at(n_f, n),
            );
            let ctor_app = expr_ops::mk_app_n(
                const_p(&model_name(&mc.c.cv.name), &lps),
                &app2(vars_at(n_f + k + n, n_p), &fields),
            );
            // the constructor's index expressions, at the statement frame
            let idx_c: Vec<Expr> = expr_ops::get_app_args(&cresid)
                .into_iter()
                .skip(n_p as usize)
                .collect();
            let alpha: Expr = expr_ops::mk_app_n(
                expr::bvar(sub(sub(n_f + n + k, 1), m)),
                &app2(dup_all(&idx_c), &[expr::dup(&ctor_app)]),
            );
            let lhs = expr_ops::mk_app_n(
                expr::mk_const(model_name(&r.cv.name), rlvls.iter().map(level::dup).collect()),
                &app2(
                    app2(dup_all(&prefix_vars), &idx_c),
                    &[expr::dup(&ctor_app)],
                ),
            );
            let mut rhs_args = dup_all(&fields);
            for (i, tgt) in mc.rec_fields.iter() {
                // the recursive field's index expressions, lifted from its
                // binder to the statement frame
                let idx_i: Vec<Expr> = expr_ops::get_app_args(&expr_ops::lift_loose_bvars(
                    sub(n_f, *i),
                    0,
                    &get_d(&doms, *i),
                ))
                .into_iter()
                .skip(n_p as usize)
                .collect();
                let rec_model = model_name(&kit::nstr(
                    match member_names.get(*tgt as usize) {
                        Some(nm) => name::dup(nm),
                        None => name::anonymous(),
                    },
                    "rec",
                ));
                rhs_args.push(expr_ops::mk_app_n(
                    expr::mk_const(rec_model, rlvls.iter().map(level::dup).collect()),
                    &app2(
                        app2(dup_all(&prefix_vars), &idx_i),
                        &[expr::bvar(sub(sub(n_f, 1), *i))],
                    ),
                ));
            }
            let rhs = expr_ops::mk_app_n(expr::bvar(sub(sub(n_f + n, 1), big_j)), &rhs_args);
            let stmt = mk_pis(
                &app2(pi_binders(&prefix_bs), &pi_binders(&field_bs)),
                expr_ops::mk_app_n(
                    expr::mk_const(bnm::eq_name(), vec![level::dup(&l_elim)]),
                    &vec![expr::dup(&alpha), expr::dup(&lhs), rhs],
                ),
            );
            let value = need(
                "iota proof",
                expr_ops::pis_to_lams(
                    r_p + n_f,
                    &stmt,
                    &expr_ops::mk_app_n(
                        expr::mk_const(bnm::eq_refl_name(), vec![level::dup(&l_elim)]),
                        &vec![alpha, lhs],
                    ),
                ),
            )?;
            out.push(Declaration::ThmDecl(
                ConstantVal {
                    name: iota_name(&r.cv.name, j),
                    level_params: rlps.iter().map(name::dup).collect(),
                    ty: stmt,
                },
                value,
            ));
        }
    }
    // 7. projection artifacts of structure-like non-`Prop` members — only
    // under a LARGE eliminator: the artifact is the model recursor at the
    // field's sort (`projRecValue` instantiates the elimination level), and a
    // block at a possibly-zero sort eliminates into `Prop` only.  Nothing is
    // lost: official's `is_structure_like` is single-type, so a mutual member
    // never carries `.proj`; the artifacts only feed the projection rewrite's
    // levels.
    let mut gen_types: Vec<(Name, Vec<Name>, Expr)> = Vec::new();
    for t in b.types.iter() {
        gen_types.push((
            model_name(&t.cv.name),
            lps.iter().map(name::dup).collect(),
            expr::dup(&t.cv.ty),
        ));
    }
    for c in b.ctors.iter() {
        gen_types.push((
            model_name(&c.cv.name),
            lps.iter().map(name::dup).collect(),
            rn(&c.cv.ty),
        ));
    }
    let tbl2 = |x: &Name| -> Option<(Vec<Name>, Expr)> {
        match gen_types.iter().find(|g| name::beq(&g.0, x)) {
            Some((_, l, ty)) => Some((l.iter().map(name::dup).collect(), expr::dup(ty))),
            None => (ctx.tbl)(x),
        }
    };
    if !is_prop && large {
        for m in 0..k {
            let t = &b.types[m as usize];
            let own: Vec<&MCtor> = mctors.iter().filter(|mc| mc.m == m).collect();
            if own.len() != 1 {
                continue;
            }
            let mc = own[0];
            if t.n_idx != 0 {
                continue;
            }
            let n_f = mc.c.n_f;
            let cty = rn(&mc.c.cv.ty);
            let r = rec_of(m)?;
            let owner = proj_rec::ProjRecOwner {
                t: model_name(&t.cv.name),
                lps: lps.iter().map(name::dup).collect(),
                n_p,
                ctor: model_name(&mc.c.cv.name),
                n_f,
                rec_name: model_name(&r.cv.name),
                rec_lps: rlps.iter().map(name::dup).collect(),
                rec_type: rn(&r.cv.ty),
                num_motives: k,
                num_minors: n,
            };
            let cbs = match expr_ops::strip_pis(n_p + n_f, &cty) {
                Some((cbs, _)) => cbs,
                None => continue,
            };
            let mut stop = false;
            for i in 0..n_f {
                if stop {
                    continue;
                }
                // the field's sort, at the constructor frame
                let mut ctx_i = pi_binders(&cbs[..((n_p + i) as usize).min(cbs.len())]);
                ctx_i.reverse();
                let dom = get_d(&pi_binders(&cbs), n_p + i);
                let li = match kit::sort_of(&tbl2, &ctx_i, &dom) {
                    Some(l) => l,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                // the projection type `∀ p⃗ (x : T._model p⃗), F_i[f_j := proj_j p⃗ x]`
                let mut args = struct_parts::struct_proj_ps(n_p);
                for j in 0..i {
                    args.push(expr_ops::mk_app_n(
                        const_p(&core_k::proj_model_name(&t.cv.name, j), &lps),
                        &app2(struct_parts::struct_proj_ps(n_p), &[expr::bvar(0)]),
                    ));
                }
                let fdom = match expr_ops::inst_pis_at_lift(&args, &cty) {
                    Some(e) => match expr::view(&e) {
                        ExprView::ForallE(fdom, _, _) => expr::dup(fdom),
                        _ => {
                            stop = true;
                            continue;
                        }
                    },
                    None => {
                        stop = true;
                        continue;
                    }
                };
                let pty = match expr_ops::replace_pi_body(
                    n_p,
                    &t.cv.ty,
                    &expr::forall_e(
                        expr_ops::mk_app_n(const_p(&model_name(&t.cv.name), &lps), &ps0),
                        fdom,
                        bm(),
                    ),
                ) {
                    Some(e) => e,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                let pbs_prime = match expr_ops::strip_pis(n_p + 1, &pty) {
                    Some((bs, _)) => bs,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                let dummy = mk_lams(
                    &pi_binders(&pbs_prime),
                    expr::proj(model_name(&t.cv.name), i, expr::bvar(0)),
                );
                let pval = match proj_rec::proj_rec_value(&owner, &li, &pty, &dummy, i) {
                    Some(v) => v,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                let h = {
                    let hof = |x: &Name| -> u64 { h_of(&heights, ctx, x) };
                    kit::hint_for(&hof, &pval)
                };
                heights.insert(
                    0,
                    (
                        core_k::proj_model_name(&t.cv.name, i),
                        kit::hint_height(&h),
                    ),
                );
                out.push(Declaration::DefnDecl(
                    ConstantVal {
                        name: core_k::proj_model_name(&t.cv.name, i),
                        level_params: lps.iter().map(name::dup).collect(),
                        ty: pty,
                    },
                    pval,
                    h,
                ));
                // `proj_i.iota : ∀ p⃗ f⃗, proj_i p⃗ (C._model p⃗ f⃗) = f_i`
                let fields: Vec<Expr> =
                    (0..n_f).map(|l| expr::bvar(sub(sub(n_f, 1), l))).collect();
                let slot = expr_ops::lift_loose_bvars(sub(n_f, i), 0, &dom);
                let lhs = expr_ops::mk_app_n(
                    const_p(&core_k::proj_model_name(&t.cv.name, i), &lps),
                    &app2(
                        vars_at(n_f, n_p),
                        &[expr_ops::mk_app_n(
                            const_p(&model_name(&mc.c.cv.name), &lps),
                            &app2(vars_at(n_f, n_p), &fields),
                        )],
                    ),
                );
                let stmt = mk_pis(
                    &pi_binders(&cbs),
                    expr_ops::mk_app_n(
                        expr::mk_const(bnm::eq_name(), vec![level::dup(&li)]),
                        &vec![
                            expr::dup(&slot),
                            lhs,
                            expr::bvar(sub(sub(n_f, 1), i)),
                        ],
                    ),
                );
                let pf = match expr_ops::pis_to_lams(
                    n_p + n_f,
                    &stmt,
                    &expr_ops::mk_app_n(
                        expr::mk_const(bnm::eq_refl_name(), vec![level::dup(&li)]),
                        &vec![slot, expr::bvar(sub(sub(n_f, 1), i))],
                    ),
                ) {
                    Some(v) => v,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                out.push(Declaration::ThmDecl(
                    ConstantVal {
                        name: kit::nstr(core_k::proj_model_name(&t.cv.name, i), "iota"),
                        level_params: lps.iter().map(name::dup).collect(),
                        ty: stmt,
                    },
                    pf,
                ));
            }
        }
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/InModel/Mutual.lean:160-452 genMutual
/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The `hOf` of both generators: the height of a constant, the definitions
/// emitted by this block first (they are not in `ctx` yet), else the parse
/// state's table.
pub fn h_of(heights: &[(Name, u64)], ctx: &Ctx, x: &Name) -> u64 {
    match heights.iter().find(|e| name::beq(&e.0, x)) {
        Some((_, h)) => *h,
        None => (ctx.heights)(x),
    }
}
