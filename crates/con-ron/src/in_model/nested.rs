//! `ConLeche/Frontend/InModel/Nested.lean` — in-process models of a NESTED
//! (or nested-and-mutual) block, the nested rung fused with the mutual one:
//! the kernel's own nested→mutual reduction is READ OFF THE EXPORTED RECURSOR
//! FAMILY instead of being re-derived, the auxiliary family has one member
//! per motive, and the public slots go through an isomorphism per mimic
//! (`pack`/`unpack`, `unpackPack`/`packUnpack`, the congruences).
//!
//! Declines (the residual) and the one KNOWN GAP are the cited module
//! header's; nothing here is trusted, and every record is checked by the fold
//! like any stream declaration.
//!
//! Deviations beyond `kit`'s and `mutual`'s:
//!
//! * **`genNested`'s ~40 local `let f := fun …` definitions become methods of
//!   a `Gen` record** (and the iota proof's five become an `Iota` one).  Lean
//!   closes them over `genNested`'s locals for free; Rust closures that call
//!   each other and recurse (`nest`, `goT`, the `congrChain` go) cannot, so
//!   the captured locals are the struct's fields and each closure is a method
//!   with the same name and the same arguments.  The cited line range is the
//!   whole `genNested`, since that is where every one of them lives.
//! * **`zs`/`hs` of the iota proof's generalisation are `&[Option<Expr>]`**
//!   indexed by field position, where con-leche passes `Nat → Option Expr`:
//!   every caller indexes them by a field position below `nF`, so the slice
//!   is the same function tabulated.
//! * `readMems`/`readCtors` return `Result<_, String>` and the `Mem`/`ACtor`
//!   field `I` is `i_name` (`I` is not a Rust identifier convention and
//!   `Self` is taken).

use con_ron_core::kernel::env::Declaration;
use con_ron_core::kernel::basis_names as bnm;
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, RecRule, ReducibilityHint};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprView};
use con_ron_core::kernel::expr_ops;
use crate::tree::struct_parts;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

use crate::render::name_str;
use crate::in_model::kit;
use crate::in_model::kit::{
    app2, bm, const_p, dup_all, dup_names, get_d, impl_name, iota_name, lift_all_n, mentions_any,
    mk_lams, mk_pis, model_name, pi_binders, sub, tag_ctor_name, vars_at, KCtor,
};
use crate::in_model::mutual::{need, BlockRec, Ctx, IndRecRec};

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:69-89 Mem
/// A member of the auxiliary family: a real member of the block or a mimic (a
/// nested occurrence `I As`, the container at its pins).
pub struct Mem {
    /// position among the motives
    pub tag: u64,
    /// the block member (`Some m`) or the mimic ordinal (`None`, see `j`)
    pub real: Option<u64>,
    /// mimic ordinal (0-based; meaningful when `real = None`)
    pub j: u64,
    /// the carrier's head: `T_m` at a real member, the container `I` at a mimic
    pub i_name: Name,
    /// the carrier's levels
    pub lv: Vec<Level>,
    /// the pins (the container's parameters), at the parameter frame; empty at
    /// a real member (whose parameters are the block's)
    pub pins: Vec<Expr>,
    /// the index count
    pub n_idx: u64,
    /// the index telescope, at the parameter frame
    pub idx_bs: Vec<Expr>,
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:91-110 ACtor
/// One constructor of the auxiliary family.
pub struct ACtor {
    /// the member it belongs to
    pub mem: u64,
    /// the public constructor name (the container's at a mimic) and levels
    pub cname: Name,
    pub clv: Vec<Level>,
    /// field count
    pub n_f: u64,
    /// the field binders, each at its own frame over the parameter frame
    pub doms: Vec<Expr>,
    /// per field: the member it recurses to, or `None`
    pub kinds: Vec<Option<u64>>,
    /// the residual's index expressions, at the fields' frame
    pub idx: Vec<Expr>,
    /// the global minor index
    pub big_j: u64,
    /// the rule index within the member's recursor
    pub j_in: u64,
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:112-124 Group
/// A container group (B4): the mimics that are one container's recursor family
/// instantiated at the pins, in the container's motive order, with each
/// member's recursor name; `lv`/`pins` are the container's levels and pins
/// (shared by the group), `large` whether its recursors carry an elimination
/// level.
pub struct Group {
    pub tags: Vec<u64>,
    pub rec_names: Vec<Name>,
    pub lv: Vec<Level>,
    pub pins: Vec<Expr>,
    pub n_pi: u64,
    pub large: bool,
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:126-140 Family
/// The family read off the block.
pub struct Family {
    pub t: Name,
    pub lps: Vec<Name>,
    pub n_p: u64,
    /// the parameter binders (from the first former)
    pub pbs: Vec<Expr>,
    pub u: Level,
    /// the real member count
    pub r: u64,
    pub mems: Vec<Mem>,
    pub ctors: Vec<ACtor>,
    pub large: bool,
    pub elim: Name,
}

// ---------------------------------------------------------------------------
// Carriers and the family rewrite (`Nested.lean:143-251`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:144-154 carrierAt
/// Member `mem`'s carrier at `o` binders below the parameter frame, at index
/// arguments `idx`; `model` renames a real member to its model.
pub fn carrier_at(fam: &Family, mem: &Mem, o: u64, idx: &[Expr], model: bool) -> Expr {
    match mem.real {
        Some(_) => expr_ops::mk_app_n(
            expr::mk_const(
                if model {
                    model_name(&mem.i_name)
                } else {
                    name::dup(&mem.i_name)
                },
                mem.lv.iter().map(level::dup).collect(),
            ),
            &app2(vars_at(o, fam.n_p), idx),
        ),
        None => {
            let pins: Vec<Expr> = mem
                .pins
                .iter()
                .map(|p| {
                    let p = expr_ops::lift_loose_bvars(o, 0, p);
                    if model {
                        expr_ops::rename_consts(
                            &kit::RenameFn(|x: &Name| {
                                if fam
                                    .mems
                                    .iter()
                                    .any(|m| m.real.is_some() && name::beq(&m.i_name, x))
                                {
                                    model_name(x)
                                } else {
                                    name::dup(x)
                                }
                            }),
                            &p,
                        )
                    } else {
                        p
                    }
                })
                .collect();
            expr_ops::mk_app_n(
                expr::mk_const(
                    name::dup(&mem.i_name),
                    mem.lv.iter().map(level::dup).collect(),
                ),
                &app2(pins, idx),
            )
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:156-159 auxAt
/// `aux p⃗ (tag.mem p⃗ idx)` at `o` binders below the parameter frame.
pub fn aux_at(fam: &Family, tag: u64, o: u64, idx: &[Expr]) -> Expr {
    expr_ops::mk_app_n(
        const_p(&kit::aux_name(&fam.t), &fam.lps),
        &app2(
            vars_at(o, fam.n_p),
            &[expr_ops::mk_app_n(
                const_p(&tag_ctor_name(&fam.t, tag), &fam.lps),
                &app2(vars_at(o, fam.n_p), idx),
            )],
        ),
    )
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:161-182 matchCarrier
/// Is `e`, at `o` binders below the parameter frame, a member's carrier at
/// some index arguments?  Returns the member's tag and the index arguments.
pub fn match_carrier(fam: &Family, o: u64, e: &Expr) -> Option<(u64, Vec<Expr>)> {
    let f = expr_ops::get_app_fn(e);
    match expr::view(&f) {
        ExprView::Const(x, us) => {
            let args = expr_ops::get_app_args(e);
            fam.mems.iter().find_map(|mem| {
                if !name::beq(&mem.i_name, x) || !expr::levels_beq(us, &mem.lv) {
                    return None;
                }
                match mem.real {
                    Some(_) => {
                        if args.len() as u64 == fam.n_p + mem.n_idx
                            && expr::exprs_beq(
                                &dup_all(&args[..(fam.n_p as usize).min(args.len())]),
                                &vars_at(o, fam.n_p),
                            )
                        {
                            Some((
                                mem.tag,
                                dup_all(&args[(fam.n_p as usize).min(args.len())..]),
                            ))
                        } else {
                            None
                        }
                    }
                    None => {
                        let n_pi = mem.pins.len();
                        if args.len() == n_pi + mem.n_idx as usize
                            && expr::exprs_beq(
                                &dup_all(&args[..n_pi.min(args.len())]),
                                &lift_all_n(o, &mem.pins),
                            )
                        {
                            Some((mem.tag, dup_all(&args[n_pi.min(args.len())..])))
                        } else {
                            None
                        }
                    }
                }
            })
        }
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:186-235 specAllGo
/// Rewrite every whole carrier occurrence into the auxiliary family (`o`
/// binders below the parameter frame at entry).  One memoized DAG walk, keyed
/// by the node and the binder offset `o` (which shifts under binders, so a
/// node's answer is not a function of the node alone), and dropped after each
/// call.  Without the memo the rebuild runs once per path —
/// `tests/e2e/tower_nested.ndjson`.
pub fn spec_all_go(
    fam: &Family,
    memo: &mut std::collections::HashMap<(crate::keys::ExprKey, u64), Expr>,
    o: u64,
    e: &Expr,
) -> Expr {
    if let Some((tag, idx)) = match_carrier(fam, o, e) {
        let idx2 = spec_all_go_list(fam, memo, o, &idx);
        return aux_at(fam, tag, o, &idx2);
    }
    match expr::view(&e) {
        ExprView::Bvar(_) | ExprView::Sort(_) | ExprView::Fvar(_, _) | ExprView::Const(_, _)
        | ExprView::Lit(_) => expr::dup(e),
        _ => {
            let key = (
                crate::keys::ExprKey(expr::dup(e)),
                o,
            );
            if let Some(r) = memo.get(&key) {
                return expr::dup(r);
            }
            let r = match expr::view(&e) {
                ExprView::App(f, a) => {
                    let f2 = spec_all_go(fam, memo, o, f);
                    let a2 = spec_all_go(fam, memo, o, a);
                    expr::app(f2, a2)
                }
                ExprView::Lam(d, b, m) => {
                    let d2 = spec_all_go(fam, memo, o, d);
                    let b2 = spec_all_go(fam, memo, o + 1, b);
                    expr::lam(d2, b2, expr::binder_meta_dup(m))
                }
                ExprView::ForallE(d, b, m) => {
                    let d2 = spec_all_go(fam, memo, o, d);
                    let b2 = spec_all_go(fam, memo, o + 1, b);
                    expr::forall_e(d2, b2, expr::binder_meta_dup(m))
                }
                ExprView::LetE(t, v, b) => {
                    let t2 = spec_all_go(fam, memo, o, t);
                    let v2 = spec_all_go(fam, memo, o, v);
                    let b2 = spec_all_go(fam, memo, o + 1, b);
                    expr::let_e(t2, v2, b2)
                }
                ExprView::Proj(s, i, x) => {
                    let x2 = spec_all_go(fam, memo, o, x);
                    expr::proj(name::dup(s), *i, x2)
                }
                _ => expr::dup(e),
            };
            memo.insert(key, expr::dup(&r));
            r
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:237-244 specAllGoList
/// `spec_all_go` over a list, threading the memo.
pub fn spec_all_go_list(
    fam: &Family,
    memo: &mut std::collections::HashMap<(crate::keys::ExprKey, u64), Expr>,
    o: u64,
    es: &[Expr],
) -> Vec<Expr> {
    es.iter().map(|e| spec_all_go(fam, memo, o, e)).collect()
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:248-250 specAll
/// `spec_all_go` at a fresh memo.
pub fn spec_all(fam: &Family, o: u64, e: &Expr) -> Expr {
    let mut memo = std::collections::HashMap::new();
    spec_all_go(fam, &mut memo, o, e)
}

// ---------------------------------------------------------------------------
// Reading the family off the recursor (`Nested.lean:253-351`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:254-258 stripAllPis
/// Strip every leading `∀`, returning binders and body.
pub fn strip_all_pis(e: &Expr) -> (Vec<(Expr, expr::BinderMeta)>, Expr) {
    let mut bs: Vec<(Expr, expr::BinderMeta)> = Vec::new();
    let mut cur = expr::dup(e);
    loop {
        let next = match expr::view(&cur) {
            ExprView::ForallE(d, b, m) => {
                bs.push((expr::dup(d), expr::binder_meta_dup(m)));
                expr::dup(b)
            }
            _ => return (bs, cur),
        };
        cur = next;
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:260-303 readMems
/// Read the members off the motives of the first recursor's type (after the
/// parameters): motive `m`'s domain `∀ ı⃗ (t : C), Sort ℓ`.
pub fn read_mems(
    lps: &[Name],
    n_p: u64,
    types: &[crate::in_model::mutual::IndTypeRec],
    motives: &[Expr],
) -> Result<Vec<Mem>, String> {
    let r = types.len() as u64;
    let member_names: Vec<Name> = types.iter().map(|t| name::dup(&t.cv.name)).collect();
    let mut out: Vec<Mem> = Vec::new();
    for m in 0..motives.len() as u64 {
        // motive `m`'s domain sits under the `m` earlier motive binders, which
        // it never mentions: lower it to the parameter frame
        let dom = expr_ops::lower_bvars(m, 0, &get_d(motives, m));
        let (bs, body) = strip_all_pis(&dom);
        if !matches!(expr::view(&body), ExprView::Sort(_)) {
            return Err(format!("motive {} does not end in a sort", m));
        }
        let carr = match bs.last() {
            Some((d, _)) => expr::dup(d),
            None => return Err(format!("motive {} has no major binder", m)),
        };
        let n_idx = sub(bs.len() as u64, 1);
        let idx_bs = pi_binders(&bs[..(n_idx as usize).min(bs.len())]);
        let head = expr_ops::get_app_fn(&carr);
        let (i_name, us) = match expr::view(&head) {
            ExprView::Const(i, us) => (name::dup(i), us.iter().map(level::dup).collect::<Vec<_>>()),
            _ => return Err(format!("motive {}: carrier head is not a constant", m)),
        };
        let args = expr_ops::get_app_args(&carr);
        if m < r {
            // a real member, in order
            let want = get_name(&member_names, m);
            if !name::beq(&i_name, &want) {
                return Err(format!("motive {} is not member {}", m, name_str(&want)));
            }
            if !kit::levels_are_params(&us, lps)
                || !expr::exprs_beq(&args, &app2(vars_at(n_idx, n_p), &vars_at(0, n_idx)))
            {
                return Err(format!(
                    "motive {}: the member's carrier is not at its parameters and indices",
                    m
                ));
            }
            if types[m as usize].n_idx != n_idx {
                return Err(format!(
                    "motive {}: index count differs from the member's",
                    m
                ));
            }
            out.push(Mem {
                tag: m,
                real: Some(m),
                j: 0,
                i_name,
                lv: us,
                pins: Vec::new(),
                n_idx,
                idx_bs,
            });
        } else {
            if member_names.iter().any(|x| name::beq(x, &i_name)) {
                return Err(format!("motive {}: a member's carrier among the mimics", m));
            }
            if !(args.len() as u64 >= n_idx
                && expr::exprs_beq(
                    &dup_all(&args[(sub(args.len() as u64, n_idx) as usize).min(args.len())..]),
                    &vars_at(0, n_idx),
                ))
            {
                return Err(format!(
                    "motive {}: the mimic's carrier does not end in its index variables",
                    m
                ));
            }
            let cut = (sub(args.len() as u64, n_idx) as usize).min(args.len());
            let pins: Vec<Expr> = dup_all(&args[..cut]);
            // the pins live at the parameter frame: no index variable in them
            let pins_p: Vec<Expr> = pins
                .iter()
                .map(|p| expr_ops::lower_bvars(n_idx, 0, p))
                .collect();
            if !expr::exprs_beq(&lift_all_n(n_idx, &pins_p), &pins) {
                return Err(format!("motive {}: a pin mentions an index variable", m));
            }
            out.push(Mem {
                tag: m,
                real: None,
                j: sub(m, r),
                i_name,
                lv: us,
                pins: pins_p,
                n_idx,
                idx_bs,
            });
        }
    }
    Ok(out)
}

/// con-leche: none — `ns.getD i .anonymous`, a `Name` list's out-of-range
/// guard (`memberNames.getD m .anonymous`).
pub fn get_name(ns: &[Name], i: u64) -> Name {
    match ns.get(i as usize) {
        Some(n) => name::dup(n),
        None => name::anonymous(),
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:305-350 readCtors
/// Read the constructors off the minors: minor `J`'s domain
/// `∀ f⃗ ih⃗, motive_m e⃗ (C As f⃗)`, `nF` from the rules.
pub fn read_ctors(
    fam: &Family,
    big_m: u64,
    minors: &[Expr],
    n_f_of: &dyn Fn(&Name, u64) -> Result<u64, String>,
) -> Result<Vec<ACtor>, String> {
    let mut out: Vec<ACtor> = Vec::new();
    let mut per_mem: Vec<u64> = fam.mems.iter().map(|_| 0).collect();
    for big_j in 0..minors.len() as u64 {
        let dom = get_d(minors, big_j);
        let (bs, body) = strip_all_pis(&dom);
        // the motive: `bvar (bs.length + J + (M - 1 - m))`
        let head = expr_ops::get_app_fn(&body);
        let mv = match expr::view(&head) {
            ExprView::Bvar(i) => *i,
            _ => {
                return Err(format!(
                    "minor {}: codomain head is not a motive",
                    big_j
                ))
            }
        };
        if !(mv >= bs.len() as u64 + big_j && mv < bs.len() as u64 + big_j + big_m) {
            return Err(format!("minor {}: codomain head is not a motive", big_j));
        }
        let mem = sub(sub(big_m, 1), sub(sub(mv, bs.len() as u64), big_j));
        let margs = expr_ops::get_app_args(&body);
        let capp = match margs.last() {
            Some(e) => expr::dup(e),
            None => return Err(format!("minor {}: no major", big_j)),
        };
        let chead = expr_ops::get_app_fn(&capp);
        let (cname, clv) = match expr::view(&chead) {
            ExprView::Const(c, us) => {
                (name::dup(c), us.iter().map(level::dup).collect::<Vec<_>>())
            }
            _ => {
                return Err(format!(
                    "minor {}: major head is not a constructor",
                    big_j
                ))
            }
        };
        let n_f = n_f_of(&cname, mem)?;
        if n_f > bs.len() as u64 {
            return Err(format!("minor {}: fewer binders than fields", big_j));
        }
        let n_ih = sub(bs.len() as u64, n_f);
        // the field domains, lowered to the parameter frame (the motives and
        // earlier minors sit between the parameters and the fields)
        // (head-β-reduced: a container at a dependent pin `I α (fun _ => T α)`
        // leaves `(fun _ => T α) k` in the kernel's minor)
        let doms: Vec<Expr> = (0..n_f)
            .map(|i| {
                let d = match bs.get(i as usize) {
                    Some((d, _)) => expr::dup(d),
                    None => expr::bvar(0),
                };
                kit::beta_head(&expr_ops::lower_bvars(big_m + big_j, i, &d))
            })
            .collect();
        // the kinds, by the carrier match at each field's frame
        let kinds: Vec<Option<u64>> = (0..n_f)
            .map(|i| match_carrier(fam, i, &get_d(&doms, i)).map(|x| x.0))
            .collect();
        let n_rec = kinds.iter().filter(|k| k.is_some()).count() as u64;
        if n_rec != n_ih {
            return Err(format!(
                "minor {} ({}): {} inductive hypotheses for {} recursive fields",
                big_j,
                name_str(&cname),
                n_ih,
                n_rec
            ));
        }
        // every other field must not mention the block at all
        let member_names: Vec<Name> = fam
            .mems
            .iter()
            .filter_map(|m| {
                if m.real.is_some() {
                    Some(name::dup(&m.i_name))
                } else {
                    None
                }
            })
            .collect();
        for i in 0..n_f {
            if kinds[i as usize].is_none() && mentions_any(&member_names, &get_d(&doms, i)) {
                return Err(format!(
                    "field {} of {} mentions the block other than as a whole member or \
                     container occurrence (nested under a binder)",
                    i,
                    name_str(&cname)
                ));
            }
        }
        // the residual's index expressions at the fields' frame
        let idx: Vec<Expr> = margs[..sub(margs.len() as u64, 1) as usize]
            .iter()
            .map(|e| {
                expr_ops::lower_bvars(
                    big_m + big_j,
                    n_f,
                    &expr_ops::lower_bvars(n_ih, 0, e),
                )
            })
            .collect();
        let j_in = *per_mem.get(mem as usize).unwrap_or(&0);
        if (mem as usize) < per_mem.len() {
            per_mem[mem as usize] = j_in + 1;
        }
        out.push(ACtor {
            mem,
            cname,
            clv,
            n_f,
            doms,
            kinds,
            idx,
            big_j,
            j_in,
        });
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Emission helpers (`Nested.lean:353-397`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:354-355 mkEq
/// `Eq.{ℓ} α a b`.
pub fn mk_eq(l: &Level, alpha: Expr, a: Expr, b: Expr) -> Expr {
    expr_ops::mk_app_n(
        expr::mk_const(bnm::eq_name(), vec![level::dup(l)]),
        &vec![alpha, a, b],
    )
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:357-358 mkRefl
/// `Eq.refl.{ℓ} α a`.
pub fn mk_refl(l: &Level, alpha: Expr, a: Expr) -> Expr {
    expr_ops::mk_app_n(
        expr::mk_const(bnm::eq_refl_name(), vec![level::dup(l)]),
        &vec![alpha, a],
    )
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:360-362 mkEqRec
/// `@Eq.rec.{ℓm, ℓα} α a motive refl b h`.
pub fn mk_eq_rec(
    lm: &Level,
    la: &Level,
    alpha: Expr,
    a: Expr,
    motive: Expr,
    refl: Expr,
    b: Expr,
    h: Expr,
) -> Expr {
    expr_ops::mk_app_n(
        expr::mk_const(
            kit::nstr(bnm::eq_name(), "rec"),
            vec![level::dup(lm), level::dup(la)],
        ),
        &vec![alpha, a, motive, refl, b, h],
    )
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:364-365 liftAll
/// Lift every entry.
pub fn lift_all(n: u64, es: &[Expr]) -> Vec<Expr> {
    lift_all_n(n, es)
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:367-396 congrChain
/// The congruence chain (Prop motives): given a spine builder `F` (closed over
/// the current frame), argument lists `l⃗`, `r⃗` (equal at unmoved positions),
/// the moved positions with their equations `e_k : l_k = r_k` and their types,
/// a proof of `F l⃗ = F r⃗`.  `α`/`ℓα` are the spine's type and its sort.
pub fn congr_chain(
    la: &Level,
    alpha: &Expr,
    f: &dyn Fn(u64, &[Expr]) -> Expr,
    ls: &[Expr],
    rs: &[Expr],
    moved: &[(u64, Expr, Expr, Level)],
) -> Expr {
    congr_chain_go(la, alpha, f, ls, rs, moved, 0)
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:367-396 congrChain
/// The cited `where go`.
pub fn congr_chain_go(
    la: &Level,
    alpha: &Expr,
    f: &dyn Fn(u64, &[Expr]) -> Expr,
    ls: &[Expr],
    rs: &[Expr],
    moved: &[(u64, Expr, Expr, Level)],
    k: u64,
) -> Expr {
    match moved.get(k as usize) {
        None => mk_refl(la, expr::dup(alpha), f(0, ls)),
        Some((pos, e, ty, l_ty)) => {
            // `S'_k`: the first `k` moved positions at `l`, the later ones at
            // `r` (unmoved positions agree)
            let mid: Vec<Expr> = (0..ls.len() as u64)
                .map(|i| {
                    if moved[(k as usize).min(moved.len())..]
                        .iter()
                        .any(|x| x.0 == i)
                    {
                        get_d(rs, i)
                    } else {
                        get_d(ls, i)
                    }
                })
                .collect();
            let mut mid2 = lift_all(2, &mid);
            if (*pos as usize) < mid2.len() {
                mid2[*pos as usize] = expr::bvar(1);
            }
            let motive: Expr = expr::lam(
                expr::dup(ty),
                expr::lam(
                    mk_eq(
                        l_ty,
                        expr_ops::lift_loose_bvars(1, 0, ty),
                        expr_ops::lift_loose_bvars(1, 0, &get_d(ls, *pos)),
                        expr::bvar(0),
                    ),
                    mk_eq(
                        la,
                        expr_ops::lift_loose_bvars(2, 0, alpha),
                        f(2, &lift_all(2, ls)),
                        f(2, &mid2),
                    ),
                    bm(),
                ),
                bm(),
            );
            mk_eq_rec(
                &level::zero(),
                l_ty,
                expr::dup(ty),
                get_d(ls, *pos),
                motive,
                congr_chain_go(la, alpha, f, ls, rs, moved, k + 1),
                get_d(rs, *pos),
                expr::dup(e),
            )
        }
    }
}

// ---------------------------------------------------------------------------
// The nested rung (`Nested.lean:399-1317`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The shared builders of `genNested`: every one of the cited function's local
/// `let f := fun …` definitions, as methods over the locals they close over
/// (the module note's first deviation).
pub struct Gen<'a> {
    pub fam: &'a Family,
    /// `M`, the motive count
    pub big_m: u64,
    /// `n`, the minor count
    pub n: u64,
    pub tag: Name,
    pub aux: Name,
    /// `ℓ`, the elimination level
    pub l: Level,
    pub rlps: Vec<Name>,
    pub rlvls: Vec<Level>,
    pub block_names: Vec<Name>,
    pub member_names: Vec<Name>,
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The builders themselves; each method is the cited function's `let` of the
/// same name, with the same arguments.
impl<'a> Gen<'a> {
    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `rnF`: a block name becomes its model.
    pub fn rn_name(&self, x: &Name) -> Name {
        if self.block_names.iter().any(|y| name::beq(y, x)) {
            model_name(x)
        } else {
            name::dup(x)
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `rn`: `Expr.renameConsts rnF`.
    pub fn rn(&self, e: &Expr) -> Expr {
        expr_ops::rename_consts(&kit::RenameFn(|x: &Name| self.rn_name(x)), e)
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `auxCtorName'`.
    pub fn aux_ctor_name_of(&self, c: &ACtor) -> Name {
        kit::aux_ctor_name(&self.fam.t, c.mem, &c.cname)
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `specDoms`: the spec'd field domains of a constructor at `o` extra
    /// binders below the parameter frame (field `i` sits `o + i` below).
    pub fn spec_doms(&self, c: &ACtor, o: u64) -> Vec<Expr> {
        (0..c.n_f)
            .map(|i| {
                spec_all(
                    self.fam,
                    o + i,
                    &expr_ops::lift_loose_bvars(o, i, &get_d(&c.doms, i)),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `modelDoms`: the model-side field domains (public spelling renamed).
    pub fn model_doms(&self, c: &ACtor, o: u64) -> Vec<Expr> {
        (0..c.n_f)
            .map(|i| self.rn(&expr_ops::lift_loose_bvars(o, i, &get_d(&c.doms, i))))
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `fieldIdx`: a field's index arguments off its domain, at `o'` below the
    /// field's own frame.
    pub fn field_idx(&self, c: &ACtor, i: u64, o2: u64) -> Vec<Expr> {
        match match_carrier(self.fam, i, &get_d(&c.doms, i)) {
            Some((_, idx)) => lift_all(o2, &idx),
            None => Vec::new(),
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `tagDispatch`: `tag.rec p⃗ (λ i', ∀ s, aux p⃗ i' → Sort ℓs) branches i s`
    /// at frame `o` below the parameters.
    pub fn tag_dispatch(&self, o: u64, ls: &Level, branches: &[Expr], i: Expr, s: Expr) -> Expr {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        let mot_tag: Expr = expr::lam(
            expr_ops::mk_app_n(const_p(&self.tag, lps), &vars_at(o, n_p)),
            expr::forall_e(
                expr_ops::mk_app_n(
                    const_p(&self.aux, lps),
                    &app2(vars_at(o + 1, n_p), &[expr::bvar(0)]),
                ),
                expr::sort(level::dup(ls)),
                bm(),
            ),
            bm(),
        );
        let mut lvls: Vec<Level> = vec![level::imax(
            level::dup(&self.fam.u),
            level::succ(level::dup(ls)),
        )];
        for x in kit::params_of(lps) {
            lvls.push(x);
        }
        expr_ops::mk_app_n(
            expr::mk_const(kit::nstr(name::dup(&self.tag), "rec"), lvls),
            &app2(
                app2(app2(vars_at(o, n_p), &[mot_tag]), branches),
                &[i, s],
            ),
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `dispatchMotive`: the dispatching motive `λ i s, tag.rec … i s` at frame
    /// `o`, with the branches built at frame `o + 2`.
    pub fn dispatch_motive(
        &self,
        o: u64,
        ls: &Level,
        branches_at: &dyn Fn(u64) -> Vec<Expr>,
    ) -> Expr {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        expr::lam(
            expr_ops::mk_app_n(const_p(&self.tag, lps), &vars_at(o, n_p)),
            expr::lam(
                expr_ops::mk_app_n(
                    const_p(&self.aux, lps),
                    &app2(vars_at(o + 1, n_p), &[expr::bvar(0)]),
                ),
                self.tag_dispatch(
                    o + 2,
                    ls,
                    &branches_at(o + 2),
                    expr::bvar(1),
                    expr::bvar(0),
                ),
                bm(),
            ),
            bm(),
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `idxBsAt`: the index binders of a member at frame `o` (spec'd).
    pub fn idx_bs_at(&self, mem: &Mem, o: u64) -> Vec<Expr> {
        (0..mem.n_idx)
            .map(|j| {
                expr_ops::lift_loose_bvars(
                    o,
                    j,
                    &spec_all(self.fam, j, &get_d(&mem.idx_bs, j)),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `idxBsAtM`: the same on the model side.
    pub fn idx_bs_at_m(&self, mem: &Mem, o: u64) -> Vec<Expr> {
        (0..mem.n_idx)
            .map(|j| expr_ops::lift_loose_bvars(o, j, &self.rn(&get_d(&mem.idx_bs, j))))
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `packName`, `unpackName`, `unpackPackName`, `packUnpackName`,
    /// `congrPackName`, `unpackAll`, `packUnpackAll`, `recAll`: the `_impl`
    /// names of the isomorphism.
    pub fn impl_nm(&self, stem: &str, j: u64) -> Name {
        impl_name(&self.fam.t, &format!("{}_{}", stem, j))
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `appImpl`: `pack_j p⃗ idx x`, `unpack_j p⃗ idx s`, … at frame `o`.
    pub fn app_impl(&self, nm: &Name, o: u64, idx: &[Expr], args: &[Expr]) -> Expr {
        expr_ops::mk_app_n(
            const_p(nm, &self.fam.lps),
            &app2(app2(vars_at(o, self.fam.n_p), idx), args),
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `carrM`: the model-side carrier of a member at frame `o`.
    pub fn carr_m(&self, mem: &Mem, o: u64, idx: &[Expr]) -> Expr {
        carrier_at(self.fam, mem, o, idx, true)
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `ihPos`: the k-th recursive field is the k-th ih.
    pub fn ih_pos(&self, c: &ACtor, i: u64) -> u64 {
        (0..i)
            .filter(|i2| c.kinds.get(*i2 as usize).copied().flatten().is_some())
            .count() as u64
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `nIhOf`.
    pub fn n_ih_of(&self, c: &ACtor) -> u64 {
        c.kinds.iter().filter(|k| k.is_some()).count() as u64
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `c.kinds.getD i none`.
    pub fn kind(&self, c: &ACtor, i: u64) -> Option<u64> {
        c.kinds.get(i as usize).copied().flatten()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `mems.getD t default`, at a tag that is always in range.
    pub fn mem_at(&self, t: u64) -> &Mem {
        match self.fam.mems.get(t as usize) {
            Some(m) => m,
            None => &self.fam.mems[0],
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `motVar`: the motive variables at frame `o` below the prefix's end.
    pub fn mot_var(&self, o: u64, m: u64) -> Expr {
        expr::bvar(o + self.n + sub(sub(self.big_m, 1), m))
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `minVar`: the minor variables at frame `o` below the prefix's end.
    pub fn min_var(&self, o: u64, big_j: u64) -> Expr {
        expr::bvar(o + sub(sub(self.n, 1), big_j))
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `motU`: `_impl.unpack`'s motive — the identity carrier at a real
    /// member, `Carrier_j` at a mimic.
    pub fn mot_u(&self, o: u64) -> Expr {
        let u = level::dup(&self.fam.u);
        self.dispatch_motive(o, &u, &|o2: u64| {
            self.fam
                .mems
                .iter()
                .map(|mem| {
                    mk_lams(
                        &app2(
                            self.idx_bs_at(mem, o2),
                            &[aux_at(
                                self.fam,
                                mem.tag,
                                o2 + mem.n_idx,
                                &vars_at(0, mem.n_idx),
                            )],
                        ),
                        match mem.real {
                            Some(_) => aux_at(
                                self.fam,
                                mem.tag,
                                o2 + mem.n_idx + 1,
                                &vars_at(1, mem.n_idx),
                            ),
                            None => self.carr_m(mem, o2 + mem.n_idx + 1, &vars_at(1, mem.n_idx)),
                        },
                    )
                })
                .collect()
        })
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `unpackMinors`: the unpack minors at frame `o`, `λ f⃗' ih⃗, body`.
    pub fn unpack_minors(&self, o: u64) -> Vec<Expr> {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        self.fam
            .ctors
            .iter()
            .map(|c| {
                let n_ih = self.n_ih_of(c);
                let fbs = self.spec_doms(c, o);
                let ihbs: Vec<Expr> = (0..c.n_f)
                    .filter_map(|i| match self.kind(c, i) {
                        Some(t) => {
                            let k = self.ih_pos(c, i);
                            // at the ih's frame: `o + nF + k` below the parameters
                            let fo = c.n_f + k;
                            Some(expr_ops::mk_app_n(
                                self.mot_u(o + fo),
                                &vec![
                                    expr_ops::mk_app_n(
                                        const_p(&tag_ctor_name(&self.fam.t, t), lps),
                                        &app2(
                                            vars_at(o + fo, n_p),
                                            &self.field_idx(c, i, sub(fo, i)),
                                        ),
                                    ),
                                    expr::bvar(sub(sub(fo, 1), i)),
                                ],
                            ))
                        }
                        None => None,
                    })
                    .collect();
                let field_var = |i: u64| expr::bvar(sub(sub(n_ih + c.n_f, 1), i));
                let ih_var = |i: u64| expr::bvar(sub(sub(n_ih, 1), self.ih_pos(c, i)));
                let body = match self.mem_at(c.mem).real {
                    Some(_) => expr_ops::mk_app_n(
                        const_p(&self.aux_ctor_name_of(c), lps),
                        &app2(
                            vars_at(c.n_f + n_ih, n_p),
                            &(0..c.n_f).map(field_var).collect::<Vec<Expr>>(),
                        ),
                    ),
                    None => {
                        let mem = self.mem_at(c.mem);
                        // a mimic-typed field is its (unpacked) inductive
                        // hypothesis; a real-member field passes through
                        // unchanged (its hypothesis is an opaque `aux.rec`
                        // rebuild, not the field)
                        let pins = expr_ops::get_app_args(&self.carr_m(mem, c.n_f + n_ih, &[]));
                        let args: Vec<Expr> = (0..c.n_f)
                            .map(|i| match self.kind(c, i) {
                                Some(t2) => {
                                    if t2 >= self.fam.r {
                                        ih_var(i)
                                    } else {
                                        field_var(i)
                                    }
                                }
                                None => field_var(i),
                            })
                            .collect();
                        expr_ops::mk_app_n(
                            expr::mk_const(
                                name::dup(&c.cname),
                                c.clv.iter().map(level::dup).collect(),
                            ),
                            &app2(
                                dup_all(&pins[..mem.pins.len().min(pins.len())]),
                                &args,
                            ),
                        )
                    }
                };
                mk_lams(&app2(fbs, &ihbs), body)
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `motPU`: `_impl.packUnpack`'s motive.
    pub fn mot_pu(&self, o: u64) -> Expr {
        self.dispatch_motive(o, &level::zero(), &|o2: u64| {
            self.fam
                .mems
                .iter()
                .map(|mem| {
                    let s_at = |o3: u64| {
                        aux_at(
                            self.fam,
                            mem.tag,
                            o3,
                            &vars_at(sub(o3, o2 + mem.n_idx), mem.n_idx),
                        )
                    };
                    let o3 = o2 + mem.n_idx + 1;
                    mk_lams(
                        &app2(self.idx_bs_at(mem, o2), &[s_at(o2 + mem.n_idx)]),
                        match mem.real {
                            Some(_) => mk_eq(
                                &self.fam.u,
                                s_at(o3),
                                expr::bvar(0),
                                expr::bvar(0),
                            ),
                            None => {
                                let idx = vars_at(1, mem.n_idx);
                                mk_eq(
                                    &self.fam.u,
                                    s_at(o3),
                                    self.app_impl(
                                        &self.impl_nm("pack", mem.j),
                                        o3,
                                        &idx,
                                        &[self.app_impl(
                                            &self.impl_nm("unpack", mem.j),
                                            o3,
                                            &idx,
                                            &[expr::bvar(0)],
                                        )],
                                    ),
                                    expr::bvar(0),
                                )
                            }
                        },
                    )
                })
                .collect()
        })
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `puMinors`: `_impl.packUnpack`'s minors at frame `o`.
    pub fn pu_minors(&self, o: u64) -> Vec<Expr> {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        self.fam
            .ctors
            .iter()
            .map(|c| {
                let n_ih = self.n_ih_of(c);
                let fbs = self.spec_doms(c, o);
                let fo = c.n_f + n_ih;
                let field_var = |i: u64| expr::bvar(sub(sub(n_ih + c.n_f, 1), i));
                let ih_var = |i: u64| expr::bvar(sub(sub(n_ih, 1), self.ih_pos(c, i)));
                let ihbs: Vec<Expr> = (0..c.n_f)
                    .filter_map(|i| match self.kind(c, i) {
                        Some(t) => {
                            let k = self.ih_pos(c, i);
                            let fo2 = c.n_f + k;
                            Some(expr_ops::mk_app_n(
                                self.mot_pu(o + fo2),
                                &vec![
                                    expr_ops::mk_app_n(
                                        const_p(&tag_ctor_name(&self.fam.t, t), lps),
                                        &app2(
                                            vars_at(o + fo2, n_p),
                                            &self.field_idx(c, i, sub(fo2, i)),
                                        ),
                                    ),
                                    expr::bvar(sub(sub(fo2, 1), i)),
                                ],
                            ))
                        }
                        None => None,
                    })
                    .collect();
                let selfe = expr_ops::mk_app_n(
                    const_p(&self.aux_ctor_name_of(c), lps),
                    &app2(
                        vars_at(o + fo, n_p),
                        &(0..c.n_f).map(field_var).collect::<Vec<Expr>>(),
                    ),
                );
                let idx_c = lift_all(n_ih, &c.idx);
                let body = match self.mem_at(c.mem).real {
                    Some(_) => mk_refl(
                        &self.fam.u,
                        aux_at(self.fam, c.mem, o + fo, &idx_c),
                        selfe,
                    ),
                    None => {
                        let f = |o2: u64, args: &[Expr]| -> Expr {
                            expr_ops::mk_app_n(
                                const_p(&self.aux_ctor_name_of(c), lps),
                                &app2(vars_at(o + fo + o2, n_p), args),
                            )
                        };
                        let ls: Vec<Expr> = (0..c.n_f)
                            .map(|i| match self.kind(c, i) {
                                Some(t2) => {
                                    if t2 >= self.fam.r {
                                        let mem2 = self.mem_at(t2);
                                        let idx = self.field_idx(c, i, sub(fo, i));
                                        self.app_impl(
                                            &self.impl_nm("pack", mem2.j),
                                            o + fo,
                                            &idx,
                                            &[self.app_impl(
                                                &self.impl_nm("unpack", mem2.j),
                                                o + fo,
                                                &idx,
                                                &[field_var(i)],
                                            )],
                                        )
                                    } else {
                                        field_var(i)
                                    }
                                }
                                None => field_var(i),
                            })
                            .collect();
                        let rs: Vec<Expr> = (0..c.n_f).map(field_var).collect();
                        let moved: Vec<(u64, Expr, Expr, Level)> = (0..c.n_f)
                            .filter_map(|i| match self.kind(c, i) {
                                Some(t2) => {
                                    if t2 >= self.fam.r {
                                        Some((
                                            i,
                                            ih_var(i),
                                            aux_at(
                                                self.fam,
                                                t2,
                                                o + fo,
                                                &self.field_idx(c, i, sub(fo, i)),
                                            ),
                                            level::dup(&self.fam.u),
                                        ))
                                    } else {
                                        None
                                    }
                                }
                                None => None,
                            })
                            .collect();
                        congr_chain(
                            &self.fam.u,
                            &aux_at(self.fam, c.mem, o + fo, &idx_c),
                            &f,
                            &ls,
                            &rs,
                            &moved,
                        )
                    }
                };
                mk_lams(&app2(fbs, &ihbs), body)
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `motR`: `_impl.rec`'s motive — `M_m` at a real member, `M_{r+j} ∘
    /// unpack_j` at a mimic.
    pub fn mot_r(&self, o: u64) -> Expr {
        let l = level::dup(&self.l);
        self.dispatch_motive(o + self.big_m + self.n, &l, &|o2: u64| {
            // `o2` is below the parameter frame; below the prefix's end:
            // `o2 - M - n`
            let oo = sub(o2, self.big_m + self.n);
            self.fam
                .mems
                .iter()
                .map(|mem| match mem.real {
                    Some(m) => self.mot_var(oo, m),
                    None => {
                        let s_at = |o3: u64| {
                            aux_at(
                                self.fam,
                                mem.tag,
                                o3,
                                &vars_at(sub(o3, o2 + mem.n_idx), mem.n_idx),
                            )
                        };
                        let o3 = o2 + mem.n_idx + 1;
                        mk_lams(
                            &app2(self.idx_bs_at(mem, o2), &[s_at(o2 + mem.n_idx)]),
                            expr_ops::mk_app_n(
                                self.mot_var(oo + mem.n_idx + 1, mem.tag),
                                &app2(
                                    vars_at(1, mem.n_idx),
                                    &[self.app_impl(
                                        &self.impl_nm("unpack", mem.j),
                                        o3,
                                        &vars_at(1, mem.n_idx),
                                        &[expr::bvar(0)],
                                    )],
                                ),
                            ),
                        )
                    }
                })
                .collect()
        })
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `recMinors`: the adapted minors at frame `o` below the prefix's end — a
    /// mimic constructor's by unpacking its mimic-typed fields, a real
    /// constructor's by unpacking them and transporting the result along
    /// `packUnpack_j` at each packed position.
    pub fn rec_minors(&self, o: u64) -> Vec<Expr> {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        self.fam
            .ctors
            .iter()
            .map(|c| {
                let n_ih = self.n_ih_of(c);
                let o_p = o + self.big_m + self.n; // below the parameters
                let fbs = self.spec_doms(c, o_p);
                let fo = c.n_f + n_ih;
                let field_var = |i: u64| expr::bvar(sub(sub(n_ih + c.n_f, 1), i));
                let ih_var = |i: u64| expr::bvar(sub(sub(n_ih, 1), self.ih_pos(c, i)));
                let ihbs: Vec<Expr> = (0..c.n_f)
                    .filter_map(|i| match self.kind(c, i) {
                        Some(t) => {
                            let k = self.ih_pos(c, i);
                            let fo2 = c.n_f + k;
                            Some(expr_ops::mk_app_n(
                                self.mot_r(o + fo2),
                                &vec![
                                    expr_ops::mk_app_n(
                                        const_p(&tag_ctor_name(&self.fam.t, t), lps),
                                        &app2(
                                            vars_at(o_p + fo2, n_p),
                                            &self.field_idx(c, i, sub(fo2, i)),
                                        ),
                                    ),
                                    expr::bvar(sub(sub(fo2, 1), i)),
                                ],
                            ))
                        }
                        None => None,
                    })
                    .collect();
                // the public minor applied: fields (unpacked where
                // mimic-typed) and the ihs
                let unpacked = |i: u64| -> Expr {
                    match self.kind(c, i) {
                        Some(t2) => {
                            if t2 >= self.fam.r {
                                self.app_impl(
                                    &self.impl_nm("unpack", self.mem_at(t2).j),
                                    o_p + fo,
                                    &self.field_idx(c, i, sub(fo, i)),
                                    &[field_var(i)],
                                )
                            } else {
                                field_var(i)
                            }
                        }
                        None => field_var(i),
                    }
                };
                let x = expr_ops::mk_app_n(
                    self.min_var(o + fo, c.big_j),
                    &app2(
                        (0..c.n_f).map(unpacked).collect::<Vec<Expr>>(),
                        &(0..c.n_f)
                            .filter_map(|i| {
                                if self.kind(c, i).is_some() {
                                    Some(ih_var(i))
                                } else {
                                    None
                                }
                            })
                            .collect::<Vec<Expr>>(),
                    ),
                );
                let body = match self.mem_at(c.mem).real {
                    None => x,
                    Some(m) => {
                        // transports along `packUnpack_j f'_k` at each packed
                        // position
                        let packed: Vec<u64> = (0..c.n_f)
                            .filter(|i| match self.kind(c, *i) {
                                Some(t2) => t2 >= self.fam.r,
                                None => false,
                            })
                            .collect();
                        let idx_c = lift_all(n_ih, &c.idx);
                        let spine_at = |o2: u64, args: &[Expr]| -> Expr {
                            expr_ops::mk_app_n(
                                const_p(&self.aux_ctor_name_of(c), lps),
                                &app2(vars_at(o_p + fo + o2, n_p), args),
                            )
                        };
                        let mot_app = |o2: u64, args: &[Expr]| -> Expr {
                            expr_ops::mk_app_n(
                                self.mot_var(o + fo + o2, m),
                                &app2(lift_all(o2, &idx_c), &[spine_at(o2, args)]),
                            )
                        };
                        let pack_unpack_of = |i: u64| -> (Expr, Expr, Expr) {
                            let mem2 = self.mem_at(self.kind(c, i).unwrap_or(0));
                            let idx = self.field_idx(c, i, sub(fo, i));
                            (
                                self.app_impl(
                                    &self.impl_nm("pack", mem2.j),
                                    o_p + fo,
                                    &idx,
                                    &[self.app_impl(
                                        &self.impl_nm("unpack", mem2.j),
                                        o_p + fo,
                                        &idx,
                                        &[field_var(i)],
                                    )],
                                ),
                                self.app_impl(
                                    &self.impl_nm("packUnpack", mem2.j),
                                    o_p + fo,
                                    &idx,
                                    &[field_var(i)],
                                ),
                                aux_at(self.fam, mem2.tag, o_p + fo, &idx),
                            )
                        };
                        let mut acc = x;
                        let mut done: Vec<u64> = Vec::new();
                        for k in packed.iter() {
                            let (pu, prf, ty) = pack_unpack_of(*k);
                            let args = |o2: u64, z: &Expr| -> Vec<Expr> {
                                (0..c.n_f)
                                    .map(|i| {
                                        if i == *k {
                                            expr::dup(z)
                                        } else if done.iter().any(|d| *d == i) {
                                            expr_ops::lift_loose_bvars(o2, 0, &field_var(i))
                                        } else if packed.iter().any(|p| *p == i) {
                                            expr_ops::lift_loose_bvars(
                                                o2,
                                                0,
                                                &pack_unpack_of(i).0,
                                            )
                                        } else {
                                            expr_ops::lift_loose_bvars(o2, 0, &field_var(i))
                                        }
                                    })
                                    .collect()
                            };
                            let motive: Expr = expr::lam(
                                expr::dup(&ty),
                                expr::lam(
                                    mk_eq(
                                        &self.fam.u,
                                        expr_ops::lift_loose_bvars(1, 0, &ty),
                                        expr_ops::lift_loose_bvars(1, 0, &pu),
                                        expr::bvar(0),
                                    ),
                                    mot_app(2, &args(2, &expr::bvar(1))),
                                    bm(),
                                ),
                                bm(),
                            );
                            acc = mk_eq_rec(
                                &self.l,
                                &self.fam.u,
                                ty,
                                pu,
                                motive,
                                acc,
                                field_var(*k),
                                prf,
                            );
                            done.push(*k);
                        }
                        acc
                    }
                };
                mk_lams(&app2(fbs, &ihbs), body)
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `upStmtOf`: `unpack_j (pack_j x) = x` at frame `o`.
    pub fn up_stmt_of(&self, mem: &Mem, o: u64, idx: &[Expr], x: Expr) -> Expr {
        mk_eq(
            &self.fam.u,
            self.carr_m(mem, o, idx),
            self.app_impl(
                &self.impl_nm("unpack", mem.j),
                o,
                idx,
                &[self.app_impl(&self.impl_nm("pack", mem.j), o, idx, &[expr::dup(&x)])],
            ),
            x,
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `gctors`: the group's constructors, in the container family's order.
    pub fn gctors(&self, g: &Group) -> Vec<&'a ACtor> {
        let mut out: Vec<&ACtor> = Vec::new();
        for t in g.tags.iter() {
            for c in self.fam.ctors.iter() {
                if c.mem == *t {
                    out.push(c);
                }
            }
        }
        out
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `cRec`: group member `k`'s container recursor at an elimination level.
    pub fn c_rec(&self, g: &Group, k: u64, le: &Level) -> Expr {
        let mut lvls: Vec<Level> = if g.large {
            vec![level::dup(le)]
        } else {
            Vec::new()
        };
        for x in g.lv.iter() {
            lvls.push(level::dup(x));
        }
        expr::mk_const(get_name(&g.rec_names, k), lvls)
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `pinsAt`: the group's pins at frame `o`.
    pub fn pins_at(&self, g: &Group, o: u64) -> Vec<Expr> {
        let head = self.mem_at(*g.tags.first().unwrap_or(&0));
        let args = expr_ops::get_app_args(&self.carr_m(head, o, &[]));
        dup_all(&args[..(g.n_pi as usize).min(args.len())])
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `inGroup`.
    pub fn in_group(&self, g: &Group, k: Option<u64>) -> bool {
        match k {
            Some(t2) => g.tags.iter().any(|t| *t == t2),
            None => false,
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `packMotives`: the pack motives at frame `o`.
    pub fn pack_motives(&self, g: &Group, o: u64) -> Vec<Expr> {
        g.tags
            .iter()
            .map(|t| {
                let mem = self.mem_at(*t);
                mk_lams(
                    &app2(
                        self.idx_bs_at_m(mem, o),
                        &[self.carr_m(mem, o + mem.n_idx, &vars_at(0, mem.n_idx))],
                    ),
                    aux_at(self.fam, *t, o + mem.n_idx + 1, &vars_at(1, mem.n_idx)),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `packMinors`: the pack minors at frame `o`.
    pub fn pack_minors(&self, g: &Group, o: u64) -> Vec<Expr> {
        let lps = &self.fam.lps;
        let n_p = self.fam.n_p;
        self.gctors(g)
            .into_iter()
            .map(|c| {
                let grp_rec: Vec<u64> = (0..c.n_f)
                    .filter(|i| self.in_group(g, self.kind(c, *i)))
                    .collect();
                let n_ih_i = grp_rec.len() as u64;
                let gbs = self.model_doms(c, o);
                let ihbs: Vec<Expr> = grp_rec
                    .iter()
                    .map(|i| {
                        let k = grp_rec.iter().filter(|x| **x < *i).count() as u64;
                        let fo = c.n_f + k;
                        aux_at(
                            self.fam,
                            self.kind(c, *i).unwrap_or(0),
                            o + fo,
                            &self.field_idx(c, *i, sub(fo, *i)),
                        )
                    })
                    .collect();
                let g_var = |i: u64| expr::bvar(sub(sub(n_ih_i + c.n_f, 1), i));
                let ih_var_i = |i: u64| {
                    expr::bvar(sub(
                        sub(n_ih_i, 1),
                        grp_rec.iter().filter(|x| **x < i).count() as u64,
                    ))
                };
                let fo = c.n_f + n_ih_i;
                let args: Vec<Expr> = (0..c.n_f)
                    .map(|i| match self.kind(c, i) {
                        Some(t2) => {
                            if g.tags.iter().any(|t| *t == t2) {
                                ih_var_i(i)
                            } else if t2 >= self.fam.r {
                                let mem2 = self.mem_at(t2);
                                self.app_impl(
                                    &self.impl_nm("pack", mem2.j),
                                    o + fo,
                                    &self.field_idx(c, i, sub(fo, i)),
                                    &[g_var(i)],
                                )
                            } else {
                                g_var(i)
                            }
                        }
                        None => g_var(i),
                    })
                    .collect();
                mk_lams(
                    &app2(gbs, &ihbs),
                    expr_ops::mk_app_n(
                        const_p(&self.aux_ctor_name_of(c), lps),
                        &app2(vars_at(o + fo, n_p), &args),
                    ),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `upMotives`: `unpackPack`'s motives at frame `o`.
    pub fn up_motives(&self, g: &Group, o: u64) -> Vec<Expr> {
        g.tags
            .iter()
            .map(|t| {
                let mem = self.mem_at(*t);
                mk_lams(
                    &app2(
                        self.idx_bs_at_m(mem, o),
                        &[self.carr_m(mem, o + mem.n_idx, &vars_at(0, mem.n_idx))],
                    ),
                    self.up_stmt_of(
                        mem,
                        o + mem.n_idx + 1,
                        &vars_at(1, mem.n_idx),
                        expr::bvar(0),
                    ),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `upMinors`: `unpackPack`'s minors at frame `o`, by the congruence chain.
    pub fn up_minors(&self, g: &Group, o: u64) -> Vec<Expr> {
        self.gctors(g)
            .into_iter()
            .map(|c| {
                let mem_c = self.mem_at(c.mem);
                let grp_rec: Vec<u64> = (0..c.n_f)
                    .filter(|i| self.in_group(g, self.kind(c, *i)))
                    .collect();
                let n_ih_i = grp_rec.len() as u64;
                let gbs = self.model_doms(c, o);
                let fo = c.n_f + n_ih_i;
                let g_var_at = |i: u64, o2: u64| expr::bvar(o2 + sub(sub(n_ih_i + c.n_f, 1), i));
                let ihbs: Vec<Expr> = grp_rec
                    .iter()
                    .map(|i| {
                        let k = grp_rec.iter().filter(|x| **x < *i).count() as u64;
                        let fo2 = c.n_f + k;
                        let mem2 = self.mem_at(self.kind(c, *i).unwrap_or(0));
                        self.up_stmt_of(
                            mem2,
                            o + fo2,
                            &self.field_idx(c, *i, sub(fo2, *i)),
                            expr::bvar(sub(sub(fo2, 1), *i)),
                        )
                    })
                    .collect();
                // the spine's pins are the constructor's OWN container's (a
                // group member's container differs from the group's head
                // container)
                let f = |o2: u64, args: &[Expr]| -> Expr {
                    let pins = expr_ops::get_app_args(&self.carr_m(mem_c, o + fo + o2, &[]));
                    expr_ops::mk_app_n(
                        expr::mk_const(
                            name::dup(&c.cname),
                            c.clv.iter().map(level::dup).collect(),
                        ),
                        &app2(dup_all(&pins[..mem_c.pins.len().min(pins.len())]), args),
                    )
                };
                let ls: Vec<Expr> = (0..c.n_f)
                    .map(|i| match self.kind(c, i) {
                        Some(t2) => {
                            if t2 >= self.fam.r {
                                let mem2 = self.mem_at(t2);
                                let idx = self.field_idx(c, i, sub(fo, i));
                                self.app_impl(
                                    &self.impl_nm("unpack", mem2.j),
                                    o + fo,
                                    &idx,
                                    &[self.app_impl(
                                        &self.impl_nm("pack", mem2.j),
                                        o + fo,
                                        &idx,
                                        &[g_var_at(i, 0)],
                                    )],
                                )
                            } else {
                                g_var_at(i, 0)
                            }
                        }
                        None => g_var_at(i, 0),
                    })
                    .collect();
                let rs: Vec<Expr> = (0..c.n_f).map(|i| g_var_at(i, 0)).collect();
                let moved: Vec<(u64, Expr, Expr, Level)> = (0..c.n_f)
                    .filter_map(|i| match self.kind(c, i) {
                        Some(t2) => {
                            if g.tags.iter().any(|t| *t == t2) {
                                Some((
                                    i,
                                    expr::bvar(sub(
                                        sub(n_ih_i, 1),
                                        grp_rec.iter().filter(|x| **x < i).count() as u64,
                                    )),
                                    self.carr_m(
                                        self.mem_at(t2),
                                        o + fo,
                                        &self.field_idx(c, i, sub(fo, i)),
                                    ),
                                    level::dup(&self.fam.u),
                                ))
                            } else if t2 >= self.fam.r {
                                let mem2 = self.mem_at(t2);
                                let idx = self.field_idx(c, i, sub(fo, i));
                                Some((
                                    i,
                                    self.app_impl(
                                        &self.impl_nm("unpackPack", mem2.j),
                                        o + fo,
                                        &idx,
                                        &[g_var_at(i, 0)],
                                    ),
                                    self.carr_m(mem2, o + fo, &idx),
                                    level::dup(&self.fam.u),
                                ))
                            } else {
                                None
                            }
                        }
                        None => None,
                    })
                    .collect();
                let alpha = self.carr_m(mem_c, o + fo, &lift_all(n_ih_i, &c.idx));
                mk_lams(
                    &app2(gbs, &ihbs),
                    congr_chain(&self.fam.u, &alpha, &f, &ls, &rs, &moved),
                )
            })
            .collect()
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The iota proof's own builders (step 9's `uOf`, `eOf`, `carrOf`, `rOf`,
/// `ihApp`, `stmtAt`, `nest`, `goT`): the locals they close over, as a record,
/// for the reason the module note gives for `Gen`.
pub struct Iota<'b, 'a> {
    pub g: &'b Gen<'a>,
    pub mem: &'b Mem,
    pub c: &'b ACtor,
    pub n_f: u64,
    /// `oP`: below the parameters at the statement's end
    pub o_p: u64,
    /// the constructor's index expressions at the statement frame
    pub idx_c: Vec<Expr>,
    pub prefix_vars: Vec<Expr>,
    pub packed: Vec<u64>,
    pub rec_all: Name,
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The iota proof's builders themselves.
impl<'b, 'a> Iota<'b, 'a> {
    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// The repeated `fieldIdx c i (nF - i) |>.map rn |>.map (·.liftLooseBVars
    /// (M + n) nF) |> liftAll o'` of step 9.
    pub fn idx_of(&self, i: u64, o2: u64) -> Vec<Expr> {
        let gg = self.g;
        let raw = gg.field_idx(self.c, i, sub(self.n_f, i));
        raw.iter()
            .map(|e| {
                expr_ops::lift_loose_bvars(
                    o2,
                    0,
                    &expr_ops::lift_loose_bvars(gg.big_m + gg.n, self.n_f, &gg.rn(e)),
                )
            })
            .collect()
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `uOf`: `unpack (pack f_i)` at frame `o'`.
    pub fn u_of(&self, o2: u64, i: u64) -> Expr {
        let gg = self.g;
        let mem2 = gg.mem_at(gg.kind(self.c, i).unwrap_or(0));
        let idx = self.idx_of(i, o2);
        gg.app_impl(
            &gg.impl_nm("unpack", mem2.j),
            self.o_p + o2,
            &idx,
            &[gg.app_impl(
                &gg.impl_nm("pack", mem2.j),
                self.o_p + o2,
                &idx,
                &[expr_ops::lift_loose_bvars(
                    o2,
                    0,
                    &expr::bvar(sub(sub(self.n_f, 1), i)),
                )],
            )],
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `eOf`: `unpackPack_j f_i`.
    pub fn e_of(&self, o2: u64, i: u64) -> Expr {
        let gg = self.g;
        let mem2 = gg.mem_at(gg.kind(self.c, i).unwrap_or(0));
        let idx = self.idx_of(i, o2);
        gg.app_impl(
            &gg.impl_nm("unpackPack", mem2.j),
            self.o_p + o2,
            &idx,
            &[expr_ops::lift_loose_bvars(
                o2,
                0,
                &expr::bvar(sub(sub(self.n_f, 1), i)),
            )],
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `carrOf`: the field's model-side carrier.
    pub fn carr_of(&self, o2: u64, i: u64) -> Expr {
        let gg = self.g;
        let mem2 = gg.mem_at(gg.kind(self.c, i).unwrap_or(0));
        gg.carr_m(mem2, self.o_p + o2, &self.idx_of(i, o2))
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `rOf`: `R_k`, the aux recursor at `pack f_k`.
    pub fn r_of(&self, o2: u64, i: u64) -> Expr {
        let gg = self.g;
        let mem2 = gg.mem_at(gg.kind(self.c, i).unwrap_or(0));
        let idx = self.idx_of(i, o2);
        expr_ops::mk_app_n(
            const_p(&self.rec_all, &gg.rlps),
            &app2(
                app2(
                    lift_all(o2, &self.prefix_vars),
                    &[expr_ops::mk_app_n(
                        const_p(&tag_ctor_name(&gg.fam.t, mem2.tag), &gg.fam.lps),
                        &app2(vars_at(self.o_p + o2, gg.fam.n_p), &idx),
                    )],
                ),
                &[gg.app_impl(
                    &gg.impl_nm("pack", mem2.j),
                    self.o_p + o2,
                    &idx,
                    &[expr_ops::lift_loose_bvars(
                        o2,
                        0,
                        &expr::bvar(sub(sub(self.n_f, 1), i)),
                    )],
                )],
            ),
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `ihApp`: the real-kind ih through the model recursor.
    pub fn ih_app(&self, i: u64) -> Expr {
        let gg = self.g;
        let t2 = gg.kind(self.c, i).unwrap_or(0);
        let mem2 = gg.mem_at(t2);
        let rn2 = match mem2.real {
            Some(m2) => model_name(&kit::nstr(get_name(&gg.member_names, m2), "rec")),
            None => model_name(&kit::nstr(
                name::dup(&gg.fam.t),
                &format!("rec_{}", mem2.j + 1),
            )),
        };
        let idx_i: Vec<Expr> = gg
            .field_idx(self.c, i, sub(self.n_f, i))
            .iter()
            .map(|e| expr_ops::lift_loose_bvars(gg.big_m + gg.n, self.n_f, &gg.rn(e)))
            .collect();
        expr_ops::mk_app_n(
            expr::mk_const(rn2, gg.rlvls.iter().map(level::dup).collect()),
            &app2(
                app2(dup_all(&self.prefix_vars), &idx_i),
                &[expr::bvar(sub(sub(self.n_f, 1), i))],
            ),
        )
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `zOf`: the generalised value at a packed position, `f_k` where fixed.
    pub fn z_of(&self, o2: u64, zs: &[Option<Expr>], k: u64) -> Expr {
        match zs.get(k as usize).and_then(|x| x.as_ref()) {
            Some(e) => expr::dup(e),
            None => expr_ops::lift_loose_bvars(
                o2,
                0,
                &expr::bvar(sub(sub(self.n_f, 1), k)),
            ),
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `hOfk`: the generalised proof at a packed position, `e_k` where fixed.
    pub fn h_of_k(&self, o2: u64, hs: &[Option<Expr>], k: u64) -> Expr {
        match hs.get(k as usize).and_then(|x| x.as_ref()) {
            Some(e) => expr::dup(e),
            None => self.e_of(o2, k),
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `stmtAt`: the statement's three parts at the generalisation state
    /// `(zs, hs)`, at frame `o'`.
    pub fn stmt_at(
        &self,
        o2: u64,
        zs: &[Option<Expr>],
        hs: &[Option<Expr>],
    ) -> (Expr, Expr, Expr) {
        let gg = self.g;
        let lps = &gg.fam.lps;
        let n_p = gg.fam.n_p;
        let n_f = self.n_f;
        let fields_g: Vec<Expr> = (0..n_f)
            .map(|i| {
                if self.packed.iter().any(|p| *p == i) {
                    self.z_of(o2, zs, i)
                } else {
                    expr_ops::lift_loose_bvars(o2, 0, &expr::bvar(sub(sub(n_f, 1), i)))
                }
            })
            .collect();
        let idx_cg = lift_all(o2, &self.idx_c);
        let ctor_app_g = match self.mem.real {
            Some(_) => expr_ops::mk_app_n(
                const_p(&model_name(&self.c.cname), lps),
                &app2(vars_at(self.o_p + o2, n_p), &fields_g),
            ),
            None => {
                let pins = expr_ops::get_app_args(&gg.carr_m(self.mem, self.o_p + o2, &[]));
                expr_ops::mk_app_n(
                    expr::mk_const(
                        name::dup(&self.c.cname),
                        self.c.clv.iter().map(level::dup).collect(),
                    ),
                    &app2(
                        dup_all(&pins[..self.mem.pins.len().min(pins.len())]),
                        &fields_g,
                    ),
                )
            }
        };
        let alpha_g = expr_ops::mk_app_n(
            gg.mot_var(n_f + o2, self.mem.tag),
            &app2(dup_all(&idx_cg), &[expr::dup(&ctor_app_g)]),
        );
        // RHS: the minor at the generalised fields, transported ihs at packed
        // positions
        let rhs_ihs: Vec<Expr> = (0..n_f)
            .filter_map(|i| match gg.kind(self.c, i) {
                Some(t2) => {
                    if t2 >= gg.fam.r {
                        let carr = self.carr_of(o2, i);
                        let mem2 = gg.mem_at(t2);
                        let idx = self.idx_of(i, o2);
                        Some(mk_eq_rec(
                            &gg.l,
                            &gg.fam.u,
                            expr::dup(&carr),
                            self.u_of(o2, i),
                            expr::lam(
                                expr::dup(&carr),
                                expr::lam(
                                    mk_eq(
                                        &gg.fam.u,
                                        expr_ops::lift_loose_bvars(1, 0, &carr),
                                        expr_ops::lift_loose_bvars(1, 0, &self.u_of(o2, i)),
                                        expr::bvar(0),
                                    ),
                                    expr_ops::mk_app_n(
                                        gg.mot_var(n_f + o2 + 2, mem2.tag),
                                        &app2(lift_all(2, &idx), &[expr::bvar(1)]),
                                    ),
                                    bm(),
                                ),
                                bm(),
                            ),
                            self.r_of(o2, i),
                            self.z_of(o2, zs, i),
                            self.h_of_k(o2, hs, i),
                        ))
                    } else {
                        Some(expr_ops::lift_loose_bvars(o2, 0, &self.ih_app(i)))
                    }
                }
                None => None,
            })
            .collect();
        let rhs_g = expr_ops::mk_app_n(
            gg.min_var(n_f + o2, self.c.big_j),
            &app2(dup_all(&fields_g), &rhs_ihs),
        );
        // LHS: the unfolded recursor
        let x = expr_ops::mk_app_n(
            gg.min_var(n_f + o2, self.c.big_j),
            &app2(
                (0..n_f)
                    .map(|i| {
                        if self.packed.iter().any(|p| *p == i) {
                            self.u_of(o2, i)
                        } else {
                            expr_ops::lift_loose_bvars(
                                o2,
                                0,
                                &expr::bvar(sub(sub(n_f, 1), i)),
                            )
                        }
                    })
                    .collect::<Vec<Expr>>(),
                &(0..n_f)
                    .filter_map(|i| match gg.kind(self.c, i) {
                        Some(t2) => {
                            if t2 >= gg.fam.r {
                                Some(self.r_of(o2, i))
                            } else {
                                Some(expr_ops::lift_loose_bvars(o2, 0, &self.ih_app(i)))
                            }
                        }
                        None => None,
                    })
                    .collect::<Vec<Expr>>(),
            ),
        );
        let lhs_g = match self.mem.real {
            Some(_) => self.go_t(o2, zs, hs, &self.packed, &mut Vec::new(), x),
            None => {
                let f = |o3: u64, args: &[Expr]| -> Expr {
                    let pins =
                        expr_ops::get_app_args(&gg.carr_m(self.mem, self.o_p + o2 + o3, &[]));
                    expr_ops::mk_app_n(
                        expr::mk_const(
                            name::dup(&self.c.cname),
                            self.c.clv.iter().map(level::dup).collect(),
                        ),
                        &app2(
                            dup_all(&pins[..self.mem.pins.len().min(pins.len())]),
                            args,
                        ),
                    )
                };
                let ls: Vec<Expr> = (0..n_f)
                    .map(|i| {
                        if self.packed.iter().any(|p| *p == i) {
                            self.u_of(o2, i)
                        } else {
                            expr_ops::lift_loose_bvars(
                                o2,
                                0,
                                &expr::bvar(sub(sub(n_f, 1), i)),
                            )
                        }
                    })
                    .collect();
                let rs: Vec<Expr> = dup_all(&fields_g);
                let moved: Vec<(u64, Expr, Expr, Level)> = self
                    .packed
                    .iter()
                    .map(|k| {
                        (
                            *k,
                            self.h_of_k(o2, hs, *k),
                            self.carr_of(o2, *k),
                            level::dup(&gg.fam.u),
                        )
                    })
                    .collect();
                let carr = gg.carr_m(self.mem, self.o_p + o2, &idx_cg);
                let chain = congr_chain(&gg.fam.u, &carr, &f, &ls, &rs, &moved);
                mk_eq_rec(
                    &gg.l,
                    &gg.fam.u,
                    expr::dup(&carr),
                    f(0, &ls),
                    expr::lam(
                        expr::dup(&carr),
                        expr::lam(
                            mk_eq(
                                &gg.fam.u,
                                expr_ops::lift_loose_bvars(1, 0, &carr),
                                expr_ops::lift_loose_bvars(1, 0, &f(0, &ls)),
                                expr::bvar(0),
                            ),
                            expr_ops::mk_app_n(
                                gg.mot_var(n_f + o2 + 2, self.mem.tag),
                                &app2(lift_all(2, &idx_cg), &[expr::bvar(1)]),
                            ),
                            bm(),
                        ),
                        bm(),
                    ),
                    x,
                    f(0, &rs),
                    chain,
                )
            }
        };
        (alpha_g, lhs_g, rhs_g)
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `goT`: the LHS transport chain over the packed positions at a real
    /// member.
    pub fn go_t(
        &self,
        o2: u64,
        zs: &[Option<Expr>],
        hs: &[Option<Expr>],
        ks: &[u64],
        done: &mut Vec<u64>,
        acc: Expr,
    ) -> Expr {
        let gg = self.g;
        let lps = &gg.fam.lps;
        let n_p = gg.fam.n_p;
        let n_f = self.n_f;
        match ks.split_first() {
            None => acc,
            Some((k, rest)) => {
                let aux_ty_k = aux_at(
                    gg.fam,
                    gg.kind(self.c, *k).unwrap_or(0),
                    self.o_p + o2,
                    &self.idx_of(*k, o2),
                );
                let pack_of = |o3: u64, i: u64, x: Expr| -> Expr {
                    let mem2 = gg.mem_at(gg.kind(self.c, i).unwrap_or(0));
                    gg.app_impl(
                        &gg.impl_nm("pack", mem2.j),
                        self.o_p + o2 + o3,
                        &self.idx_of(i, o2 + o3),
                        &[x],
                    )
                };
                let spine_at = |o3: u64, args: &[Expr]| -> Expr {
                    expr_ops::mk_app_n(
                        const_p(&gg.aux_ctor_name_of(self.c), lps),
                        &app2(vars_at(self.o_p + o2 + o3, n_p), args),
                    )
                };
                let idx_cg = lift_all(o2, &self.idx_c);
                let mot_app = |o3: u64, args: &[Expr]| -> Expr {
                    expr_ops::mk_app_n(
                        gg.mot_var(n_f + o2 + o3, self.mem.tag),
                        &app2(lift_all(o3, &idx_cg), &[spine_at(o3, args)]),
                    )
                };
                let args = |o3: u64, z: &Expr| -> Vec<Expr> {
                    (0..n_f)
                        .map(|i| {
                            if i == *k {
                                expr::dup(z)
                            } else if self.packed.iter().any(|p| *p == i) {
                                if done.iter().any(|d| *d == i) {
                                    pack_of(
                                        o3,
                                        i,
                                        expr_ops::lift_loose_bvars(
                                            o3,
                                            0,
                                            &self.z_of(o2, zs, i),
                                        ),
                                    )
                                } else {
                                    pack_of(
                                        o3,
                                        i,
                                        expr_ops::lift_loose_bvars(o3, 0, &self.u_of(o2, i)),
                                    )
                                }
                            } else {
                                expr_ops::lift_loose_bvars(
                                    o2 + o3,
                                    0,
                                    &expr::bvar(sub(sub(n_f, 1), i)),
                                )
                            }
                        })
                        .collect()
                };
                let motive: Expr = expr::lam(
                    expr::dup(&aux_ty_k),
                    expr::lam(
                        mk_eq(
                            &gg.fam.u,
                            expr_ops::lift_loose_bvars(1, 0, &aux_ty_k),
                            pack_of(
                                1,
                                *k,
                                expr_ops::lift_loose_bvars(1, 0, &self.u_of(o2, *k)),
                            ),
                            expr::bvar(0),
                        ),
                        mot_app(2, &args(2, &expr::bvar(1))),
                        bm(),
                    ),
                    bm(),
                );
                let mem2 = gg.mem_at(gg.kind(self.c, *k).unwrap_or(0));
                let idx = self.idx_of(*k, o2);
                let cp = gg.app_impl(
                    &gg.impl_nm("congrPack", mem2.j),
                    self.o_p + o2,
                    &idx,
                    &[
                        self.u_of(o2, *k),
                        self.z_of(o2, zs, *k),
                        self.h_of_k(o2, hs, *k),
                    ],
                );
                let next = mk_eq_rec(
                    &gg.l,
                    &gg.fam.u,
                    expr::dup(&aux_ty_k),
                    pack_of(0, *k, self.u_of(o2, *k)),
                    motive,
                    acc,
                    pack_of(0, *k, self.z_of(o2, zs, *k)),
                    cp,
                );
                done.push(*k);
                self.go_t(o2, zs, hs, rest, done, next)
            }
        }
    }

    /// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
    /// `nest`: the generalisations, outermost over the first packed position;
    /// the innermost base is `Eq.refl`.
    pub fn nest(
        &self,
        ks: &[u64],
        o2: u64,
        zs: &[Option<Expr>],
        hs: &[Option<Expr>],
    ) -> Expr {
        let gg = self.g;
        match ks.split_first() {
            None => {
                let (alpha_g, lhs_g, _) = self.stmt_at(o2, zs, hs);
                mk_refl(&gg.l, alpha_g, lhs_g)
            }
            Some((k, rest)) => {
                // J on `e_k` with motive `λ z h, stmt[z_k := z, h_k := h]`
                let carr = self.carr_of(o2, *k);
                let zs2: Vec<Option<Expr>> = (0..self.n_f)
                    .map(|i| {
                        if i == *k {
                            Some(expr::bvar(1))
                        } else {
                            zs.get(i as usize)
                                .and_then(|x| x.as_ref())
                                .map(|e| expr_ops::lift_loose_bvars(2, 0, e))
                        }
                    })
                    .collect();
                let hs2: Vec<Option<Expr>> = (0..self.n_f)
                    .map(|i| {
                        if i == *k {
                            Some(expr::bvar(0))
                        } else {
                            hs.get(i as usize)
                                .and_then(|x| x.as_ref())
                                .map(|e| expr_ops::lift_loose_bvars(2, 0, e))
                        }
                    })
                    .collect();
                let (alpha_m, lhs_m, rhs_m) = self.stmt_at(o2 + 2, &zs2, &hs2);
                let motive: Expr = expr::lam(
                    expr::dup(&carr),
                    expr::lam(
                        mk_eq(
                            &gg.fam.u,
                            expr_ops::lift_loose_bvars(1, 0, &carr),
                            expr_ops::lift_loose_bvars(1, 0, &self.u_of(o2, *k)),
                            expr::bvar(0),
                        ),
                        mk_eq(&gg.l, alpha_m, lhs_m, rhs_m),
                        bm(),
                    ),
                    bm(),
                );
                // the base: position k at `u_k`, `Eq.refl`
                let zs_b: Vec<Option<Expr>> = (0..self.n_f)
                    .map(|i| {
                        if i == *k {
                            Some(self.u_of(o2, *k))
                        } else {
                            zs.get(i as usize)
                                .and_then(|x| x.as_ref())
                                .map(expr::dup)
                        }
                    })
                    .collect();
                let hs_b: Vec<Option<Expr>> = (0..self.n_f)
                    .map(|i| {
                        if i == *k {
                            Some(mk_refl(
                                &gg.fam.u,
                                expr::dup(&carr),
                                self.u_of(o2, *k),
                            ))
                        } else {
                            hs.get(i as usize)
                                .and_then(|x| x.as_ref())
                                .map(expr::dup)
                        }
                    })
                    .collect();
                mk_eq_rec(
                    &level::zero(),
                    &gg.fam.u,
                    expr::dup(&carr),
                    self.u_of(o2, *k),
                    motive,
                    self.nest(rest, o2, &zs_b, &hs_b),
                    expr_ops::lift_loose_bvars(
                        o2,
                        0,
                        &expr::bvar(sub(sub(self.n_f, 1), *k)),
                    ),
                    self.e_of(o2, *k),
                )
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// The cited function's `push` local: emit a definition and record its height.
pub fn push_defn(
    out: &mut Vec<Declaration>,
    heights: &mut Vec<(Name, u64)>,
    ctx: &Ctx,
    nm: Name,
    l: Vec<Name>,
    ty: Expr,
    v: Expr,
) {
    let h: ReducibilityHint = {
        let hof = |x: &Name| -> u64 { crate::in_model::mutual::h_of(heights, ctx, x) };
        kit::hint_for(&hof, &v)
    };
    heights.insert(0, (name::dup(&nm), kit::hint_height(&h)));
    out.push(Declaration::DefnDecl(
        ConstantVal {
            name: nm,
            level_params: l,
            ty,
        },
        v,
        h,
    ));
}

/// con-leche: ConLeche/Frontend/InModel/Nested.lean:400-1316 genNested
/// **The generic in-process rung**: mutual, nested, both.  (The mutual rung of
/// `mutual::gen_mutual` is the special case without mimics; it stays as the
/// B1/B2 landing.)
pub fn gen_nested(ctx: &Ctx, b: &BlockRec) -> Result<Vec<Declaration>, String> {
    let t0 = b.types.first().ok_or_else(|| "empty block".to_string())?;
    let t_name = name::dup(&t0.cv.name);
    let lps: Vec<Name> = dup_names(&t0.cv.level_params);
    let n_p = t0.n_p;
    let r = b.types.len() as u64;
    for t in b.types.iter() {
        if t.is_reflexive {
            return Err(format!("reflexive member {}", name_str(&t.cv.name)));
        }
        if !crate::tree::export::names_beq(&t.cv.level_params, &lps) || t.n_p != n_p {
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
    // the first member's parameter binders and sort: the telescope of
    // everything generated below (the other members' telescopes and sorts are
    // NOT compared here — the fold's typing of the public slots, emitted at
    // each member's own declared type, is official's `is_def_eq` /
    // `is_equivalent` check)
    let pbs: Vec<Expr> = pi_binders(&pbs0[..(n_p as usize).min(pbs0.len())]);
    for t in b.types.iter() {
        let ok = match expr_ops::strip_pis(n_p + t.n_idx, &t.cv.ty) {
            Some((_, rr)) => matches!(expr::view(&rr), ExprView::Sort(_)),
            None => false,
        };
        if !ok {
            return Err(format!(
                "former {} is not a telescope ending in a sort",
                name_str(&t.cv.name)
            ));
        }
    }
    // the first recursor's telescope: parameters, `M` motives, `n` minors
    let t_rec = kit::nstr(name::dup(&t_name), "rec");
    let r0 = b
        .recs
        .iter()
        .find(|x| name::beq(&x.cv.name, &t_rec))
        .ok_or_else(|| format!("no recursor {}.rec", name_str(&t_name)))?;
    let big_m = r0.n_m;
    let n = r0.nm;
    if big_m < r {
        return Err("fewer motives than members".to_string());
    }
    let (_, after_p) = expr_ops::strip_pis(n_p, &r0.cv.ty)
        .ok_or_else(|| "recursor: parameter telescope".to_string())?;
    let (motive_bs, after_m) = expr_ops::strip_pis(big_m, &after_p)
        .ok_or_else(|| "recursor: motive telescope".to_string())?;
    let (minor_bs, _) = expr_ops::strip_pis(n, &after_m)
        .ok_or_else(|| "recursor: minor telescope".to_string())?;
    // the members: real ones and mimics
    let mems = read_mems(&lps, n_p, &b.types, &pi_binders(&motive_bs))?;
    let large_opt: Option<Name> = match r0.cv.level_params.split_first() {
        Some((e, rest)) => {
            if crate::tree::export::names_beq(&dup_names(rest), &lps)
                && !lps.iter().any(|x| name::beq(x, e))
            {
                Some(name::dup(e))
            } else {
                None
            }
        }
        None => None,
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
        dup_names(&lps)
    };
    let mut fam = Family {
        t: name::dup(&t_name),
        lps: dup_names(&lps),
        n_p,
        pbs: dup_all(&pbs),
        u: level::dup(&u),
        r,
        mems,
        ctors: Vec::new(),
        large,
        elim: name::dup(&elim),
    };
    // the recursor of each member: `T_m.rec` at a real member, `T.rec_j`
    // (1-based) at a mimic
    let rec_of = |mem_real: Option<u64>, mem_j: u64| -> Result<&IndRecRec, String> {
        let nm = match mem_real {
            Some(m) => kit::nstr(name::dup(&b.types[m as usize].cv.name), "rec"),
            None => kit::nstr(name::dup(&t_name), &format!("rec_{}", mem_j + 1)),
        };
        b.recs
            .iter()
            .find(|rr| name::beq(&rr.cv.name, &nm))
            .ok_or_else(|| format!("no recursor {}", name_str(&nm)))
    };
    for mem in fam.mems.iter() {
        let rr = rec_of(mem.real, mem.j)?;
        if rr.n_p != n_p || rr.n_m != big_m || rr.nm != n || rr.n_i != mem.n_idx {
            return Err(format!(
                "recursor {}: unexpected telescope",
                name_str(&rr.cv.name)
            ));
        }
        if !crate::tree::export::names_beq(&rr.cv.level_params, &rlps) {
            return Err(format!(
                "recursor {}: eliminator shape differs",
                name_str(&rr.cv.name)
            ));
        }
    }
    // field counts: a real constructor's from the block, a mimic's from the
    // member's recursor rules
    let n_f_of = |cname: &Name, mem: u64| -> Result<u64, String> {
        let mem_r = fam
            .mems
            .iter()
            .find(|x| x.tag == mem)
            .ok_or_else(|| "unreachable".to_string())?;
        match mem_r.real {
            Some(_) => match b.ctors.iter().find(|c| name::beq(&c.cv.name, cname)) {
                Some(c) => Ok(c.n_f),
                None => Err(format!("constructor {} not in the block", name_str(cname))),
            },
            None => {
                let rr = rec_of(mem_r.real, mem_r.j)?;
                match rr.rules.iter().find(|ru| name::beq(&ru.ctor, cname)) {
                    Some(rule) => Ok(rule.nfields),
                    None => Err(format!(
                        "no rule for {} in {}",
                        name_str(cname),
                        name_str(&rr.cv.name)
                    )),
                }
            }
        }
    };
    let ctors = read_ctors(&fam, big_m, &pi_binders(&minor_bs), &n_f_of)?;
    fam.ctors = ctors;
    if fam.ctors.len() as u64 != n {
        return Err("minor count".to_string());
    }
    // the real members' constructors must be the block's, in order
    for m in 0..r {
        let t = &b.types[m as usize];
        let own: Vec<&ACtor> = fam.ctors.iter().filter(|c| c.mem == m).collect();
        let same = own.len() == t.ctors.len()
            && (0..own.len()).all(|i| name::beq(&own[i].cname, &t.ctors[i]));
        if !same {
            return Err(format!(
                "member {}: constructors differ from the recursor's minors",
                name_str(&t.cv.name)
            ));
        }
    }
    // containers: CONTAINER GROUPS (B4).  A container's whole recursor family —
    // its real members and its own mimics, instantiated at the pins — is among
    // our mimics (the kernel flattens nesting), so every mimic belongs to the
    // group of its container's family, in the container's motive order;
    // `pack`/`unpackPack` for a group are one application of each group
    // member's recursor with the group's motives.  A plain container is a
    // singleton group.
    let mimic_tags: Vec<u64> = fam
        .mems
        .iter()
        .filter(|m| m.real.is_none())
        .map(|m| m.tag)
        .collect();
    let mut groups: Vec<Group> = Vec::new();
    for mt in mimic_tags.iter() {
        let mem = &fam.mems[*mt as usize];
        if groups.iter().any(|g| g.tags.iter().any(|t| *t == mem.tag)) {
            continue;
        }
        let cb = (ctx.blocks)(&mem.i_name)
            .ok_or_else(|| format!("container {}: no block record", name_str(&mem.i_name)))?;
        let c_i0 = cb
            .types
            .first()
            .ok_or_else(|| format!("container {}: no block record", name_str(&mem.i_name)))?;
        let i1 = name::dup(&c_i0.cv.name);
        let lps_i: Vec<Name> = dup_names(&c_i0.cv.level_params);
        let n_pi = c_i0.n_p;
        if n_pi as usize != mem.pins.len() {
            return Err(format!(
                "container {}: parameter count",
                name_str(&mem.i_name)
            ));
        }
        if lps_i.len() != mem.lv.len() {
            return Err(format!("container {}: level count", name_str(&mem.i_name)));
        }
        let i1_rec = kit::nstr(name::dup(&i1), "rec");
        let r_i = cb
            .recs
            .iter()
            .find(|x| name::beq(&x.cv.name, &i1_rec))
            .ok_or_else(|| format!("container {}: no recursor", name_str(&i1)))?;
        let m_i = r_i.n_m;
        let (_, after_pi) = expr_ops::strip_pis(n_pi, &r_i.cv.ty)
            .ok_or_else(|| format!("container {}: recursor parameters", name_str(&i1)))?;
        let (motives_i, _) = expr_ops::strip_pis(m_i, &after_pi)
            .ok_or_else(|| format!("container {}: recursor motives", name_str(&i1)))?;
        let mems_i = read_mems(&lps_i, n_pi, &cb.types, &pi_binders(&motives_i))?;
        let fam_i = Family {
            t: name::dup(&i1),
            lps: dup_names(&lps_i),
            n_p: n_pi,
            pbs: Vec::new(),
            u: level::zero(),
            r: cb.types.len() as u64,
            mems: mems_i,
            ctors: Vec::new(),
            large: false,
            elim: name::anonymous(),
        };
        let mut tags: Vec<u64> = Vec::new();
        let mut rec_names: Vec<Name> = Vec::new();
        for mem_i in fam_i.mems.iter() {
            // the family member's carrier at the pins: instantiate the
            // container's parameters (under the member's index binders)
            let carr_i = carrier_at(
                &fam_i,
                mem_i,
                mem_i.n_idx,
                &vars_at(0, mem_i.n_idx),
                false,
            );
            // levels first (the container's level names may coincide with the
            // block's, which the pins mention), then the pins
            let carr = kit::subst_params(
                mem_i.n_idx,
                n_pi,
                &lift_all(mem_i.n_idx, &mem.pins),
                &expr_ops::instantiate_level_params(
                    &lps_i,
                    &mem.lv.iter().map(level::dup).collect(),
                    &carr_i,
                ),
            );
            let (t, _) = match_carrier(&fam, mem_i.n_idx, &carr).ok_or_else(|| {
                format!(
                    "container {}: family member {} at the pins is not among the mimics",
                    name_str(&mem.i_name),
                    name_str(&mem_i.i_name)
                )
            })?;
            tags.push(t);
            rec_names.push(match mem_i.real {
                Some(m) => kit::nstr(name::dup(&cb.types[m as usize].cv.name), "rec"),
                None => kit::nstr(name::dup(&i1), &format!("rec_{}", mem_i.j + 1)),
            });
        }
        let g_large = r_i.cv.level_params.len() == lps_i.len() + 1;
        groups.push(Group {
            tags,
            rec_names,
            lv: mem.lv.iter().map(level::dup).collect(),
            pins: dup_all(&mem.pins),
            n_pi,
            large: g_large,
        });
    }
    // dependency order among the groups: a group needs another when a field of
    // one of its constructors has a carrier outside the group
    let deps_of_group = |g: &Group| -> Vec<u64> {
        let mut acc: Vec<u64> = Vec::new();
        for c in fam.ctors.iter().filter(|c| g.tags.iter().any(|t| *t == c.mem)) {
            for k in c.kinds.iter() {
                if let Some(t) = k {
                    if *t >= r && !g.tags.iter().any(|x| x == t) {
                        acc.push(*t);
                    }
                }
            }
        }
        acc
    };
    let mut order: Vec<usize> = Vec::new();
    let mut pending: Vec<usize> = (0..groups.len()).collect();
    let mut progress = true;
    while progress && !pending.is_empty() {
        progress = false;
        let snapshot: Vec<usize> = pending.clone();
        for gi in snapshot {
            if !pending.iter().any(|x| *x == gi) {
                continue;
            }
            let ready = deps_of_group(&groups[gi]).iter().all(|d| {
                order
                    .iter()
                    .any(|oi| groups[*oi].tags.iter().any(|t| t == d))
            });
            if ready {
                order.push(gi);
                pending.retain(|x| *x != gi);
                progress = true;
            }
        }
    }
    if !pending.is_empty() {
        let shapes: Vec<String> = pending
            .iter()
            .map(|gi| format!("{:?}", groups[*gi].tags))
            .collect();
        return Err(format!(
            "the container groups form a cycle: [{}]",
            shapes.join(", ")
        ));
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
    let mut block_names: Vec<Name> = b.types.iter().map(|t| name::dup(&t.cv.name)).collect();
    for c in b.ctors.iter() {
        block_names.push(name::dup(&c.cv.name));
    }
    for rr in b.recs.iter() {
        block_names.push(name::dup(&rr.cv.name));
    }
    let gen = Gen {
        fam: &fam,
        big_m,
        n,
        tag: kit::tag_name(&t_name),
        aux: kit::aux_name(&t_name),
        l: level::dup(&l_elim),
        rlps: dup_names(&rlps),
        rlvls: rlvls.iter().map(level::dup).collect(),
        block_names,
        member_names: b.types.iter().map(|t| name::dup(&t.cv.name)).collect(),
    };
    let tag = name::dup(&gen.tag);
    let aux = name::dup(&gen.aux);
    let tag_rec_name = kit::nstr(name::dup(&tag), "rec");
    let aux_rec_name = kit::nstr(name::dup(&aux), "rec");
    let unpack_all = impl_name(&t_name, "unpack");
    let pack_unpack_all = impl_name(&t_name, "packUnpack");
    let rec_all = impl_name(&t_name, "rec");
    let mut out: Vec<Declaration> = Vec::new();
    let mut heights: Vec<(Name, u64)> = Vec::new();
    // -----------------------------------------------------------------
    // 1. the tag block
    let mut w: Level = level::succ(level::zero());
    for mem in fam.mems.iter() {
        for j in 0..mem.n_idx {
            let mut ctx_j = app2(
                dup_all(&pbs),
                &mem.idx_bs[..(j as usize).min(mem.idx_bs.len())],
            );
            ctx_j.reverse();
            let dom = get_d(&mem.idx_bs, j);
            let lj = kit::idx_sort(ctx.tbl, &ctx_j, &gen.rn(&dom)).ok_or_else(|| {
                format!(
                    "cannot bound the sort of index {} of member {} (the tag's universe)",
                    j, mem.tag
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
    for mem in fam.mems.iter() {
        let ty = need(
            "tag constructor type",
            expr_ops::replace_pi_body(
                n_p,
                &t0.cv.ty,
                &mk_pis(
                    &mem.idx_bs
                        .iter()
                        .map(|d| spec_all(&fam, 0, d))
                        .collect::<Vec<Expr>>(),
                    expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(mem.n_idx, n_p)),
                ),
            ),
        )?;
        tag_ctors.push(KCtor {
            name: tag_ctor_name(&t_name, mem.tag),
            n_f: mem.n_idx,
            ty,
            rec_idx: Vec::new(),
        });
    }
    let tag_rec_ty = need(
        "tag recursor type",
        kit::rec_ty(&tag, &lps, &elim_tag, true, n_p, 0, &tag_ty, &tag_ctors),
    )?;
    let mut tag_rlvls: Vec<Level> = vec![level::param(name::dup(&elim_tag))];
    for x in kit::params_of(&lps) {
        tag_rlvls.push(x);
    }
    let mut tag_rules: Vec<RecRule> = Vec::new();
    for mem in fam.mems.iter() {
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
                mem.tag,
            ),
        )?;
        tag_rules.push(env::rec_rule_parsed(
            tag_ctor_name(&t_name, mem.tag),
            mem.n_idx,
            rhs,
        ));
    }
    let mut tag_block: Vec<ConstantInfo> = vec![ConstantInfo::IndInfo(
        ConstantVal {
            name: name::dup(&tag),
            level_params: dup_names(&lps),
            ty: tag_ty,
        },
        env::ind_caps_default(),
    )];
    for c in tag_ctors.iter() {
        tag_block.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: name::dup(&c.name),
                level_params: dup_names(&lps),
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
            n_p + 1 + big_m,
            n_p + 1 + big_m,
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
                expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(0, n_p)),
                expr::sort(level::dup(&u)),
                bm(),
            ),
        ),
    )?;
    let mut aux_ctors: Vec<KCtor> = Vec::new();
    for c in fam.ctors.iter() {
        let doms2: Vec<Expr> = (0..c.n_f)
            .map(|i| spec_all(&fam, i, &get_d(&c.doms, i)))
            .collect();
        let ty = need(
            "aux constructor type",
            expr_ops::replace_pi_body(
                n_p,
                &t0.cv.ty,
                &mk_pis(&doms2, aux_at(&fam, c.mem, c.n_f, &c.idx)),
            ),
        )?;
        aux_ctors.push(KCtor {
            name: kit::aux_ctor_name(&t_name, c.mem, &c.cname),
            n_f: c.n_f,
            ty,
            rec_idx: (0..c.n_f)
                .filter(|i| gen.kind(c, *i).is_some())
                .collect(),
        });
    }
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
            level_params: dup_names(&lps),
            ty: aux_ty,
        },
        env::ind_caps_default(),
    )];
    for c in aux_ctors.iter() {
        aux_block.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: name::dup(&c.name),
                level_params: dup_names(&lps),
                ty: expr::dup(&c.ty),
            },
            n_p,
            c.n_f,
        ));
    }
    aux_block.push(ConstantInfo::RecInfo(
        ConstantVal {
            name: name::dup(&aux_rec_name),
            level_params: dup_names(&rlps),
            ty: aux_rec_ty,
        },
        n_p + 1 + n + 1,
        n_p + 1 + n,
        aux_rules,
    ));
    out.push(Declaration::IndDecl(aux_block, n_p));
    // 2b. the member models `T_m._model := λ p⃗ ı⃗, aux p⃗ (tag.m p⃗ ı⃗)` — the
    // model-side carriers of the mimics mention them
    for m in 0..r {
        let t = &b.types[m as usize];
        let n_i = t.n_idx;
        let value = need(
            "member model",
            expr_ops::pis_to_lams(
                n_p + n_i,
                &t.cv.ty,
                &aux_at(&fam, m, n_i, &vars_at(0, n_i)),
            ),
        )?;
        push_defn(
            &mut out,
            &mut heights,
            ctx,
            model_name(&t.cv.name),
            dup_names(&lps),
            expr::dup(&t.cv.ty),
            value,
        );
    }
    // 3. `_impl.unpack : ∀ p⃗ (i : tag p⃗) (s : aux p⃗ i), MotU i s`
    let unpack_all_ty = mk_pis(
        &app2(
            dup_all(&pbs),
            &[
                expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(0, n_p)),
                expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(vars_at(1, n_p), &[expr::bvar(0)]),
                ),
            ],
        ),
        expr_ops::mk_app_n(gen.mot_u(2), &vec![expr::bvar(1), expr::bvar(0)]),
    );
    let unpack_all_val = mk_lams(
        &pbs,
        expr_ops::mk_app_n(
            expr::mk_const(
                name::dup(&aux_rec_name),
                {
                    let mut v: Vec<Level> = if large {
                        vec![level::dup(&u)]
                    } else {
                        Vec::new()
                    };
                    for x in kit::params_of(&lps) {
                        v.push(x);
                    }
                    v
                },
            ),
            &app2(
                app2(vars_at(0, n_p), &[gen.mot_u(0)]),
                &gen.unpack_minors(0),
            ),
        ),
    );
    if !large && !is_prop {
        return Err("small eliminator on a non-Prop block".to_string());
    }
    push_defn(
        &mut out,
        &mut heights,
        ctx,
        name::dup(&unpack_all),
        dup_names(&lps),
        unpack_all_ty,
        unpack_all_val,
    );
    // 4. per container group, in dependency order: `pack_j` and `unpackPack_j`
    //    for every member by that member's container recursor at the group's
    //    motives, `unpack_j`/`congrPack_j` per member
    for gi in order.iter() {
        let g = &groups[*gi];
        if !g.large && !(level::is_equiv(&u, &level::zero()) == Some(true)) {
            return Err(format!(
                "container of group {:?} eliminates into Prop only but the block is not Prop",
                g.tags
            ));
        }
        for k in 0..g.tags.len() as u64 {
            let t = g.tags[k as usize];
            let mem = &fam.mems[t as usize];
            let j = mem.j;
            let n_i = mem.n_idx;
            let o0 = n_i + 1;
            let bs_x = app2(
                app2(dup_all(&pbs), &gen.idx_bs_at_m(mem, 0)),
                &[gen.carr_m(mem, n_i, &vars_at(0, n_i))],
            );
            let pack_ty = mk_pis(&bs_x, aux_at(&fam, t, o0, &vars_at(1, n_i)));
            let pack_val = mk_lams(
                &bs_x,
                expr_ops::mk_app_n(
                    gen.c_rec(g, k, &u),
                    &app2(
                        app2(
                            app2(
                                app2(gen.pins_at(g, o0), &gen.pack_motives(g, o0)),
                                &gen.pack_minors(g, o0),
                            ),
                            &vars_at(1, n_i),
                        ),
                        &[expr::bvar(0)],
                    ),
                ),
            );
            push_defn(
                &mut out,
                &mut heights,
                ctx,
                gen.impl_nm("pack", j),
                dup_names(&lps),
                pack_ty,
                pack_val,
            );
        }
        for t in g.tags.iter() {
            let mem = &fam.mems[*t as usize];
            let j = mem.j;
            let n_i = mem.n_idx;
            let o0 = n_i + 1;
            // `unpack_j`
            let bs_s = app2(
                app2(dup_all(&pbs), &gen.idx_bs_at_m(mem, 0)),
                &[aux_at(&fam, *t, n_i, &vars_at(0, n_i))],
            );
            let unpack_ty = mk_pis(&bs_s, gen.carr_m(mem, o0, &vars_at(1, n_i)));
            let unpack_val = mk_lams(
                &bs_s,
                expr_ops::mk_app_n(
                    const_p(&unpack_all, &lps),
                    &app2(
                        vars_at(o0, n_p),
                        &[
                            expr_ops::mk_app_n(
                                const_p(&tag_ctor_name(&t_name, *t), &lps),
                                &app2(vars_at(o0, n_p), &vars_at(1, n_i)),
                            ),
                            expr::bvar(0),
                        ],
                    ),
                ),
            );
            push_defn(
                &mut out,
                &mut heights,
                ctx,
                gen.impl_nm("unpack", j),
                dup_names(&lps),
                unpack_ty,
                unpack_val,
            );
            // `congrPack_j`
            let carr_at_o = |o: u64| gen.carr_m(mem, o, &vars_at(sub(o, n_i), n_i));
            let cp_bs = app2(
                app2(dup_all(&pbs), &gen.idx_bs_at_m(mem, 0)),
                &[
                    carr_at_o(n_i),
                    carr_at_o(n_i + 1),
                    mk_eq(
                        &u,
                        carr_at_o(n_i + 2),
                        expr::bvar(1),
                        expr::bvar(0),
                    ),
                ],
            );
            let pack_app = |o: u64, x: Expr| {
                gen.app_impl(
                    &gen.impl_nm("pack", j),
                    o,
                    &vars_at(sub(o, n_i), n_i),
                    &[x],
                )
            };
            let cp_ty = mk_pis(
                &cp_bs,
                mk_eq(
                    &u,
                    aux_at(&fam, *t, n_i + 3, &vars_at(3, n_i)),
                    pack_app(n_i + 3, expr::bvar(2)),
                    pack_app(n_i + 3, expr::bvar(1)),
                ),
            );
            let cp_val = mk_lams(
                &cp_bs,
                mk_eq_rec(
                    &level::zero(),
                    &u,
                    carr_at_o(n_i + 3),
                    expr::bvar(2),
                    expr::lam(
                        carr_at_o(n_i + 3),
                        expr::lam(
                            mk_eq(
                                &u,
                                carr_at_o(n_i + 4),
                                expr::bvar(3),
                                expr::bvar(0),
                            ),
                            mk_eq(
                                &u,
                                aux_at(&fam, *t, n_i + 5, &vars_at(5, n_i)),
                                pack_app(n_i + 5, expr::bvar(4)),
                                pack_app(n_i + 5, expr::bvar(1)),
                            ),
                            bm(),
                        ),
                        bm(),
                    ),
                    mk_refl(
                        &u,
                        aux_at(&fam, *t, n_i + 3, &vars_at(3, n_i)),
                        pack_app(n_i + 3, expr::bvar(2)),
                    ),
                    expr::bvar(1),
                    expr::bvar(0),
                ),
            );
            push_defn(
                &mut out,
                &mut heights,
                ctx,
                gen.impl_nm("congrPack", j),
                dup_names(&lps),
                cp_ty,
                cp_val,
            );
        }
        // `unpackPack_j` for every member, by its container recursor into Prop
        for k in 0..g.tags.len() as u64 {
            let t = g.tags[k as usize];
            let mem = &fam.mems[t as usize];
            let n_i = mem.n_idx;
            let o0 = n_i + 1;
            let bs_x = app2(
                app2(dup_all(&pbs), &gen.idx_bs_at_m(mem, 0)),
                &[gen.carr_m(mem, n_i, &vars_at(0, n_i))],
            );
            let up_ty = mk_pis(
                &bs_x,
                gen.up_stmt_of(mem, o0, &vars_at(1, n_i), expr::bvar(0)),
            );
            let up_val = mk_lams(
                &bs_x,
                expr_ops::mk_app_n(
                    gen.c_rec(g, k, &level::zero()),
                    &app2(
                        app2(
                            app2(
                                app2(gen.pins_at(g, o0), &gen.up_motives(g, o0)),
                                &gen.up_minors(g, o0),
                            ),
                            &vars_at(1, n_i),
                        ),
                        &[expr::bvar(0)],
                    ),
                ),
            );
            out.push(Declaration::ThmDecl(
                ConstantVal {
                    name: gen.impl_nm("unpackPack", mem.j),
                    level_params: dup_names(&lps),
                    ty: up_ty,
                },
                up_val,
            ));
        }
    }
    // 5. `_impl.packUnpack : ∀ p⃗ i s, MotPU i s` (all mimics at once)
    let pu_ty = mk_pis(
        &app2(
            dup_all(&pbs),
            &[
                expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(0, n_p)),
                expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(vars_at(1, n_p), &[expr::bvar(0)]),
                ),
            ],
        ),
        expr_ops::mk_app_n(gen.mot_pu(2), &vec![expr::bvar(1), expr::bvar(0)]),
    );
    let pu_val = mk_lams(
        &pbs,
        expr_ops::mk_app_n(
            expr::mk_const(name::dup(&aux_rec_name), {
                let mut v: Vec<Level> = if large {
                    vec![level::zero()]
                } else {
                    Vec::new()
                };
                for x in kit::params_of(&lps) {
                    v.push(x);
                }
                v
            }),
            &app2(
                app2(vars_at(0, n_p), &[gen.mot_pu(0)]),
                &gen.pu_minors(0),
            ),
        ),
    );
    out.push(Declaration::ThmDecl(
        ConstantVal {
            name: name::dup(&pack_unpack_all),
            level_params: dup_names(&lps),
            ty: pu_ty,
        },
        pu_val,
    ));
    for mt in mimic_tags.iter() {
        let mem = &fam.mems[*mt as usize];
        let t = mem.tag;
        let n_i = mem.n_idx;
        let o0 = n_i + 1;
        let idx = vars_at(1, n_i);
        let bs = app2(
            app2(dup_all(&pbs), &gen.idx_bs_at_m(mem, 0)),
            &[aux_at(&fam, t, n_i, &vars_at(0, n_i))],
        );
        let ty = mk_pis(
            &bs,
            mk_eq(
                &u,
                aux_at(&fam, t, o0, &idx),
                gen.app_impl(
                    &gen.impl_nm("pack", mem.j),
                    o0,
                    &idx,
                    &[gen.app_impl(
                        &gen.impl_nm("unpack", mem.j),
                        o0,
                        &idx,
                        &[expr::bvar(0)],
                    )],
                ),
                expr::bvar(0),
            ),
        );
        let v = mk_lams(
            &bs,
            expr_ops::mk_app_n(
                const_p(&pack_unpack_all, &lps),
                &app2(
                    vars_at(o0, n_p),
                    &[
                        expr_ops::mk_app_n(
                            const_p(&tag_ctor_name(&t_name, t), &lps),
                            &app2(vars_at(o0, n_p), &idx),
                        ),
                        expr::bvar(0),
                    ],
                ),
            ),
        );
        out.push(Declaration::ThmDecl(
            ConstantVal {
                name: gen.impl_nm("packUnpack", mem.j),
                level_params: dup_names(&lps),
                ty,
            },
            v,
        ));
    }
    // -----------------------------------------------------------------
    // 6. the constructor models
    for c in fam.ctors.iter() {
        if c.mem < r {
            let pc = b
                .ctors
                .iter()
                .find(|x| name::beq(&x.cv.name, &c.cname))
                .ok_or_else(|| "unreachable".to_string())?;
            let ty = gen.rn(&pc.cv.ty);
            let n_f = c.n_f;
            let args: Vec<Expr> = (0..n_f)
                .map(|i| match gen.kind(c, i) {
                    Some(t2) => {
                        if t2 >= r {
                            gen.app_impl(
                                &gen.impl_nm("pack", fam.mems[t2 as usize].j),
                                n_f,
                                &gen.field_idx(c, i, sub(n_f, i)),
                                &[expr::bvar(sub(sub(n_f, 1), i))],
                            )
                        } else {
                            expr::bvar(sub(sub(n_f, 1), i))
                        }
                    }
                    None => expr::bvar(sub(sub(n_f, 1), i)),
                })
                .collect();
            let value = need(
                "constructor model",
                expr_ops::pis_to_lams(
                    n_p + n_f,
                    &ty,
                    &expr_ops::mk_app_n(
                        const_p(&gen.aux_ctor_name_of(c), &lps),
                        &app2(vars_at(n_f, n_p), &args),
                    ),
                ),
            )?;
            push_defn(
                &mut out,
                &mut heights,
                ctx,
                model_name(&c.cname),
                dup_names(&lps),
                ty,
                value,
            );
        }
    }
    // 7. `_impl.rec : ∀ p⃗ M⃗ S⃗ (i : tag p⃗) (s : aux p⃗ i), MotR i s`
    let r_p = n_p + big_m + n;
    let (prefix_bs, _) = expr_ops::strip_pis(r_p, &gen.rn(&r0.cv.ty))
        .ok_or_else(|| "recursor prefix".to_string())?;
    let prefix_bs_l = pi_binders(&prefix_bs);
    let rec_all_ty = mk_pis(
        &app2(
            dup_all(&prefix_bs_l),
            &[
                expr_ops::mk_app_n(const_p(&tag, &lps), &vars_at(big_m + n, n_p)),
                expr_ops::mk_app_n(
                    const_p(&aux, &lps),
                    &app2(vars_at(big_m + n + 1, n_p), &[expr::bvar(0)]),
                ),
            ],
        ),
        expr_ops::mk_app_n(gen.mot_r(2), &vec![expr::bvar(1), expr::bvar(0)]),
    );
    let rec_all_val = mk_lams(
        &prefix_bs_l,
        expr_ops::mk_app_n(
            expr::mk_const(
                name::dup(&aux_rec_name),
                rlvls.iter().map(level::dup).collect(),
            ),
            &app2(
                app2(vars_at(big_m + n, n_p), &[gen.mot_r(0)]),
                &gen.rec_minors(0),
            ),
        ),
    );
    push_defn(
        &mut out,
        &mut heights,
        ctx,
        name::dup(&rec_all),
        dup_names(&rlps),
        rec_all_ty,
        rec_all_val,
    );
    // 8. the recursor models
    for mem in fam.mems.iter() {
        let rr = rec_of(mem.real, mem.j)?;
        let ty = gen.rn(&rr.cv.ty);
        let n_i = mem.n_idx;
        let d = r_p + n_i + 1;
        let e = n_i + 1;
        let prefix_vars = app2(
            app2(vars_at(e + big_m + n, n_p), &vars_at(e + n, big_m)),
            &vars_at(e, n),
        );
        let tag_app = expr_ops::mk_app_n(
            const_p(&tag_ctor_name(&t_name, mem.tag), &lps),
            &app2(vars_at(e + big_m + n, n_p), &vars_at(1, n_i)),
        );
        let body = match mem.real {
            Some(_) => expr_ops::mk_app_n(
                const_p(&rec_all, &rlps),
                &app2(dup_all(&prefix_vars), &[tag_app, expr::bvar(0)]),
            ),
            None => {
                let idx = vars_at(1, n_i);
                let o_p = e + big_m + n;
                let pack_x = gen.app_impl(
                    &gen.impl_nm("pack", mem.j),
                    o_p,
                    &idx,
                    &[expr::bvar(0)],
                );
                let carr = gen.carr_m(mem, o_p, &idx);
                let inner = expr_ops::mk_app_n(
                    const_p(&rec_all, &rlps),
                    &app2(
                        dup_all(&prefix_vars),
                        &[tag_app, expr::dup(&pack_x)],
                    ),
                );
                let up = gen.app_impl(
                    &gen.impl_nm("unpack", mem.j),
                    o_p,
                    &idx,
                    &[pack_x],
                );
                mk_eq_rec(
                    &l_elim,
                    &u,
                    expr::dup(&carr),
                    expr::dup(&up),
                    expr::lam(
                        expr::dup(&carr),
                        expr::lam(
                            mk_eq(
                                &u,
                                expr_ops::lift_loose_bvars(1, 0, &carr),
                                expr_ops::lift_loose_bvars(1, 0, &up),
                                expr::bvar(0),
                            ),
                            expr_ops::mk_app_n(
                                gen.mot_var(e + 2, mem.tag),
                                &app2(lift_all(2, &idx), &[expr::bvar(1)]),
                            ),
                            bm(),
                        ),
                        bm(),
                    ),
                    inner,
                    expr::bvar(0),
                    gen.app_impl(
                        &gen.impl_nm("unpackPack", mem.j),
                        o_p,
                        &idx,
                        &[expr::bvar(0)],
                    ),
                )
            }
        };
        let value = need("recursor model", expr_ops::pis_to_lams(d, &ty, &body))?;
        push_defn(
            &mut out,
            &mut heights,
            ctx,
            model_name(&rr.cv.name),
            dup_names(&rlps),
            ty,
            value,
        );
    }
    // 9. the iota theorems
    for mem in fam.mems.iter() {
        let rr = rec_of(mem.real, mem.j)?;
        let own: Vec<&ACtor> = fam.ctors.iter().filter(|c| c.mem == mem.tag).collect();
        for c in own.into_iter() {
            let n_f = c.n_f;
            // statement frame: prefix (rP) then the fields
            let o_p = n_f + big_m + n; // below the parameters at the statement's end
            let field_bs = gen.model_doms(c, big_m + n);
            let fields: Vec<Expr> = (0..n_f).map(|i| expr::bvar(sub(sub(n_f, 1), i))).collect();
            let prefix_vars = app2(
                app2(
                    vars_at(n_f + big_m + n, n_p),
                    &vars_at(n_f + n, big_m),
                ),
                &vars_at(n_f, n),
            );
            let idx_c: Vec<Expr> = c
                .idx
                .iter()
                .map(|e| {
                    expr_ops::lift_loose_bvars(big_m + n, n_f, &gen.rn(e))
                })
                .collect();
            let ctor_app = match mem.real {
                Some(_) => expr_ops::mk_app_n(
                    const_p(&model_name(&c.cname), &lps),
                    &app2(vars_at(o_p, n_p), &fields),
                ),
                None => {
                    let pins = expr_ops::get_app_args(&gen.carr_m(mem, o_p, &[]));
                    expr_ops::mk_app_n(
                        expr::mk_const(
                            name::dup(&c.cname),
                            c.clv.iter().map(level::dup).collect(),
                        ),
                        &app2(
                            dup_all(&pins[..mem.pins.len().min(pins.len())]),
                            &fields,
                        ),
                    )
                }
            };
            let packed: Vec<u64> = (0..n_f)
                .filter(|i| match gen.kind(c, *i) {
                    Some(t2) => t2 >= r,
                    None => false,
                })
                .collect();
            let iota = Iota {
                g: &gen,
                mem,
                c,
                n_f,
                o_p,
                idx_c: dup_all(&idx_c),
                prefix_vars: dup_all(&prefix_vars),
                packed: packed.clone(),
                rec_all: name::dup(&rec_all),
            };
            let alpha = expr_ops::mk_app_n(
                expr::bvar(n_f + n + sub(sub(big_m, 1), mem.tag)),
                &app2(dup_all(&idx_c), &[expr::dup(&ctor_app)]),
            );
            let lhs = expr_ops::mk_app_n(
                expr::mk_const(
                    model_name(&rr.cv.name),
                    rlvls.iter().map(level::dup).collect(),
                ),
                &app2(
                    app2(dup_all(&prefix_vars), &idx_c),
                    &[expr::dup(&ctor_app)],
                ),
            );
            let rhs = expr_ops::mk_app_n(
                expr::bvar(n_f + sub(sub(n, 1), c.big_j)),
                &app2(
                    dup_all(&fields),
                    &(0..n_f)
                        .filter_map(|i| {
                            if gen.kind(c, i).is_some() {
                                Some(iota.ih_app(i))
                            } else {
                                None
                            }
                        })
                        .collect::<Vec<Expr>>(),
                ),
            );
            let stmt = mk_pis(
                &app2(dup_all(&prefix_bs_l), &field_bs),
                mk_eq(&l_elim, expr::dup(&alpha), expr::dup(&lhs), rhs),
            );
            let proof = if packed.is_empty() {
                need(
                    "iota proof",
                    expr_ops::pis_to_lams(r_p + n_f, &stmt, &mk_refl(&l_elim, alpha, lhs)),
                )?
            } else {
                let none_v: Vec<Option<Expr>> = (0..n_f).map(|_| None).collect();
                let body = iota.nest(&packed, 0, &none_v, &none_v);
                need("iota proof", expr_ops::pis_to_lams(r_p + n_f, &stmt, &body))?
            };
            out.push(Declaration::ThmDecl(
                ConstantVal {
                    name: iota_name(&rr.cv.name, c.j_in),
                    level_params: dup_names(&rlps),
                    ty: stmt,
                },
                proof,
            ));
        }
    }
    // 10. projection artifacts of structure-like non-Prop real members (under a
    // LARGE eliminator only: `mutual::gen_mutual` step 7)
    let mut gen_types: Vec<(Name, Vec<Name>, Expr)> = Vec::new();
    for t in b.types.iter() {
        gen_types.push((
            model_name(&t.cv.name),
            dup_names(&lps),
            expr::dup(&t.cv.ty),
        ));
    }
    for c in b.ctors.iter() {
        gen_types.push((model_name(&c.cv.name), dup_names(&lps), gen.rn(&c.cv.ty)));
    }
    let tbl2 = |x: &Name| -> Option<(Vec<Name>, Expr)> {
        match gen_types.iter().find(|g| name::beq(&g.0, x)) {
            Some((_, l, ty)) => Some((dup_names(l), expr::dup(ty))),
            None => (ctx.tbl)(x),
        }
    };
    if !is_prop && large {
        for m in 0..r {
            let t = &b.types[m as usize];
            let own: Vec<&ACtor> = fam.ctors.iter().filter(|c| c.mem == m).collect();
            if own.len() != 1 {
                continue;
            }
            let c = own[0];
            if t.n_idx != 0 {
                continue;
            }
            let n_f = c.n_f;
            let pc = match b.ctors.iter().find(|x| name::beq(&x.cv.name, &c.cname)) {
                Some(pc) => pc,
                None => continue,
            };
            let cty = gen.rn(&pc.cv.ty);
            let cbs = match expr_ops::strip_pis(n_p + n_f, &cty) {
                Some((cbs, _)) => cbs,
                None => continue,
            };
            let cbs_doms = pi_binders(&cbs);
            let mut stop = false;
            for i in 0..n_f {
                if stop {
                    continue;
                }
                let mut ctx_i = pi_binders(&cbs[..((n_p + i) as usize).min(cbs.len())]);
                ctx_i.reverse();
                let dom = get_d(&cbs_doms, n_p + i);
                let li = match kit::sort_of(&tbl2, &ctx_i, &dom) {
                    Some(l) => l,
                    None => {
                        stop = true;
                        continue;
                    }
                };
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
                        expr_ops::mk_app_n(
                            const_p(&model_name(&t.cv.name), &lps),
                            &vars_at(0, n_p),
                        ),
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
                // the value: `λ p⃗ x, aux.rec p⃗ MotP minorsP (tag.m p⃗) x`
                let mot_p = |o: u64| -> Expr {
                    gen.dispatch_motive(o, &li, &|o2: u64| {
                        fam.mems
                            .iter()
                            .map(|mem| {
                                let s_at = |o3: u64| {
                                    aux_at(
                                        &fam,
                                        mem.tag,
                                        o3,
                                        &vars_at(sub(o3, o2 + mem.n_idx), mem.n_idx),
                                    )
                                };
                                mk_lams(
                                    &app2(
                                        gen.idx_bs_at(mem, o2),
                                        &[s_at(o2 + mem.n_idx)],
                                    ),
                                    if mem.tag == m {
                                        // `F_i[f_j := proj_j p⃗ s]`, at frame o2 + 1
                                        let mut args_s = struct_parts::struct_proj_ps(n_p);
                                        for j in 0..i {
                                            args_s.push(expr_ops::mk_app_n(
                                                const_p(
                                                    &core_k::proj_model_name(&t.cv.name, j),
                                                    &lps,
                                                ),
                                                &app2(
                                                    struct_parts::struct_proj_ps(n_p),
                                                    &[expr::bvar(0)],
                                                ),
                                            ));
                                        }
                                        match expr_ops::inst_pis_at_lift(&args_s, &cty) {
                                            Some(e) => match expr::view(&e) {
                                                // `fd` is at frame `p⃗, x`: lift
                                                // the parameters past the extras
                                                ExprView::ForallE(fd, _, _) => {
                                                    expr_ops::lift_loose_bvars(o2, 1, fd)
                                                }
                                                _ => expr::sort(level::zero()),
                                            },
                                            None => expr::sort(level::zero()),
                                        }
                                    } else {
                                        expr::mk_const(
                                            bnm::punit_name(),
                                            vec![level::dup(&li)],
                                        )
                                    },
                                )
                            })
                            .collect()
                    })
                };
                let minors_p = |o: u64| -> Vec<Expr> {
                    fam.ctors
                        .iter()
                        .map(|c2| {
                            let n_ih = gen.n_ih_of(c2);
                            let fbs = gen.spec_doms(c2, o);
                            let ihbs: Vec<Expr> = (0..c2.n_f)
                                .filter_map(|i2| match gen.kind(c2, i2) {
                                    Some(t2) => {
                                        let k = gen.ih_pos(c2, i2);
                                        let fo2 = c2.n_f + k;
                                        Some(expr_ops::mk_app_n(
                                            mot_p(o + fo2),
                                            &vec![
                                                expr_ops::mk_app_n(
                                                    const_p(
                                                        &tag_ctor_name(&t_name, t2),
                                                        &lps,
                                                    ),
                                                    &app2(
                                                        vars_at(o + fo2, n_p),
                                                        &gen.field_idx(
                                                            c2,
                                                            i2,
                                                            sub(fo2, i2),
                                                        ),
                                                    ),
                                                ),
                                                expr::bvar(sub(sub(fo2, 1), i2)),
                                            ],
                                        ))
                                    }
                                    None => None,
                                })
                                .collect();
                            let fo = c2.n_f + n_ih;
                            let field_var =
                                |i2: u64| expr::bvar(sub(sub(n_ih + c2.n_f, 1), i2));
                            let body = if c2.mem == m {
                                match gen.kind(c2, i) {
                                    Some(t2) => {
                                        if t2 >= r {
                                            gen.app_impl(
                                                &gen.impl_nm(
                                                    "unpack",
                                                    fam.mems[t2 as usize].j,
                                                ),
                                                o + fo,
                                                &gen.field_idx(c2, i, sub(fo, i)),
                                                &[field_var(i)],
                                            )
                                        } else {
                                            field_var(i)
                                        }
                                    }
                                    None => field_var(i),
                                }
                            } else {
                                expr::mk_const(
                                    bnm::punit_unit_name(),
                                    vec![level::dup(&li)],
                                )
                            };
                            mk_lams(&app2(fbs, &ihbs), body)
                        })
                        .collect()
                };
                let pval = mk_lams(
                    &app2(
                        dup_all(&pbs),
                        &[expr_ops::mk_app_n(
                            const_p(&model_name(&t.cv.name), &lps),
                            &vars_at(0, n_p),
                        )],
                    ),
                    expr_ops::mk_app_n(
                        expr::mk_const(name::dup(&aux_rec_name), {
                            let mut v: Vec<Level> = if large {
                                vec![level::dup(&li)]
                            } else {
                                Vec::new()
                            };
                            for x in kit::params_of(&lps) {
                                v.push(x);
                            }
                            v
                        }),
                        &app2(
                            app2(
                                app2(vars_at(1, n_p), &[mot_p(1)]),
                                &minors_p(1),
                            ),
                            &[
                                expr_ops::mk_app_n(
                                    const_p(&tag_ctor_name(&t_name, m), &lps),
                                    &vars_at(1, n_p),
                                ),
                                expr::bvar(0),
                            ],
                        ),
                    ),
                );
                push_defn(
                    &mut out,
                    &mut heights,
                    ctx,
                    core_k::proj_model_name(&t.cv.name, i),
                    dup_names(&lps),
                    pty,
                    pval,
                );
                // `proj_i.iota`
                let fields: Vec<Expr> =
                    (0..n_f).map(|l| expr::bvar(sub(sub(n_f, 1), l))).collect();
                let slot = expr_ops::lift_loose_bvars(sub(n_f, i), 0, &dom);
                let lhs = expr_ops::mk_app_n(
                    const_p(&core_k::proj_model_name(&t.cv.name, i), &lps),
                    &app2(
                        vars_at(n_f, n_p),
                        &[expr_ops::mk_app_n(
                            const_p(&model_name(&c.cname), &lps),
                            &app2(vars_at(n_f, n_p), &fields),
                        )],
                    ),
                );
                let stmt = mk_pis(
                    &cbs_doms,
                    mk_eq(
                        &li,
                        expr::dup(&slot),
                        lhs,
                        expr::bvar(sub(sub(n_f, 1), i)),
                    ),
                );
                let pf = match gen.kind(c, i) {
                    Some(t2) => {
                        if t2 >= r {
                            gen.app_impl(
                                &gen.impl_nm("unpackPack", fam.mems[t2 as usize].j),
                                n_f,
                                &gen
                                    .field_idx(c, i, sub(n_f, i))
                                    .iter()
                                    .map(|e| gen.rn(e))
                                    .collect::<Vec<Expr>>(),
                                &[expr::bvar(sub(sub(n_f, 1), i))],
                            )
                        } else {
                            mk_refl(&li, expr::dup(&slot), expr::bvar(sub(sub(n_f, 1), i)))
                        }
                    }
                    None => mk_refl(&li, expr::dup(&slot), expr::bvar(sub(sub(n_f, 1), i))),
                };
                let pf_l = match expr_ops::pis_to_lams(n_p + n_f, &stmt, &pf) {
                    Some(v) => v,
                    None => {
                        stop = true;
                        continue;
                    }
                };
                out.push(Declaration::ThmDecl(
                    ConstantVal {
                        name: kit::nstr(core_k::proj_model_name(&t.cv.name, i), "iota"),
                        level_params: dup_names(&lps),
                        ty: stmt,
                    },
                    pf_l,
                ));
            }
        }
    }
    Ok(out)
}
