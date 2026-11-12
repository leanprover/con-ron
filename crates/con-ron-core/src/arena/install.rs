//! `arena::install` — what a declaration adds.
//!
//! The port of `ConLeche/Kernel/Install.lean` over handles: a declaration's
//! constants and projection tables are a direct consequence of the
//! declaration, read off it with no environment, no inference and no
//! reduction.  The block's check pushes exactly this once its checks pass
//! (`block_tail::check_block`), and the stream's index is built from it
//! before any check runs (the driver's `decl_constants`/`decl_tables`).
//!
//! A block the checks reject may still read as something here (a recursor
//! whose major is not a container reads as firing `.plain`, a block with a
//! structure whose constructor is too short has no tables): what it reads as
//! never reaches an accepted environment.
//!
//! ## The port's deviations
//!
//! * **`Env.pushDelta` and `FEnv.pushDelta` are one function** over the one
//!   environment type, `IFEnv` (task #97c's deviation 1).
//! * **Every reader takes the store**: a term is read through `view`, and the
//!   pins' renamings (`quot_at`) and `Expr.dropVars`'s
//!   instantiation intern, so the functions return `Result` where con-leche's
//!   are total.  Run on the driver's store before the freeze, what they intern
//!   is persistent.
//! * **The `map`/`zipIdx` closures are index recursions** (§3.4).

use crate::arena::basis;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IDeclaration, IFEnv, IProjTable, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::inductives::block_install;
use crate::arena::inductives::block_shape;
use crate::arena::inductives::block_shape::{BlockShape, MemberShape, RecShape};
use crate::arena::inductives::struct_parts;
use crate::arena::monad::{fail_dangling_e, intern_e_sort, view_bind, view_const, view_ls, AState};
use crate::arena::pins;
use crate::arena::store::PersTier;
use crate::arena::stream_index;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::{reducibility_hint_dup, QuotKind};
use crate::kernel::expr_ops::sub_nat;
use crate::ron::hashmap::{Dup, Eq2};

/// con-leche: ConLeche/Kernel/Install.lean:22-24 Env.pushDelta
/// con-leche: ConLeche/Kernel/FEnv.lean:155-160 FEnv.pushDelta
/// **The environment with a declaration's constants and tables pushed**, each
/// list oldest first: the constants, then the tables (a constant push and a
/// table push touch different components, so the order between them is not
/// observable).
pub fn push_delta(fe: IFEnv, l: Vec<IConstantInfo>, q: Vec<IProjTable>) -> IFEnv {
    let fe1: IFEnv = push_delta_consts(fe, l, 0);
    push_delta_tables(fe1, q, 0)
}

/// con-leche: ConLeche/Kernel/FEnv.lean:150-153 FEnv.pushAll
/// Push a list of records from `i` on, head first.
pub fn push_delta_consts(fe: IFEnv, l: Vec<IConstantInfo>, i: usize) -> IFEnv {
    if i >= l.len() {
        fe
    } else {
        let ci: IConstantInfo = env::i_constant_info_dup(&l[i]);
        push_delta_consts(env::ifenv_push(fe, ci), l, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:143-148 FEnv.pushTables
/// The tables from `i` on, pushed in order.
pub fn push_delta_tables(fe: IFEnv, q: Vec<IProjTable>, i: usize) -> IFEnv {
    if i >= q.len() {
        fe
    } else {
        let t: IProjTable = stream_index::i_proj_table_dup(&q[i]);
        push_delta_tables(env::ifenv_push_table(fe, t), q, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:26-28 blockFormers
/// **The formers** from member `i` on, in block order, as declared, with the
/// capabilities their block gives them.
pub fn block_formers(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    is_rec: bool,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, CheckError> {
    if i >= p.members.len() {
        Ok(out)
    } else {
        match block_install::block_caps_at(pers, st, p, i as u64, is_rec) {
            Err(e) => Err(e),
            Ok(caps) => {
                let mut o: Vec<IConstantInfo> = out;
                o.push(IConstantInfo::IndInfo(env::i_constant_val_dup(&p.members[i].declared), caps));
                block_formers(pers, st, p, is_rec, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:30-33 blockCtors
/// **The constructors of every member**, as declared, in block order, each
/// under its member's name (the groups `p.ctorGroups` from `i` on).
pub fn block_ctors(
    n_p: u64,
    gs: &Vec<(NIdx, Vec<(IConstantVal, u64)>)>,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Vec<IConstantInfo> {
    if i >= gs.len() {
        out
    } else {
        let o: Vec<IConstantInfo> = block_ctors_group(n_p, &gs[i].0, &gs[i].1, 0, out);
        block_ctors(n_p, gs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:30-33 blockCtors
/// One group of `block_ctors`: the inner `g.2.map`, constructor `j` on, each
/// with its member's name `t` as its `induct`.
pub fn block_ctors_group(
    n_p: u64,
    t: &NIdx,
    cs: &Vec<(IConstantVal, u64)>,
    j: usize,
    out: Vec<IConstantInfo>,
) -> Vec<IConstantInfo> {
    if j >= cs.len() {
        out
    } else {
        let mut o: Vec<IConstantInfo> = out;
        o.push(IConstantInfo::CtorInfo(env::i_constant_val_dup(&cs[j].0), n_p, cs[j].1, t.dup2()));
        block_ctors_group(n_p, t, cs, j + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:35-38 Expr.dropVars
/// con-leche: ConLeche/Cached/CheckerC.lean:73-77 Expr.dropVarsC
/// **`n` variables below a term's own, which do not occur in it, dropped**:
/// each instantiated at `Sort 0`.
pub fn expr_drop_vars(pers: &PersTier, st: &mut AState, n: u64, e: EIdx) -> Result<EIdx, CheckError> {
    if n == 0 {
        Ok(e)
    } else {
        match core::zero_level(st) {
            Err(er) => Err(er),
            Ok(z) => match intern_e_sort(pers, st, z) {
                Err(er) => Err(er),
                Ok(s0) => match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &e, &s0, 0) {
                    Err(er) => Err(er),
                    Ok(e2) => expr_drop_vars(pers, st, n - 1, e2),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:35-38 Expr.dropVars
/// con-leche: ConLeche/Cached/CheckerC.lean:73-77 Expr.dropVarsC
/// `xs.map (Expr.dropVars n)`, from `i` on.
pub fn drop_vars_all(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match expr_drop_vars(pers, st, n, xs[i].dup2()) {
            Err(e) => Err(e),
            Ok(x) => {
                let mut o: Vec<EIdx> = out;
                o.push(x);
                drop_vars_all(pers, st, n, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:40-55 recFire
/// con-leche: ConLeche/Cached/CheckerC.lean:79-91 recFireC
/// **How a recursor's rules fire**: `.plain` at a member major; at a major
/// outside the block, `.nested` at the levels and parameters of the major's
/// container.  Those are read off the major's domain, whose arguments end in
/// the `mI - rP` index variables; the parameters are moved from under the
/// index binders to the rule prefix.
pub fn rec_fire(pers: &PersTier, st: &mut AState, p: &BlockShape, rc: &RecShape) -> Result<IRecRuleFire, CheckError> {
    if rc.tgt < block_shape::shape_k(p) {
        Ok(IRecRuleFire::Plain)
    } else {
        match expr_ops::strip_pis(pers, st, rc.m_i, &rc.cv_r.ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(IRecRuleFire::Plain),
            Ok(Some(q)) => {
                if q.1.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &q.1) {
                        None => fail_dangling_e(),
                        Some((dom, _)) => rec_fire_dom(pers, st, rc, &dom),
                    }
                } else {
                    Ok(IRecRuleFire::Plain)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:40-55 recFire
/// con-leche: ConLeche/Cached/CheckerC.lean:79-91 recFireC
/// `recFire`'s major-domain arm: at a constant head, `.nested` at its levels
/// and its leading arguments, the index variables dropped.
pub fn rec_fire_dom(pers: &PersTier, st: &mut AState, rc: &RecShape, dom: &EIdx) -> Result<IRecRuleFire, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_CONST {
                match view_const(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some((_, us)) => match view_ls(pers, st, &us) {
                        Err(e) => Err(e),
                        Ok(lvls) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, dom) {
                            Err(e) => Err(e),
                            Ok(args) => {
                                let n_i: u64 = sub_nat(rc.m_i, rc.r_p);
                                let lead: Vec<EIdx> = expr_ops::take_eidx_n(&args, sub_nat(args.len() as u64, n_i));
                                match drop_vars_all(pers, st, n_i, &lead, 0, Vec::new()) {
                                    Err(e) => Err(e),
                                    Ok(ps) => {
                                        let ls: Vec<LIdx> = lvls;
                                        Ok(IRecRuleFire::Nested(ls, ps))
                                    }
                                }
                            }
                        },
                    },
                }
            } else {
                Ok(IRecRuleFire::Plain)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:57-62 blockRecs
/// con-leche: ConLeche/Cached/CheckerC.lean:93-98 blockRecsC
/// `rc.rules.map ({ · with fire := f })`, from `i` on.
pub fn rules_with_fire(rules: &Vec<IRecRule>, f: &IRecRuleFire, i: usize, out: Vec<IRecRule>) -> Vec<IRecRule> {
    if i >= rules.len() {
        out
    } else {
        let mut o: Vec<IRecRule> = out;
        o.push(IRecRule {
            ctor: rules[i].ctor.dup2(),
            nfields: rules[i].nfields,
            fire: env::i_rec_rule_fire_dup(f),
            rhs: rules[i].rhs.dup2(),
        });
        rules_with_fire(rules, f, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:57-62 blockRecs
/// con-leche: ConLeche/Cached/CheckerC.lean:93-98 blockRecsC
/// **The recursors** from `i` on, in block order: each record with its rules'
/// firing mode.
pub fn block_recs(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    rs: &Vec<RecShape>,
    i: usize,
    out: Vec<IConstantInfo>,
) -> Result<Vec<IConstantInfo>, CheckError> {
    if i >= rs.len() {
        Ok(out)
    } else {
        match rec_fire(pers, st, p, &rs[i]) {
            Err(e) => Err(e),
            Ok(f) => {
                let rc: &RecShape = &rs[i];
                let mut o: Vec<IConstantInfo> = out;
                o.push(IConstantInfo::RecInfo(
                    env::i_constant_val_dup(&rc.cv_r),
                    rc.m_i,
                    rc.r_p,
                    rc.is_k,
                    rules_with_fire(&rc.rules, &f, 0, Vec::new()),
                ));
                block_recs(pers, st, p, rs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:64-75 blockTables
/// con-leche: ConLeche/Cached/CheckerC.lean:43-55 blockTablesC
/// **The projection tables** from member `i` on, in block order: one per
/// structure-like member, its bodies read off its constructor's type
/// (`struct_proj_bodies`).  `None` where a structure-like member's
/// constructor type is too short to read them (`check_block` rejects it).
pub fn block_tables(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<IProjTable>,
) -> Result<Option<Vec<IProjTable>>, CheckError> {
    if i >= ms.len() {
        Ok(Some(out))
    } else {
        match block_shape::member_struct_ctor(&ms[i]) {
            None => block_tables(pers, st, p, ms, i + 1, out),
            Some(c) => {
                let t: NIdx = ms[i].declared.name.dup2();
                match struct_parts::struct_proj_bodies(pers, st, &t, p.n_p, c.1, &c.0.ty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(bodies)) => {
                        let mut o: Vec<IProjTable> = out;
                        o.push(IProjTable {
                            struct_name: t,
                            level_params: block_shape::shape_lps(p),
                            num_params: p.n_p,
                            ctor: c.0.name.dup2(),
                            num_fields: c.1,
                            bodies,
                        });
                        block_tables(pers, st, p, ms, i + 1, o)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:77-80 blockConstants
/// con-leche: ConLeche/Cached/CheckerC.lean:99-102 blockConstantsC
/// **The block's constants**, in push order: the formers (at official's
/// `is_rec`, `blockIsRec`), the constructors, the recursors.
pub fn block_constants(pers: &PersTier, st: &mut AState, p: &BlockShape) -> Result<Vec<IConstantInfo>, CheckError> {
    match block_install::block_is_rec(pers, st, p) {
        Err(e) => Err(e),
        Ok(is_rec) => {
            let formers: Vec<IConstantInfo> = match block_formers(pers, st, p, is_rec, 0, Vec::new()) {
                Err(e) => return Err(e),
                Ok(v) => v,
            };
            let gs: Vec<(NIdx, Vec<(IConstantVal, u64)>)> = block_shape::ctor_groups(&p.members, 0, Vec::new());
            let with_ctors: Vec<IConstantInfo> = block_ctors(p.n_p, &gs, 0, formers);
            block_recs(pers, st, p, &p.recs, 0, with_ctors)
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:82-96 declConstants
/// con-leche: ConLeche/Cached/CheckerC.lean:104-118 declConstantsC
/// **The constants a declaration installs**, in push order.  A block
/// `readBlock` cannot read installs nothing (its check rejects it), and
/// `sorryAx` nothing (any use of it declines).
pub fn decl_constants(pers: &PersTier, st: &mut AState, pd: &IDeclaration) -> Result<Vec<IConstantInfo>, CheckError> {
    match pd {
        IDeclaration::DefnDecl(cv, value, hint) => {
            let mut o: Vec<IConstantInfo> = Vec::new();
            o.push(IConstantInfo::DefnInfo(env::i_constant_val_dup(cv), value.dup2(), reducibility_hint_dup(hint)));
            Ok(o)
        }
        IDeclaration::ThmDecl(cv, _) => {
            let mut o: Vec<IConstantInfo> = Vec::new();
            o.push(IConstantInfo::ThmInfo(env::i_constant_val_dup(cv)));
            Ok(o)
        }
        IDeclaration::OpaqueDecl(cv, _) => {
            let mut o: Vec<IConstantInfo> = Vec::new();
            o.push(IConstantInfo::AxiomInfo(env::i_constant_val_dup(cv)));
            Ok(o)
        }
        IDeclaration::AxiomDecl(cv) => decl_constants_axiom(pers, st, cv),
        IDeclaration::QuotDecl(k, cv) => match basis::quot_at(pers, st, k, cv) {
            Err(e) => Err(e),
            Ok(ci) => {
                let mut o: Vec<IConstantInfo> = Vec::new();
                o.push(ci);
                Ok(o)
            }
        },
        IDeclaration::IndDecl(block, n_p) => match block_shape::read_block(pers, st, *n_p, block) {
            Err(e) => Err(e),
            Ok(Ok(p)) => block_constants(pers, st, &p),
            Ok(Err(_)) => Ok(Vec::new()),
        },
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:82-96 declConstants
/// The `.axiomDecl` arm: `Quot.sound` installs its pin at the record's names,
/// `sorryAx` nothing, any other axiom itself.
pub fn decl_constants_axiom(pers: &PersTier, st: &mut AState, cv: &IConstantVal) -> Result<Vec<IConstantInfo>, CheckError> {
    match pins::pin_quot_sound(st) {
        Err(e) => Err(e),
        Ok(qs) => {
            if cv.name.eq2(&qs) {
                match basis::quot_at(pers, st, &QuotKind::Sound, cv) {
                    Err(e) => Err(e),
                    Ok(ci) => {
                        let mut o: Vec<IConstantInfo> = Vec::new();
                        o.push(ci);
                        Ok(o)
                    }
                }
            } else {
                match pins::pin_sorry_ax(st) {
                    Err(e) => Err(e),
                    Ok(sa) => {
                        if cv.name.eq2(&sa) {
                            Ok(Vec::new())
                        } else {
                            let mut o: Vec<IConstantInfo> = Vec::new();
                            o.push(IConstantInfo::AxiomInfo(env::i_constant_val_dup(cv)));
                            Ok(o)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:98-104 declTables
/// con-leche: ConLeche/Cached/CheckerC.lean:57-63 declTablesC
/// **The projection tables a declaration installs**: those of an inductive
/// block `readBlock` reads (none where a constructor is too short for them).
pub fn decl_tables(pers: &PersTier, st: &mut AState, pd: &IDeclaration) -> Result<Vec<IProjTable>, CheckError> {
    match pd {
        IDeclaration::IndDecl(block, n_p) => match block_shape::read_block(pers, st, *n_p, block) {
            Err(e) => Err(e),
            Ok(Ok(p)) => match block_tables(pers, st, &p, &p.members, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(Some(q)) => Ok(q),
                Ok(None) => Ok(Vec::new()),
            },
            Ok(Err(_)) => Ok(Vec::new()),
        },
        _ => Ok(Vec::new()),
    }
}
