//! `arena::inductives::stored_install` — the stored install of an inductive
//! block, and the comparison of what an install pushes.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StoredInstall.lean`, which
//! is `ConLeche/Cached/StoredInstall.lean` over handles.  Phase A pushes an
//! inductive block **as the input stores it**: every constant and table is read
//! off the block's records, and nothing is generated.  The block's checked
//! install runs later, as a job of the check phase (`checker::block_check`),
//! and compares what it pushes with what this install pushed; a difference is
//! an internal error (this reading is wrong, the stream is not).
//!
//! What is read, and from where (the checked install's own functions on the
//! same inputs wherever one exists):
//!
//! * the formers: each at its telescope, with `block_caps_at` at official's
//!   `is_rec` and member 0's result sort.  The telescope is the stored type
//!   where that is a syntactic telescope ending in a sort, else the reduced
//!   telescope official's `whnf` loop reads;
//! * the constructors as declared;
//! * the recursors: each at its stored type, its stored right-hand sides, its
//!   rules' metadata by `tgt_stored_rules` at the record's major;
//! * the projection tables: the bodies by substitution, the guards (the
//!   fields' sorts) inferred here by the constructor stage's own walk.
//!
//! Where a part cannot be read it is pushed at its record as declared (a
//! former, a recursor's rules) or left out (a table): the block is one the
//! checked install rejects, and its job reports it.
//!
//! ## The twin's deviations
//!
//! * **The reading's two inferences each have a scratch bracket of their own**
//!   (`stored_tele_slow`, `stored_guards`): a failed inference is a VALUE here,
//!   `None` or no guards, and the run goes on, so the state after one must be
//!   the state it started from.  The bracket gives exactly that: nothing writes
//!   the persistent tier inside it, its `Err` arm (`stored_abandon`) writes the state
//!   from the tier and the saved pins, with empty memos, caches and scratch, and what an
//!   accepted inference leaves is promoted before the drop.  Everything else of
//!   the reading runs in one bracket at its end (`stored_tail`), which promotes
//!   the block's new constants and tables as `install_step`'s does.
//! * **A term comparison is handle equality**, since a term is hash-consed
//!   across the tiers: con-leche's pointer-first `Expr` equality with no
//!   fallback.  The comparisons are one function per type: there are no
//!   closures, so `listBeqBy` is a walk per list.
//! * **The store's own failures stay failures** (a full handle space, a
//!   dangling handle): they are what `Native`/`Internal` are for, a stop of
//!   phase A at this record (`checker::phase_a_failure`).
//! * **A name already taken stops phase A here** (`M_SLOT_TAKEN`), before
//!   anything is pushed, and the block's job is run for the verdict:
//!   `ParInstall.lean`'s `commitLoop`, at the slot that does not match.

use super::block_install;
use super::block_parts;
use super::block_parts::{BlockParts, BlockShape, MemberShape, RecShape};
use super::rec_check;
use super::rec_check::TargetMajor;
use super::struct_parts;
use super::sum_install;
use crate::arena::basis;
use crate::arena::canon::{eidx_vec_beq, lidx_vec_beq, nidx_vec_beq};
use crate::arena::checker_base;
use crate::arena::core::{drop_scratch, enter_scratch, flush_caches, CORE_WALK_FUEL};
use crate::arena::env;
use crate::arena::env::{
    i_constant_val_dup, ifenv_find, ifenv_push, ifenv_push_table, IConstantInfo, IConstantVal,
    IFEnv, IIndCaps, IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_CONST, ETAG_FORALL_E, ETAG_SORT};
use crate::arena::core_state::Caches;
use crate::arena::monad::{fail, fail_dangling_e, intern_e_sort, view_bind, view_const, view_sort, AState, Memos};
use crate::arena::pins::pin_empty_levels;
use crate::arena::promote::{
    promote_e, promote_l, promote_l_list, promote_new, scratch_restore, scratch_save, PMemo, ScratchFrame,
};
use crate::arena::store::{EStore, PersTier};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{reducibility_hint_beq, CheckMode};
use crate::kernel::prop_when;
use crate::ron::hashmap::{Dup, Eq2};

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"install: the scratch tier is open"`, as code points: a block's reading starts
/// with the tier closed, which the test never finds otherwise.
pub const M_SCRATCH_OPEN: [u32; 33] = [105, 110, 115, 116, 97, 108, 108, 58, 32, 116, 104, 101, 32, 115, 99, 114, 97, 116, 99, 104, 32, 116, 105, 101, 114, 32, 105, 115, 32, 111, 112, 101, 110];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"install: a predicted slot did not match"`, as code points: the error of a
/// block one of whose names is taken, if its job does not reject it.
pub const M_SLOT_TAKEN: [u32; 39] = [
    105, 110, 115, 116, 97, 108, 108, 58, 32, 97, 32, 112, 114, 101, 100, 105, 99, 116, 101, 100,
    32, 115, 108, 111, 116, 32, 100, 105, 100, 32, 110, 111, 116, 32, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"stored guards"`, as code points.
pub const M_STORED_GUARDS: [u32; 13] = [115, 116, 111, 114, 101, 100, 32, 103, 117, 97, 114, 100, 115];

// ---------------------------------------------------------------------------
// Pointer-first equality of what an install pushes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StoredInstall.lean:76-77 ConstantVal.beqP
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:50-53 IConstantVal.beqP`
/// — `ConstantVal` equality, the type by handle.
pub fn i_constant_val_beq_p(a: &IConstantVal, b: &IConstantVal) -> bool {
    a.name.eq2(&b.name) && nidx_vec_beq(&a.level_params, &b.level_params, 0) && a.ty.eq2(&b.ty)
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:87-90 RecRuleFire.beqP
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:55-60 IRecRuleFire.beqP`
/// — `RecRuleFire` equality, the pins by handle.
pub fn i_rec_rule_fire_beq_p(a: &IRecRuleFire, b: &IRecRuleFire) -> bool {
    match a {
        IRecRuleFire::Plain => match b {
            IRecRuleFire::Plain => true,
            IRecRuleFire::Nested(_, _) => false,
        },
        IRecRuleFire::Nested(l, p) => match b {
            IRecRuleFire::Plain => false,
            IRecRuleFire::Nested(l2, p2) => lidx_vec_beq(l, l2, 0) && eidx_vec_beq(p, p2, 0),
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:96-98 RecRule.beqP
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:62-66 IRecRule.beqP`
/// — `RecRule` equality, the right-hand side by handle.
pub fn i_rec_rule_beq_p(a: &IRecRule, b: &IRecRule) -> bool {
    a.ctor.eq2(&b.ctor)
        && a.nfields == b.nfields
        && a.ctor_params == b.ctor_params
        && i_rec_rule_fire_beq_p(&a.fire, &b.fire)
        && a.rhs.eq2(&b.rhs)
        && a.k == b.k
        && a.eta == b.eta
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:62-65 listBeqBy
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:43-48 listBeqBy` —
/// `listBeqBy RecRule.beqP`, as an index recursion.
pub fn i_rec_rules_beq_p(a: &Vec<IRecRule>, b: &Vec<IRecRule>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if i_rec_rule_beq_p(&a[i], &b[i]) {
        i_rec_rules_beq_p(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:196-243 IndCaps
/// Lean twin: the `deriving DecidableEq` of `IIndCaps`, which `IConstantInfo.beqP`
/// reads as `decide (c = c')`.
pub fn i_ind_caps_beq(a: &IIndCaps, b: &IIndCaps) -> bool {
    a.eta == b.eta
        && a.eta_ctor.eq2(&b.eta_ctor)
        && a.eta_params == b.eta_params
        && a.eta_fields == b.eta_fields
        && a.unitlike == b.unitlike
        && a.unit_params == b.unit_params
        && a.rule_k == b.rule_k
        && prop_when::beq(&a.sort_z, &b.sort_z)
        && nidx_vec_beq(&a.all, &b.all, 0)
        && a.nparams == b.nparams
        && nidx_vec_beq(&a.ctors, &b.ctors, 0)
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:109-117 ConstantInfo.beqP
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:68-79 IConstantInfo.beqP`
/// — **`ConstantInfo` equality, pointer-first**: every term by handle, the rest
/// by its decidable equality.
pub fn i_constant_info_beq_p(a: &IConstantInfo, b: &IConstantInfo) -> bool {
    match a {
        IConstantInfo::AxiomInfo(v) => match b {
            IConstantInfo::AxiomInfo(v2) => i_constant_val_beq_p(v, v2),
            _ => false,
        },
        IConstantInfo::DefnInfo(v, e, h) => match b {
            IConstantInfo::DefnInfo(v2, e2, h2) => {
                i_constant_val_beq_p(v, v2) && e.eq2(e2) && reducibility_hint_beq(h, h2)
            }
            _ => false,
        },
        IConstantInfo::ThmInfo(v) => match b {
            IConstantInfo::ThmInfo(v2) => i_constant_val_beq_p(v, v2),
            _ => false,
        },
        IConstantInfo::IndInfo(v, c) => match b {
            IConstantInfo::IndInfo(v2, c2) => i_constant_val_beq_p(v, v2) && i_ind_caps_beq(c, c2),
            _ => false,
        },
        IConstantInfo::CtorInfo(v, x, y) => match b {
            IConstantInfo::CtorInfo(v2, x2, y2) => i_constant_val_beq_p(v, v2) && *x == *x2 && *y == *y2,
            _ => false,
        },
        IConstantInfo::RecInfo(v, x, y, rs) => match b {
            IConstantInfo::RecInfo(v2, x2, y2, rs2) => {
                i_constant_val_beq_p(v, v2) && *x == *x2 && *y == *y2 && i_rec_rules_beq_p(rs, rs2, 0)
            }
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:132-135 ProjTable.beqP
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:81-86 IProjTable.beqP`
/// — **`ProjTable` equality, pointer-first**: every term and level by handle.
pub fn i_proj_table_beq_p(a: &IProjTable, b: &IProjTable) -> bool {
    a.struct_name.eq2(&b.struct_name)
        && nidx_vec_beq(&a.level_params, &b.level_params, 0)
        && a.num_params == b.num_params
        && a.ctor.eq2(&b.ctor)
        && a.num_fields == b.num_fields
        && a.struct_sort.eq2(&b.struct_sort)
        && eidx_vec_beq(&a.bodies, &b.bodies, 0)
        && lidx_vec_beq(&a.guards, &b.guards, 0)
}

// ---------------------------------------------------------------------------
// The reading
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
/// con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:90-108 storedTry` — the
/// `Err` arm of a stored inference (the module note): the state written from what
/// the failed run could not touch, the tier and the saved pins, with empty memos,
/// caches and scratch tiers.  Fresh tables rather than reset ones: nothing is known
/// of the tables a failed run leaves, and the failure path is rare.
pub fn stored_abandon(st: &mut AState, tier: PersTier, saved: ScratchFrame) {
    st.store = EStore::of_tier(tier);
    st.memos = Memos::empty();
    st.caches = Caches::empty();
    st.pins = saved.pins;
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:119-138 storedTele` — **a
/// former's telescope, as the checked install computes it** (`check_sum_tele`,
/// without its checks): the stored type where it is a syntactic telescope of `n`
/// binders ending in a sort; else the telescope official's `whnf` loop reads,
/// closed.  `None` where the loop does not reach a sort.
pub fn stored_tele(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    n: u64,
) -> Result<Option<(IConstantVal, LIdx)>, CheckError> {
    match expr_ops::strip_pis(pers, st, n, &cv.ty) {
        Err(e) => Err(e),
        Ok(Some(q)) => {
            if q.1.tag() == ETAG_SORT {
                match view_sort(pers, st, &q.1) {
                    None => fail_dangling_e(),
                    Some(s) => Ok(Some((i_constant_val_dup(cv), s))),
                }
            } else {
                stored_tele_slow(st, mode, fe, cv, n)
            }
        }
        Ok(None) => stored_tele_slow(st, mode, fe, cv, n),
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:119-138 storedTele` — the
/// `whnf` loop in a scratch bracket of its own, from fresh caches (the cited
/// `flushC`); what it answers is promoted, a failure is `None`.
pub fn stored_tele_slow(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    n: u64,
) -> Result<Option<(IConstantVal, LIdx)>, CheckError> {
    flush_caches(st);
    let mut tier: PersTier = enter_scratch(st);
    let saved: ScratchFrame = scratch_save(st);
    match stored_tele_run(&tier, st, mode, fe, cv, n) {
        Err(_) => {
            stored_abandon(st, tier, saved);
            Ok(None)
        }
        Ok((ty, s)) => {
            scratch_restore(st, saved);
            match promote_e(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, &ty) {
                Err(e) => {
                    drop_scratch(st, tier);
                    Err(e)
                }
                Ok((m, ty2)) => match promote_l(&mut tier, st, m, CORE_WALK_FUEL, &s) {
                    Err(e) => {
                        drop_scratch(st, tier);
                        Err(e)
                    }
                    Ok((_, s2)) => {
                        drop_scratch(st, tier);
                        Ok(Some((
                            IConstantVal {
                                name: cv.name.dup2(),
                                level_params: env::nidx_vec_dup(&cv.level_params),
                                ty: ty2,
                            },
                            s2,
                        )))
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:161-170 storedTele
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:119-138 storedTele` — the
/// cited `run`: the telescope, closed over its sort.
pub fn stored_tele_run(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    n: u64,
) -> Result<(EIdx, LIdx), CheckError> {
    match sum_install::whnf_telescope(pers, fe.visible_below, st, mode, fe, 0, n, &cv.ty, Vec::new()) {
        Err(e) => Err(e),
        Ok(q) => match intern_e_sort(pers, st, q.1.dup2()) {
            Err(e) => Err(e),
            Ok(sort_s) => match sum_install::close_telescope(pers, st, &q.0, 0, 0, &sort_s) {
                Err(e) => Err(e),
                Ok(ty) => Ok((ty, q.1)),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:175-180 storedFormers
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:140-151 storedFormers` — the
/// members' formers at their telescopes from member `i` on, each at its record
/// as declared where its telescope cannot be read, and member 0's result sort
/// (`s0`, the recogniser's placeholder where it cannot be read).
#[allow(clippy::too_many_arguments)]
pub fn stored_formers(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    i: usize,
    out: Vec<IConstantVal>,
    s0: LIdx,
) -> Result<(Vec<IConstantVal>, LIdx), CheckError> {
    if i >= p.members.len() {
        Ok((out, s0))
    } else {
        let ms: &MemberShape = &p.members[i];
        match stored_tele(pers, st, mode, fe, &ms.cv_t, p.n_p + ms.n_idx) {
            Err(e) => Err(e),
            Ok(Some((cv, s))) => {
                let mut o: Vec<IConstantVal> = out;
                o.push(cv);
                let s1: LIdx = if i == 0 { s } else { s0 };
                stored_formers(pers, st, mode, fe, p, i + 1, o, s1)
            }
            Ok(None) => {
                let mut o: Vec<IConstantVal> = out;
                o.push(i_constant_val_dup(&ms.cv_t));
                stored_formers(pers, st, mode, fe, p, i + 1, o, s0)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:186-197 storedMajor
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:170-188 storedMajor` — **a
/// recursor record's major**, as `tgt_stored_rules` reads it: a member (its
/// parameter count and constructors), or an outside container at the levels and
/// parameters of the stored major domain opened at the recursor's prefix.
pub fn stored_major(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    p: &BlockShape,
    rc: &RecShape,
) -> Result<Option<TargetMajor>, CheckError> {
    if rc.tgt < block_parts::shape_k(p) {
        let ms: &MemberShape = &p.members[rc.tgt as usize];
        match pin_empty_levels(st) {
            Err(e) => Err(e),
            Ok(ls) => Ok(Some(TargetMajor {
                ind: ms.cv_t.name.dup2(),
                lvls: ls,
                ds: Vec::new(),
                n_pc: p.n_p,
                n_idx: ms.n_idx,
                ctors: block_parts::ctors_dup(&ms.ctors, 0, Vec::new()),
                member: Some(rc.tgt),
                nfs: Vec::new(),
                pfvs: Vec::new(),
            })),
        }
    } else {
        match checker_base::open_pis_at_fvars(pers, st, rc.m_i, &rc.cv_r.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(q)) => {
                if q.1.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &q.1) {
                        None => fail_dangling_e(),
                        Some((dom, _)) => stored_major_dom(pers, vis, st, fe, &dom),
                    }
                } else {
                    Ok(None)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:186-197 storedMajor
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:170-188 storedMajor` — the
/// outside container named by the major's domain.
pub fn stored_major_dom(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    dom: &EIdx,
) -> Result<Option<TargetMajor>, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_CONST {
                match view_const(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some((i_name, us)) => match rec_check::target_ctors_of(pers, st, vis, fe, &i_name) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some((n_pc, ctors))) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, dom) {
                            Err(e) => Err(e),
                            Ok(args) => Ok(Some(TargetMajor {
                                ind: i_name,
                                lvls: us,
                                ds: stored_take(&args, n_pc, 0, Vec::new()),
                                n_pc,
                                n_idx: 0,
                                ctors,
                                member: None,
                                nfs: Vec::new(),
                                pfvs: Vec::new(),
                            })),
                        },
                    },
                }
            } else {
                Ok(None)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:186-197 storedMajor
/// Lean twin: the cited `dom.getAppArgs.take nPc`.
pub fn stored_take(xs: &Vec<EIdx>, n: u64, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= xs.len() || (i as u64) >= n {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(xs[i].dup2());
        stored_take(xs, n, i + 1, o)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:202-208 storedRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:190-205 storedRecs` — **the
/// recursors' records** from `r` on, in the block's order, pushed; the rules'
/// lookups at the constructors' bound `vis2` while they are pushed above it.  A
/// recursor whose major cannot be read keeps its rules as declared.
pub fn stored_recs(
    pers: &PersTier,
    vis2: u64,
    st: &mut AState,
    p: &BlockShape,
    r: u64,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    if r >= p.recs.len() as u64 {
        Ok(fe)
    } else {
        let rc: &RecShape = &p.recs[r as usize];
        match stored_major(pers, vis2, st, &fe, p, rc) {
            Err(e) => Err(e),
            Ok(None) => {
                let fe2: IFEnv = ifenv_push(
                    fe,
                    IConstantInfo::RecInfo(
                        i_constant_val_dup(&rc.cv_r),
                        block_parts::major_idx_at(p, r),
                        block_parts::rule_prefix_at(p, r),
                        env::i_rec_rules_dup(&rc.rules),
                    ),
                );
                stored_recs(pers, vis2, st, p, r + 1, fe2)
            }
            Ok(Some(m)) => {
                let r_p: u64 = block_parts::rule_prefix_at(p, r);
                let rhss: Vec<EIdx> = block_parts::rule_rhss(&rc.rules, 0, Vec::new());
                match rec_check::tgt_stored_rules(pers, vis2, st, &fe, &rc.cv_r, r_p, &m, &rhss) {
                    Err(e) => Err(e),
                    Ok(rules) => {
                        let fe2: IFEnv = ifenv_push(
                            fe,
                            IConstantInfo::RecInfo(
                                i_constant_val_dup(&rc.cv_r),
                                block_parts::major_idx_at(p, r),
                                r_p,
                                rules,
                            ),
                        );
                        stored_recs(pers, vis2, st, p, r + 1, fe2)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:218-227 storedGuards` — **a
/// structure's guard levels**: the fields' sorts at the formers' environment
/// `fe1`, from fresh caches, by the constructor stage's own walk, in a scratch
/// bracket of their own; none where the walk fails (the block's checked install
/// then fails at the same walk, and the job reports it).
pub fn stored_guards(
    st: &mut AState,
    mode: &CheckMode,
    fe1: &IFEnv,
    p: &BlockShape,
    c: &(IConstantVal, u64),
) -> Result<Vec<LIdx>, CheckError> {
    flush_caches(st);
    let mut tier: PersTier = enter_scratch(st);
    let saved: ScratchFrame = scratch_save(st);
    match stored_guards_run(&tier, st, mode, fe1, p, c) {
        Err(_) => {
            stored_abandon(st, tier, saved);
            Ok(Vec::new())
        }
        Ok(gs) => {
            scratch_restore(st, saved);
            match promote_l_list(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, &gs) {
                Err(e) => {
                    drop_scratch(st, tier);
                    Err(e)
                }
                Ok((_, gs2)) => {
                    drop_scratch(st, tier);
                    Ok(gs2)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:218-227 storedGuards` — the
/// cited `run` and the guards off its sorts.
pub fn stored_guards_run(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe1: &IFEnv,
    p: &BlockShape,
    c: &(IConstantVal, u64),
) -> Result<Vec<LIdx>, CheckError> {
    match checker_base::open_pis_at_fvars_f(pers, st, p.n_p, &c.0.ty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(CheckError::Internal(code_points(&M_STORED_GUARDS))),
        Ok(Some(cq)) => match checker_base::open_pis_at_fvars_f(pers, st, c.1, &cq.1, p.n_p) {
            Err(e) => Err(e),
            Ok(None) => fail(CheckError::Internal(code_points(&M_STORED_GUARDS))),
            Ok(Some(xq)) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &xq.1) {
                Err(e) => Err(e),
                Ok(args) => {
                    let idx_args: Vec<EIdx> = stored_drop(&args, p.n_p as usize, Vec::new());
                    match sum_install::check_struct_field_sorts_i(
                        pers,
                        fe1.visible_below,
                        st,
                        mode,
                        fe1,
                        p.is_prop,
                        p.large,
                        &p.res_sort,
                        p.n_p,
                        &xq.0,
                        &idx_args,
                        c.1,
                    ) {
                        Err(e) => Err(e),
                        Ok(sorts) => struct_parts::struct_proj_guards(pers, st, &c.0.ty, p.n_p, c.1, &sorts),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:214-223 storedGuards
/// Lean twin: the cited `xq.2.getAppArgs.drop p.nP`.
pub fn stored_drop(xs: &Vec<EIdx>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(xs[i].dup2());
        stored_drop(xs, i + 1, o)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:228-241 storedTables
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:229-247 storedGuardsAll` —
/// the guards of the cited walk's every structure-like member (one constructor,
/// no index) from member `i` on, one list per member, read before the bracket
/// the bodies are built in.
pub fn stored_guards_all(
    st: &mut AState,
    mode: &CheckMode,
    fe1: &IFEnv,
    p: &BlockShape,
    i: usize,
    out: Vec<Vec<LIdx>>,
) -> Result<Vec<Vec<LIdx>>, CheckError> {
    if i >= p.members.len() {
        Ok(out)
    } else if p.members[i].ctors.len() == 1 && p.members[i].n_idx == 0 {
        match stored_guards(st, mode, fe1, p, &p.members[i].ctors[0]) {
            Err(e) => Err(e),
            Ok(gs) => {
                let mut o: Vec<Vec<LIdx>> = out;
                o.push(gs);
                stored_guards_all(st, mode, fe1, p, i + 1, o)
            }
        }
    } else {
        let mut o: Vec<Vec<LIdx>> = out;
        o.push(Vec::new());
        stored_guards_all(st, mode, fe1, p, i + 1, o)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:228-241 storedTables
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:249-266 storedTables` — **the
/// projection tables**, member by member in block order from `i` on, pushed, at
/// every structure-like member; none where the bodies cannot be built.
pub fn stored_tables(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    guards: &Vec<Vec<LIdx>>,
    i: usize,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    if i >= p.members.len() {
        Ok(fe)
    } else if p.members[i].ctors.len() == 1 && p.members[i].n_idx == 0 {
        let ms: &MemberShape = &p.members[i];
        let c: &(IConstantVal, u64) = &ms.ctors[0];
        match struct_parts::struct_proj_bodies(pers, st, &ms.cv_t.name, p.n_p, c.1, &c.0.ty) {
            Err(e) => Err(e),
            Ok(None) => stored_tables(pers, st, p, guards, i + 1, fe),
            Ok(Some(bodies)) => {
                let gs: Vec<LIdx> = if i < guards.len() {
                    env::lidx_vec_dup(&guards[i])
                } else {
                    Vec::new()
                };
                let fe2: IFEnv = ifenv_push_table(
                    fe,
                    IProjTable {
                        struct_name: ms.cv_t.name.dup2(),
                        level_params: block_parts::shape_lps(p),
                        num_params: p.n_p,
                        ctor: c.0.name.dup2(),
                        num_fields: c.1,
                        struct_sort: p.res_sort.dup2(),
                        bodies,
                        guards: gs,
                    },
                );
                stored_tables(pers, st, p, guards, i + 1, fe2)
            }
        }
    } else {
        stored_tables(pers, st, p, guards, i + 1, fe)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:268-272 storedCtors` — the
/// cited `FEnv.pushAll ctors`, member by member from `i` on: every constructor as
/// declared.
pub fn stored_ctors(n_p: u64, ms: &Vec<MemberShape>, i: usize, fe: IFEnv) -> IFEnv {
    if i >= ms.len() {
        fe
    } else {
        let fe2: IFEnv = sum_install::cons_sum_ctors(n_p, &ms[i].ctors, 0, fe);
        stored_ctors(n_p, ms, i + 1, fe2)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:274-291 storedTail` — the
/// reading's last bracket: the constructors, the recursors and the tables pushed
/// above the formers, and everything new since the counter `vis` and the table
/// count `nt` promoted.
pub fn stored_tail(
    st: &mut AState,
    p: &BlockShape,
    guards: &Vec<Vec<LIdx>>,
    vis: u64,
    nt: u64,
    fe1: IFEnv,
) -> Result<IFEnv, CheckError> {
    flush_caches(st);
    let mut tier: PersTier = enter_scratch(st);
    let saved: ScratchFrame = scratch_save(st);
    let fe2: IFEnv = stored_ctors(p.n_p, &p.members, 0, fe1);
    let vis2: u64 = fe2.visible_below;
    match stored_recs(&tier, vis2, st, p, 0, fe2) {
        Err(e) => {
            drop_scratch(st, tier);
            Err(e)
        }
        Ok(fe3) => match stored_tables(&tier, st, p, guards, 0, fe3) {
            Err(e) => {
                drop_scratch(st, tier);
                Err(e)
            }
            Ok(fe4) => {
                scratch_restore(st, saved);
                let k: u64 = fe4.visible_below - vis;
                let kt: u64 = fe4.env.tables.len() as u64 - nt;
                match promote_new(&mut tier, st, PMemo::empty(), CORE_WALK_FUEL, k, kt, fe4) {
                    Err(e) => {
                        drop_scratch(st, tier);
                        Err(e)
                    }
                    Ok((_, fe5)) => {
                        drop_scratch(st, tier);
                        Ok(fe5)
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Driver/ParInstall.lean:690-808 commitLoop
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:293-297 namesFree` — **the
/// names a block pushes are free**: `slotsOk`, read before anything is pushed.
pub fn stored_names_free(pers: &PersTier, vis: u64, fe: &IFEnv, ns: &Vec<NIdx>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if ifenv_find(pers, vis, fe, &ns[i]).is_some() {
        false
    } else {
        stored_names_free(pers, vis, fe, ns, i + 1)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:299-318 storedParts` — the
/// recursors' names from `i` on, appended.
pub fn rec_names(rs: &Vec<RecShape>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= rs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(rs[i].cv_r.name.dup2());
        rec_names(rs, i + 1, o)
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:299-318 storedParts` — **a
/// block the recogniser reads**: its names distinct and free, the formers read,
/// and the rest (`stored_parts_push`).
pub fn stored_parts(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p0: &BlockParts,
) -> Result<IFEnv, CheckError> {
    if st.store.scratch_on {
        return fail(CheckError::Internal(code_points(&M_SCRATCH_OPEN)));
    }
    let names: Vec<NIdx> = rec_names(
        &p0.shape.recs,
        0,
        block_install::ctor_name_list(
            &block_parts::all_ctors(&p0.shape.members, 0, Vec::new()),
            0,
            block_parts::shape_member_names(&p0.shape),
        ),
    );
    if !checker_base::name_nodup(&names) || !stored_names_free(pers, fe.visible_below, &fe, &names, 0) {
        fail(CheckError::Internal(code_points(&M_SLOT_TAKEN)))
    } else {
        match stored_formers(pers, st, mode, &fe, &p0.shape, 0, Vec::new(), p0.shape.res_sort.dup2()) {
            Err(e) => Err(e),
            Ok((cv_ts, s0)) => {
                match block_parts::with_sort(pers, st, block_parts::block_shape_dup(&p0.shape), s0) {
                    Err(e) => Err(e),
                    Ok(p) => match block_install::block_raw_rec(pers, st, p0) {
                        Err(e) => Err(e),
                        Ok(is_rec) => stored_parts_push(pers, st, mode, fe, &p, is_rec, &cv_ts),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:299-318 storedParts` — past
/// the formers' reading: pushed with their capability records, the guards, and
/// the last bracket.
pub fn stored_parts_push(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    is_rec: bool,
    cv_ts: &Vec<IConstantVal>,
) -> Result<IFEnv, CheckError> {
    let vis: u64 = fe.visible_below;
    let nt: u64 = fe.env.tables.len() as u64;
    match block_install::cons_block_inds(pers, st, p, is_rec, cv_ts, 0, fe) {
        Err(e) => Err(e),
        Ok(fe1) => match stored_guards_all(st, mode, &fe1, p, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(guards) => stored_tail(st, p, &guards, vis, nt, fe1),
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredInstall.lean:320-338 storedInstall` — **the
/// stored install of a block** on `fe`.  A block matching a basis pin pushes the
/// pin's constants, a block the recogniser does not read pushes nothing, and
/// every other block its reading, each part at its record as declared where the
/// reading fails.  `pers` is the phase-A reader, an owned store's, so what the
/// recogniser interns is persistent.
pub fn stored_install(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    n_p: u64,
) -> Result<IFEnv, CheckError> {
    match basis::basis_pin_hit(pers, st, block) {
        Err(e) => Err(e),
        Ok(Some(kind)) => match basis::basis_kind_decls_a(pers, st, &kind) {
            Err(e) => Err(e),
            Ok(decls) => {
                if st.store.scratch_on {
                    return fail(CheckError::Internal(code_points(&M_SCRATCH_OPEN)));
                }
                let names: Vec<NIdx> = env::i_constant_info_names_from(&decls, 0, Vec::new());
                if !stored_names_free(pers, fe.visible_below, &fe, &names, 0) {
                    fail(CheckError::Internal(code_points(&M_SLOT_TAKEN)))
                } else {
                    Ok(stored_push_all(&decls, 0, fe))
                }
            }
        },
        Ok(None) => match block_parts::block_parts(pers, st, n_p, block) {
            Err(e) => Err(e),
            Ok(None) => Ok(fe),
            Ok(Some(p0)) => stored_parts(pers, st, mode, fe, &p0),
        },
    }
}

/// con-leche: ConLeche/Cached/StoredInstall.lean:251-267 storedInstall
/// Lean twin: the cited `kind.declsA`, pushed in order (`FEnv.pushAll`).
pub fn stored_push_all(decls: &Vec<IConstantInfo>, i: usize, fe: IFEnv) -> IFEnv {
    if i >= decls.len() {
        fe
    } else {
        let fe2: IFEnv = ifenv_push(fe, env::i_constant_info_dup(&decls[i]));
        stored_push_all(decls, i + 1, fe2)
    }
}
