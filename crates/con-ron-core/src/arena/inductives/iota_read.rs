//! `arena::inductives::iota_read` — the ι reading rule.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/IotaRead.lean`, which is
//! con-leche's `Kernel/Inductives/IotaRead.lean` and `IotaEq.lean` over
//! handles, with the algorithm of their cached twin `Cached/IotaReadC.lean`
//! (`blockReadsOkC`): after a block's check, every recursor it installs must
//! state, in each minor premise, the constructor's fields, indices, levels
//! and parameters as the constructor's own type does — syntactically, up to
//! equivalent universe levels (`lvl_eq`) and, in a `.plain` rule whose
//! recursor parameters fit the constructor's, up to Lean's consumed type
//! annotations (`ann_eq`), each consumed only where it is stored as the
//! identity on its type argument.
//!
//! ## The twin's deviations
//!
//! * **The answer is a `bool`**; `check_decl::check_ind_decl` throws the
//!   rejection with a constant message (§3.1 drops the interpolation).
//! * **The environment after the install is the INPUT index with the block's
//!   constants pushed in place** (`block_reads_at`), as upstream's cached
//!   `checkBlockKS` builds it: `check_block`'s own answer holds the REDUCED
//!   formers.  The pushes are undone before `check_block` runs; the arm acts
//!   on the answer after it.  The tables are not pushed (the rule reads
//!   constants only).
//! * **The recursor's frame is read once per recursor** (`iota_rec_of`); each
//!   rule then reads its own minor premise (`iota_parts_of_at`).
//! * **`iota_parts_at` also answers the constructor's parameter domains**,
//!   which `params_ann_eq` strips off the same instantiated type.
//! * **The annotations' names are interned** and compared by handle.

use super::block_shape::BlockShape;
use super::block_tail;
use super::gen_rec;
use super::struct_parts;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{
    EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_LAM, ETAG_LET_E,
    ETAG_PROJ, ETAG_SORT,
};
use crate::arena::install;
use crate::arena::monad::{
    fail, fail_dangling_e, fail_dangling_ls, intern_e_bvar, intern_ls_node, intern_n_node,
    read_level_m, read_levels_m, view_app, view_bind, view_bvar, view_const, view_l, view_let,
    view_ls_len, view_proj, view_sort, AState,
};
use crate::arena::store::{LNodeView, NNodeView, PersTier};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::level;
use crate::ron::hashmap::{Dup, Eq2};

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: piTele`, as code points.
pub const M_FUEL_PI_TELE: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 84, 101,
    108,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: lvlEq`, as code points.
pub const M_FUEL_LVL_EQ: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 118, 108, 69,
    113,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: annEq`, as code points.
pub const M_FUEL_ANN_EQ: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 110, 110, 69,
    113,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor's minor premise does not state the constructor's fields, indices and parameters as the constructor's type does`, as code points.
pub const M_NOT_READ: [u32; 123] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 39, 115, 32, 109, 105, 110, 111, 114,
    32, 112, 114, 101, 109, 105, 115, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 116,
    97, 116, 101, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 39,
    115, 32, 102, 105, 101, 108, 100, 115, 44, 32, 105, 110, 100, 105, 99, 101, 115, 32, 97, 110,
    100, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 115, 32, 116, 104, 101, 32,
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 39, 115, 32, 116, 121, 112, 101, 32, 100,
    111, 101, 115,
];

/// con-leche: none — the name part `optParam`, as code points
/// Lean twin: `"optParam"`.
pub const OPT_PARAM: [u32; 8] = [111, 112, 116, 80, 97, 114, 97, 109];

/// con-leche: none — the name part `autoParam`, as code points
/// Lean twin: `"autoParam"`.
pub const AUTO_PARAM: [u32; 9] = [97, 117, 116, 111, 80, 97, 114, 97, 109];

/// con-leche: none — the name part `outParam`, as code points
/// Lean twin: `"outParam"`.
pub const OUT_PARAM: [u32; 8] = [111, 117, 116, 80, 97, 114, 97, 109];

/// con-leche: none — the name part `semiOutParam`, as code points
/// Lean twin: `"semiOutParam"`.
pub const SEMI_OUT_PARAM: [u32; 12] = [115, 101, 109, 105, 79, 117, 116, 80, 97, 114, 97, 109];

/// con-leche: none — the name part `missing`, as code points
/// Lean twin: `"missing"`.
pub const MISSING: [u32; 7] = [109, 105, 115, 115, 105, 110, 103];

// ---------------------------------------------------------------------------
// The recursor's own type (`IotaEq.lean`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:83-86 Expr.piTele
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:55-66 piTele` — a
/// `∀`-telescope's binder count and its body.
pub fn pi_tele(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<(u64, EIdx), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PI_TELE)))
    } else if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, b)) => match pi_tele(pers, st, fuel - 1, &b) {
                Err(e) => Err(e),
                Ok(r) => Ok((r.0 + 1, r.1)),
            },
        }
    } else {
        Ok((0, h.dup2()))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:32-43 motiveLevel?
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:68-89 motiveLevel?` —
/// the sort level of a recursor's motive: the body's head is a prefix
/// variable whose binder's domain ends in `Sort u`.
pub fn motive_level(
    pers: &PersTier,
    st: &mut AState,
    pre: &Vec<EIdx>,
    n_idx: u64,
    body: &EIdx,
) -> Result<Option<LIdx>, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, body) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_BVAR {
                match view_bvar(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some(k) => {
                        if n_idx + 1 <= k && k < n_idx + 1 + pre.len() as u64 {
                            let i: u64 = pre.len() as u64 - 1 - (k - (n_idx + 1));
                            match gen_rec::expr_get_d(pers, st, pre, i) {
                                Err(e) => Err(e),
                                Ok(d) => match expr_ops::pi_result(pers, st, CORE_WALK_FUEL, &d) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        if r.tag() == ETAG_SORT {
                                            match view_sort(pers, st, &r) {
                                                None => fail_dangling_e(),
                                                Some(u) => Ok(Some(u)),
                                            }
                                        } else {
                                            Ok(None)
                                        }
                                    }
                                },
                            }
                        } else {
                            Ok(None)
                        }
                    }
                }
            } else {
                Ok(None)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:45-53 iotaFrame
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:91-105 iotaFrame` —
/// **a recursor's frame**: its rule prefix, the domains of the index binders
/// and the major's, the body after them, and the motive's sort level.
pub fn iota_frame(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    m_i: u64,
    r_p: u64,
) -> Result<Option<(Vec<EIdx>, Vec<EIdx>, EIdx, LIdx)>, CheckError> {
    match expr_ops::strip_pis(pers, st, r_p, &cv.ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((pre, rest))) => {
            match expr_ops::strip_pis(pers, st, crate::kernel::expr_ops::sub_nat(m_i, r_p) + 1, &rest) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some((doms, body))) => {
                    match motive_level(pers, st, &pre, crate::kernel::expr_ops::sub_nat(m_i, r_p), &body) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some(u)) => Ok(Some((pre, doms, body, u))),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:107-118 isMinorAt` —
/// is the prefix binder at `q` a minor premise of the motive at `mot`.
pub fn is_minor_at(
    pers: &PersTier,
    st: &mut AState,
    pre: &Vec<EIdx>,
    mot: u64,
    q: u64,
) -> Result<bool, CheckError> {
    match gen_rec::expr_get_d(pers, st, pre, q) {
        Err(e) => Err(e),
        Ok(d) => match pi_tele(pers, st, CORE_WALK_FUEL, &d) {
            Err(e) => Err(e),
            Ok(t) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &t.1) {
                Err(e) => Err(e),
                Ok(hd) => {
                    if hd.tag() == ETAG_BVAR {
                        match view_bvar(pers, st, &hd) {
                            None => fail_dangling_e(),
                            Some(m) => {
                                if mot < q {
                                    Ok(m == t.0 + (q - 1 - mot))
                                } else {
                                    Ok(false)
                                }
                            }
                        }
                    } else {
                        Ok(false)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:88-94 minorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:120-129 minorsFrom` —
/// the minor premises of the motive at `mot` from position `q` on, behind the
/// accumulator `out`.
pub fn minors_from(
    pers: &PersTier,
    st: &mut AState,
    pre: &Vec<EIdx>,
    mot: u64,
    q: u64,
    out: Vec<u64>,
) -> Result<Vec<u64>, CheckError> {
    if q < pre.len() as u64 {
        match is_minor_at(pers, st, pre, mot, q) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut o: Vec<u64> = out;
                if b {
                    o.push(q);
                }
                minors_from(pers, st, pre, mot, q + 1, o)
            }
        }
    } else {
        Ok(out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:131-142 IotaRec` —
/// what every rule of a recursor reads off its type: the rule prefix, the
/// minor premises of the motive, the major's levels and parameters.
pub struct IotaRec {
    pub pre: Vec<EIdx>,
    pub minors: Vec<u64>,
    pub us: LsIdx,
    pub params: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:162-176 iotaRecOf` —
/// the rule-independent part of `iotaPartsOf`, read once per recursor.
pub fn iota_rec_of(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    m_i: u64,
    r_p: u64,
) -> Result<Option<IotaRec>, CheckError> {
    let n_idx: u64 = crate::kernel::expr_ops::sub_nat(m_i, r_p);
    match iota_frame(pers, st, cv, m_i, r_p) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some((pre, doms, body, _))) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &body) {
            Err(e) => Err(e),
            Ok(hd) => {
                if hd.tag() == ETAG_BVAR {
                    match view_bvar(pers, st, &hd) {
                        None => fail_dangling_e(),
                        Some(k) => iota_rec_major(pers, st, pre, &doms, n_idx, r_p, k),
                    }
                } else {
                    Ok(None)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:144-160 iotaRecMajor` —
/// `iotaRecOf` past the motive's head `k`: the minor premises, then the
/// major's type at a constant head (a split for the tail-call rule).
pub fn iota_rec_major(
    pers: &PersTier,
    st: &mut AState,
    pre: Vec<EIdx>,
    doms: &Vec<EIdx>,
    n_idx: u64,
    r_p: u64,
    k: u64,
) -> Result<Option<IotaRec>, CheckError> {
    match minors_from(pers, st, &pre, crate::kernel::expr_ops::sub_nat(r_p + n_idx, k), 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(minors) => match gen_rec::expr_get_d(pers, st, doms, n_idx) {
            Err(e) => Err(e),
            Ok(dom) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &dom) {
                Err(e) => Err(e),
                Ok(dh) => {
                    if dh.tag() == ETAG_CONST {
                        match view_const(pers, st, &dh) {
                            None => fail_dangling_e(),
                            Some((_, us)) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &dom) {
                                Err(e) => Err(e),
                                Ok(args) => {
                                    let lead: Vec<EIdx> = expr_ops::take_eidx_n(
                                        &args,
                                        crate::kernel::expr_ops::sub_nat(args.len() as u64, n_idx),
                                    );
                                    match install::drop_vars_all(pers, st, n_idx, &lead, 0, Vec::new()) {
                                        Err(e) => Err(e),
                                        Ok(ps) => Ok(Some(IotaRec { pre, minors, us, params: ps })),
                                    }
                                }
                            },
                        }
                    } else {
                        Ok(None)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:55-62 IotaParts
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:178-186 IIotaParts` —
/// the parts a rule's ι equation is built from.
pub struct IIotaParts {
    pub field_doms: Vec<EIdx>,
    pub idx: Vec<EIdx>,
    pub us: LsIdx,
    pub params: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:188-196 liftFieldDoms` —
/// `fd.mapIdx (fun j d => d.liftLooseBVars amt j)`, from field `i` on.
pub fn lift_field_doms(
    pers: &PersTier,
    st: &mut AState,
    amt: u64,
    fd: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= fd.len() {
        Ok(out)
    } else {
        match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, amt, i as u64, &fd[i]) {
            Err(e) => Err(e),
            Ok(d) => {
                let mut o: Vec<EIdx> = out;
                o.push(d);
                lift_field_doms(pers, st, amt, fd, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:198-209 liftIdxArgs` —
/// the conclusion's leading arguments as indices, from `i` on.
pub fn lift_idx_args(
    pers: &PersTier,
    st: &mut AState,
    amt: u64,
    n_t: u64,
    n_f: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        match install::expr_drop_vars(pers, st, n_t, xs[i].dup2()) {
            Err(e) => Err(e),
            Ok(b) => match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, amt, n_f, &b) {
                Err(e) => Err(e),
                Ok(c) => {
                    let mut o: Vec<EIdx> = out;
                    o.push(c);
                    lift_idx_args(pers, st, amt, n_t, n_f, xs, i + 1, o)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaEq.lean:96-115 iotaPartsOf
/// con-leche: ConLeche/Cached/IotaReadC.lean:34-47 iotaPartsOfC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:211-230 iotaPartsOfAt` —
/// **a rule's parts, read off the recursor's own type**, at its frame `rr`:
/// the `i`-th minor premise's fields and its conclusion's indices.
pub fn iota_parts_of_at(
    pers: &PersTier,
    st: &mut AState,
    rr: &IotaRec,
    r_p: u64,
    n_idx: u64,
    i: usize,
    rl: &IRecRule,
) -> Result<Option<IIotaParts>, CheckError> {
    if i < rr.minors.len() {
        let q: u64 = rr.minors[i];
        match gen_rec::expr_get_d(pers, st, &rr.pre, q) {
            Err(e) => Err(e),
            Ok(d) => match expr_ops::strip_pis(pers, st, rl.nfields, &d) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some((fd, inner))) => {
                    let amt: u64 = crate::kernel::expr_ops::sub_nat(r_p, q);
                    match lift_field_doms(pers, st, amt, &fd, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(fds) => match pi_tele(pers, st, CORE_WALK_FUEL, &inner) {
                            Err(e) => Err(e),
                            Ok(t) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &t.1) {
                                Err(e) => Err(e),
                                Ok(args) => {
                                    let lead: Vec<EIdx> = expr_ops::take_eidx_n(&args, n_idx);
                                    match lift_idx_args(pers, st, amt, t.0, rl.nfields, &lead, 0, Vec::new()) {
                                        Err(e) => Err(e),
                                        Ok(idx) => Ok(Some(IIotaParts {
                                            field_doms: fds,
                                            idx,
                                            us: rr.us.dup2(),
                                            params: env::eidx_vec_dup(&rr.params),
                                        })),
                                    }
                                }
                            },
                        },
                    }
                }
            },
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// The proofs' reading: through the constructor (`IotaRead.lean`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:50-58 RecRule.ctorLevels
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:234-242 ctorLevelsAt` —
/// the levels a rule's constructor is used at, interned.
pub fn ctor_levels_at(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    ctor_lps: &Vec<NIdx>,
) -> Result<LsIdx, CheckError> {
    match &rl.fire {
        IRecRuleFire::Nested(lvls, _) => intern_ls_node(pers, st, env::lidx_vec_dup(lvls)),
        IRecRuleFire::Levels(lvls) => intern_ls_node(pers, st, env::lidx_vec_dup(lvls)),
        IRecRuleFire::Plain => struct_parts::param_levels(pers, st, ctor_lps),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:244-252 iotaBVars` —
/// `(List.range n).map fun i => .bvar (rP - 1 - i)`, from `i` on.
pub fn iota_bvars(
    pers: &PersTier,
    st: &mut AState,
    r_p: u64,
    n: u64,
    i: u64,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i < n {
        match intern_e_bvar(pers, st, r_p - 1 - i) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut o: Vec<EIdx> = out;
                o.push(b);
                iota_bvars(pers, st, r_p, n, i + 1, o)
            }
        }
    } else {
        Ok(out)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:60-66 RecRule.iotaParams
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:254-261 iotaParamsAt` —
/// the parameters a rule applies its constructor to: a nested rule's pins,
/// else the prefix's first `cnP` variables.
pub fn iota_params_at(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    r_p: u64,
    cn_p: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match &rl.fire {
        IRecRuleFire::Nested(_, pins) => Ok(env::eidx_vec_dup(pins)),
        _ => {
            let n: u64 = if cn_p <= r_p { cn_p } else { r_p };
            iota_bvars(pers, st, r_p, n, 0, Vec::new())
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:70-82 iotaPartsAt
/// con-leche: ConLeche/Cached/IotaReadC.lean:23-32 iotaPartsAtC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:284-298 iotaPartsAt` —
/// **a rule's parts, read through the constructor `cvj`**, with the
/// constructor's parameter domains at the rule's levels.
pub fn iota_parts_at(
    pers: &PersTier,
    st: &mut AState,
    cvj: &IConstantVal,
    cn_p: u64,
    m_i: u64,
    r_p: u64,
    rl: &IRecRule,
) -> Result<Option<(IIotaParts, Vec<EIdx>)>, CheckError> {
    match ctor_levels_at(pers, st, rl, &cvj.level_params) {
        Err(e) => Err(e),
        Ok(lvls) => match iota_params_at(pers, st, rl, r_p, cn_p) {
            Err(e) => Err(e),
            Ok(params) => match expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cvj.level_params, &lvls, &cvj.ty) {
                Err(e) => Err(e),
                Ok(ty) => match expr_ops::strip_pis(pers, st, cn_p, &ty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some((pd, ctor_body))) => {
                        iota_parts_at_body(pers, st, cn_p, m_i, r_p, rl, lvls, params, pd, &ctor_body)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:70-82 iotaPartsAt
/// con-leche: ConLeche/Cached/IotaReadC.lean:23-32 iotaPartsAtC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:263-282 iotaPartsAtBody` —
/// past the parameters: the body at them, the fields' domains, the indices
/// and the shape guard (a split for the tail-call rule).
pub fn iota_parts_at_body(
    pers: &PersTier,
    st: &mut AState,
    cn_p: u64,
    m_i: u64,
    r_p: u64,
    rl: &IRecRule,
    lvls: LsIdx,
    params: Vec<EIdx>,
    pd: Vec<EIdx>,
    ctor_body: &EIdx,
) -> Result<Option<(IIotaParts, Vec<EIdx>)>, CheckError> {
    // the substitution vector is newest last: `params` is `params.reverse`'s reading
    match expr_ops::instantiate_lift_fast(pers, st, CORE_WALK_FUEL, ctor_body, &params, 0) {
        Err(e) => Err(e),
        Ok(body) => match expr_ops::strip_pis(pers, st, rl.nfields, &body) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some((field_doms, concl))) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, &concl) {
                Err(e) => Err(e),
                Ok(args) => {
                    let indices: Vec<EIdx> = core::drop_eidx_n(&args, cn_p);
                    if params.len() as u64 == cn_p && r_p <= m_i && indices.len() as u64 == m_i - r_p {
                        Ok(Some((IIotaParts { field_doms, idx: indices, us: lvls, params }, pd)))
                    } else {
                        Ok(None)
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The checker's rule: the two readings are one
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:99-112 Expr.lvlEq
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:302-352 lvlEq` —
/// **equal up to equivalent universe levels**.
pub fn lvl_eq(pers: &PersTier, st: &mut AState, fuel: u64, a: &EIdx, b: &EIdx) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LVL_EQ)))
    } else if a.eq2(b) {
        Ok(true)
    } else if a.tag() == b.tag() {
        if a.tag() == ETAG_SORT {
            match (view_sort(pers, st, a), view_sort(pers, st, b)) {
                (Some(u), Some(v)) => match read_level_m(pers, st, &u) {
                    Err(e) => Err(e),
                    Ok(lu) => match read_level_m(pers, st, &v) {
                        Err(e) => Err(e),
                        Ok(lv) => Ok(match level::is_equiv(&lu, &lv) {
                            Some(r) => r,
                            None => false,
                        }),
                    },
                },
                _ => fail_dangling_e(),
            }
        } else if a.tag() == ETAG_CONST {
            match (view_const(pers, st, a), view_const(pers, st, b)) {
                (Some((n, us)), Some((m, vs))) => {
                    if n.eq2(&m) {
                        match read_levels_m(pers, st, &us) {
                            Err(e) => Err(e),
                            Ok(lu) => match read_levels_m(pers, st, &vs) {
                                Err(e) => Err(e),
                                Ok(lv) => Ok(match level::is_equiv_list(&lu, &lv) {
                                    Some(r) => r,
                                    None => false,
                                }),
                            },
                        }
                    } else {
                        Ok(false)
                    }
                }
                _ => fail_dangling_e(),
            }
        } else if a.tag() == ETAG_APP {
            match (view_app(pers, st, a), view_app(pers, st, b)) {
                (Some((f, x)), Some((g, y))) => match lvl_eq(pers, st, fuel - 1, &f, &g) {
                    Err(e) => Err(e),
                    Ok(true) => lvl_eq(pers, st, fuel - 1, &x, &y),
                    Ok(false) => Ok(false),
                },
                _ => fail_dangling_e(),
            }
        } else if a.tag() == ETAG_LAM || a.tag() == ETAG_FORALL_E {
            match (view_bind(pers, st, a), view_bind(pers, st, b)) {
                (Some((t, x)), Some((t2, y))) => match lvl_eq(pers, st, fuel - 1, &t, &t2) {
                    Err(e) => Err(e),
                    Ok(true) => lvl_eq(pers, st, fuel - 1, &x, &y),
                    Ok(false) => Ok(false),
                },
                _ => fail_dangling_e(),
            }
        } else if a.tag() == ETAG_LET_E {
            match (view_let(pers, st, a), view_let(pers, st, b)) {
                (Some((t, v, x)), Some((t2, v2, y))) => match lvl_eq(pers, st, fuel - 1, &t, &t2) {
                    Err(e) => Err(e),
                    Ok(true) => match lvl_eq(pers, st, fuel - 1, &v, &v2) {
                        Err(e) => Err(e),
                        Ok(true) => lvl_eq(pers, st, fuel - 1, &x, &y),
                        Ok(false) => Ok(false),
                    },
                    Ok(false) => Ok(false),
                },
                _ => fail_dangling_e(),
            }
        } else if a.tag() == ETAG_PROJ {
            match (view_proj(pers, st, a), view_proj(pers, st, b)) {
                (Some((s, i, x)), Some((s2, i2, y))) => {
                    if s.eq2(&s2) && i == i2 {
                        lvl_eq(pers, st, fuel - 1, &x, &y)
                    } else {
                        Ok(false)
                    }
                }
                _ => fail_dangling_e(),
            }
    } else {
            Ok(false)
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:114-118 optParamName
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:354-358 topName` — a
/// top-level name, interned.
pub fn top_name(pers: &PersTier, st: &mut AState, s: Vec<u32>) -> Result<NIdx, CheckError> {
    match intern_n_node(pers, st, NNodeView::Anonymous) {
        Err(e) => Err(e),
        Ok(a) => intern_n_node(pers, st, NNodeView::Str(a, s)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:120-127 annWitness
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:360-378 annWitness` —
/// **a type a stored constant inhabits**: `D` is a constant `n` at no levels
/// and `n.missing` is stored at no levels with type `D`.
pub fn ann_witness(pers: &PersTier, st: &mut AState, fe: &IFEnv, d: &EIdx) -> Result<bool, CheckError> {
    if d.tag() == ETAG_CONST {
        match view_const(pers, st, d) {
            None => fail_dangling_e(),
            Some((n, us)) => match view_ls_len(pers, st, &us) {
                Some(0) => match intern_n_node(pers, st, NNodeView::Str(n, code_points(&MISSING))) {
                    Err(e) => Err(e),
                    Ok(m) => match env::ifenv_find(pers, fe, &m) {
                        Some(c) => {
                            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
                            Ok(cv.ty.eq2(d) && cv.level_params.len() == 0)
                        }
                        None => Ok(false),
                    },
                },
                Some(_) => Ok(false),
                None => fail_dangling_ls(),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:410-429 annIdentVal` —
/// `fun (α : Sort p) => α` at arity 1, `fun (α : Sort p) (_ : D) => α` at
/// arity 2 with `D` either `α` or a type a stored constant inhabits.
pub fn ann_ident_val(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    arity: u64,
    v: &EIdx,
) -> Result<bool, CheckError> {
    if lps.len() == 1 {
        if v.tag() == ETAG_LAM {
            match view_bind(pers, st, v) {
                None => fail_dangling_e(),
                Some((ty, b)) => {
                    if ty.tag() == ETAG_SORT {
                        match view_sort(pers, st, &ty) {
                            None => fail_dangling_e(),
                            Some(u) => match view_l(pers, st, &u) {
                                Err(e) => Err(e),
                                Ok(LNodeView::Param(p2)) => ann_ident_body(pers, st, fe, &lps[0], &p2, arity, &b),
                                Ok(_) => Ok(false),
                            },
                        }
                    } else {
                        Ok(false)
                    }
                }
            }
        } else {
            Ok(false)
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:129-134 annIdentVal
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:380-408 annIdentBody` —
/// the value's body under `fun (α : Sort p')`, at the definition's level
/// parameter `p` (a split for the tail-call rule).
pub fn ann_ident_body(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    p: &NIdx,
    p2: &NIdx,
    arity: u64,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if arity == 1 {
        if b.tag() == ETAG_BVAR {
            match view_bvar(pers, st, b) {
                None => fail_dangling_e(),
                Some(j) => Ok(j == 0 && p.eq2(p2)),
            }
        } else {
            Ok(false)
        }
    } else if arity == 2 {
        if b.tag() == ETAG_LAM {
            match view_bind(pers, st, b) {
                None => fail_dangling_e(),
                Some((d, c)) => {
                    if c.tag() == ETAG_BVAR {
                        match view_bvar(pers, st, &c) {
                            None => fail_dangling_e(),
                            Some(j) => {
                                if j == 1 && p.eq2(p2) {
                                    match intern_e_bvar(pers, st, 0) {
                                        Err(e) => Err(e),
                                        Ok(z) => {
                                            if d.eq2(&z) {
                                                Ok(true)
                                            } else {
                                                ann_witness(pers, st, fe, &d)
                                            }
                                        }
                                    }
                                } else {
                                    Ok(false)
                                }
                            }
                        }
                    } else {
                        Ok(false)
                    }
                }
            }
        } else {
            Ok(false)
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:136-145 annIdent
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:431-437 annIdent` —
/// **an annotation stored as the identity on its type argument**.
pub fn ann_ident(pers: &PersTier, st: &mut AState, fe: &IFEnv, n: &NIdx, arity: u64) -> Result<bool, CheckError> {
    match env::ifenv_find(pers, fe, n) {
        Some(IConstantInfo::DefnInfo(cv, v, _)) => ann_ident_val(pers, st, fe, &cv.level_params, arity, v),
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:147-158 annEq
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:439-482 annEq` —
/// **`s` is `c` with type annotations consumed at its head**, up to
/// equivalent levels.
pub fn ann_eq(pers: &PersTier, st: &mut AState, fe: &IFEnv, fuel: u64, s: &EIdx, c: &EIdx) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ANN_EQ)))
    } else {
        match lvl_eq(pers, st, CORE_WALK_FUEL, s, c) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => {
                if c.tag() == ETAG_APP {
                    match view_app(pers, st, c) {
                        None => fail_dangling_e(),
                        Some((f, x)) => {
                            if f.tag() == ETAG_APP {
                                match view_app(pers, st, &f) {
                                    None => fail_dangling_e(),
                                    Some((g, a)) => {
                                        if g.tag() == ETAG_CONST {
                                            match view_const(pers, st, &g) {
                                                None => fail_dangling_e(),
                                                Some((n, us)) => match view_ls_len(pers, st, &us) {
                                                    Some(1) => match top_name(pers, st, code_points(&OPT_PARAM)) {
                                                        Err(e) => Err(e),
                                                        Ok(o) => match top_name(pers, st, code_points(&AUTO_PARAM)) {
                                                            Err(e) => Err(e),
                                                            Ok(t) => {
                                                                if n.eq2(&o) || n.eq2(&t) {
                                                                    match ann_ident(pers, st, fe, &n, 2) {
                                                                        Err(e) => Err(e),
                                                                        Ok(true) => ann_eq(pers, st, fe, fuel - 1, s, &a),
                                                                        Ok(false) => Ok(false),
                                                                    }
                                                                } else {
                                                                    Ok(false)
                                                                }
                                                            }
                                                        },
                                                    },
                                                    Some(_) => Ok(false),
                                                    None => fail_dangling_ls(),
                                                },
                                            }
                                        } else {
                                            Ok(false)
                                        }
                                    }
                                }
                            } else if f.tag() == ETAG_CONST {
                                match view_const(pers, st, &f) {
                                    None => fail_dangling_e(),
                                    Some((n, us)) => match view_ls_len(pers, st, &us) {
                                        Some(1) => match top_name(pers, st, code_points(&OUT_PARAM)) {
                                            Err(e) => Err(e),
                                            Ok(o) => match top_name(pers, st, code_points(&SEMI_OUT_PARAM)) {
                                                Err(e) => Err(e),
                                                Ok(t) => {
                                                    if n.eq2(&o) || n.eq2(&t) {
                                                        match ann_ident(pers, st, fe, &n, 1) {
                                                            Err(e) => Err(e),
                                                            Ok(true) => ann_eq(pers, st, fe, fuel - 1, s, &x),
                                                            Ok(false) => Ok(false),
                                                        }
                                                    } else {
                                                        Ok(false)
                                                    }
                                                }
                                            },
                                        },
                                        Some(_) => Ok(false),
                                        None => fail_dangling_ls(),
                                    },
                                }
                            } else {
                                Ok(false)
                            }
                        }
                    }
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:484-490 listLvlEq` —
/// `listRel Expr.lvlEq`, from `i` on.
pub fn list_lvl_eq(pers: &PersTier, st: &mut AState, a: &Vec<EIdx>, b: &Vec<EIdx>, i: usize) -> Result<bool, CheckError> {
    if i >= a.len() && i >= b.len() {
        Ok(true)
    } else if i >= a.len() || i >= b.len() {
        Ok(false)
    } else {
        match lvl_eq(pers, st, CORE_WALK_FUEL, &a[i], &b[i]) {
            Err(e) => Err(e),
            Ok(true) => list_lvl_eq(pers, st, a, b, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:160-164 listRel
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:492-498 listAnnEq` —
/// `listRel (annEq find?)`, from `i` on.
pub fn list_ann_eq(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    a: &Vec<EIdx>,
    b: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= a.len() && i >= b.len() {
        Ok(true)
    } else if i >= a.len() || i >= b.len() {
        Ok(false)
    } else {
        match ann_eq(pers, st, fe, CORE_WALK_FUEL, &a[i], &b[i]) {
            Err(e) => Err(e),
            Ok(true) => list_ann_eq(pers, st, fe, a, b, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:166-175 paramsAnnEq
/// con-leche: ConLeche/Cached/IotaReadC.lean:49-56 paramsAnnEqC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:500-509 paramsAnnEq` —
/// **a plain rule's parameters fit its constructor's** (`pd`, at the rule's
/// levels).
pub fn params_ann_eq(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cn_p: u64,
    cv: &IConstantVal,
    pd: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(pers, st, cn_p, &cv.ty) {
        Err(e) => Err(e),
        Ok(Some((rd, _))) => list_ann_eq(pers, st, fe, &rd, pd, 0),
        Ok(None) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:177-185 iotaPartsRel
/// con-leche: ConLeche/Cached/IotaReadC.lean:58-64 iotaPartsRelC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:511-531 iotaPartsRel` —
/// **the two readings of a rule's parts are one**.
pub fn iota_parts_rel(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cn_p: u64,
    cv: &IConstantVal,
    rl: &IRecRule,
    p2: &IIotaParts,
    p: &IIotaParts,
    pd: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if crate::arena::canon::eidx_vec_beq(&p2.idx, &p.idx, 0)
        && p2.us.eq2(&p.us)
        && crate::arena::canon::eidx_vec_beq(&p2.params, &p.params, 0)
    {
        match list_lvl_eq(pers, st, &p2.field_doms, &p.field_doms, 0) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => match &rl.fire {
                IRecRuleFire::Plain => match params_ann_eq(pers, st, fe, cn_p, cv, pd) {
                    Err(e) => Err(e),
                    Ok(true) => list_ann_eq(pers, st, fe, &p2.field_doms, &p.field_doms, 0),
                    Ok(false) => Ok(false),
                },
                _ => Ok(false),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:187-196 ruleReadsB
/// con-leche: ConLeche/Cached/IotaReadC.lean:66-74 ruleReadsBC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:533-550 ruleReads` —
/// **one rule reads**: its parts off the recursor's type are its parts
/// through the constructor the index stores under the rule's name.
pub fn rule_reads(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    rr: &Option<IotaRec>,
    m_i: u64,
    r_p: u64,
    i: usize,
    rl: &IRecRule,
) -> Result<bool, CheckError> {
    match rr {
        None => Ok(false),
        Some(r) => match iota_parts_of_at(pers, st, r, r_p, crate::kernel::expr_ops::sub_nat(m_i, r_p), i, rl) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(p2)) => match env::ifenv_find(pers, fe, &rl.ctor) {
                Some(IConstantInfo::CtorInfo(cvj, cn_p, _, _)) => match iota_parts_at(pers, st, cvj, *cn_p, m_i, r_p, rl) {
                    Err(e) => Err(e),
                    Ok(Some((p, pd))) => iota_parts_rel(pers, st, fe, *cn_p, cv, rl, &p2, &p, &pd),
                    Ok(None) => Ok(false),
                },
                _ => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk
/// con-leche: ConLeche/Cached/IotaReadC.lean:76-84 recReadsOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:552-560 rulesRead` —
/// each rule from position `i` on reads.
pub fn rules_read(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    rr: &Option<IotaRec>,
    m_i: u64,
    r_p: u64,
    rules: &Vec<IRecRule>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= rules.len() {
        Ok(true)
    } else {
        match rule_reads(pers, st, fe, cv, rr, m_i, r_p, i, &rules[i]) {
            Err(e) => Err(e),
            Ok(true) => rules_read(pers, st, fe, cv, rr, m_i, r_p, rules, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:198-207 recReadsOk
/// con-leche: ConLeche/Cached/IotaReadC.lean:76-84 recReadsOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:562-571 recReads` —
/// **the checker's rule, at one recursor**; any other constant reads.
pub fn rec_reads(pers: &PersTier, st: &mut AState, fe: &IFEnv, ci: &IConstantInfo) -> Result<bool, CheckError> {
    match ci {
        IConstantInfo::RecInfo(cv, m_i, r_p, _, rules) => match iota_rec_of(pers, st, cv, *m_i, *r_p) {
            Err(e) => Err(e),
            Ok(rr) => rules_read(pers, st, fe, cv, &rr, *m_i, *r_p, rules, 0),
        },
        _ => Ok(true),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/IotaRead.lean:209-213 blockReadsOk
/// con-leche: ConLeche/Cached/IotaReadC.lean:86-89 blockReadsOkC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:573-579 recsRead` —
/// every recursor of the list from `i` on reads.
pub fn recs_read(pers: &PersTier, st: &mut AState, fe: &IFEnv, cs: &Vec<IConstantInfo>, i: usize) -> Result<bool, CheckError> {
    if i >= cs.len() {
        Ok(true)
    } else {
        match rec_reads(pers, st, fe, &cs[i]) {
            Err(e) => Err(e),
            Ok(true) => recs_read(pers, st, fe, cs, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckDecl.lean:28-170 checkDeclKind
/// con-leche: ConLeche/Cached/ParsedC.lean:108-128 checkIndDeclC
/// Lean twin: `proof/ConRon/Arena/Inductives/IotaRead.lean:581-594 blockReadsAt` —
/// **the checker's rule, at a block** (`blockReadsOk`): every recursor the
/// block installs reads against the index `fe` with the block's constants
/// pushed in place.  Answers the verdict and the index with the pushes undone.
pub fn block_reads_at(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    p: &BlockShape,
) -> Result<(bool, IFEnv), CheckError> {
    match install::block_constants(pers, st, p) {
        Err(e) => Err(e),
        Ok(cs) => match install::block_recs(pers, st, p, &p.recs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(recs) => {
                let nl: bool = fe.nat_lit;
                let sl: bool = fe.str_lit;
                let (fe_r, prevs) = block_tail::cons_block_recs_temp(pers, &cs, 0, fe, Vec::new());
                match recs_read(pers, st, &fe_r, &recs, 0) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        let mut fe0: IFEnv = gen_rec::class_fe_r_pop(fe_r, &prevs, prevs.len());
                        env::ifenv_set_flags(&mut fe0, nl, sl);
                        Ok((ok, fe0))
                    }
                }
            }
        },
    }
}
