//! `arena::inductives::block_install` — the uniform inductive check, at k
//! members.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockInstall.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockInstall.lean` over handles, with its
//! index twins `ConLeche/Kernel/Inductives/BlockInstallF.lean` collapsed into
//! it: the capability record per member, official's `is_rec`, the formers'
//! stage (telescopes, the two agreements, the cons), the constructors'
//! stage, the positivity check on the stored constructors, the index sorts
//! and the constructors' cons.  Every stage is a check: what the block
//! installs is read off it (`arena::install`).
//!
//! ## The twin's deviations
//!
//! * **The `…F` twins collapse into these** (task #97c's deviation 1): the
//!   arena has one environment representation, `IFEnv`, so
//!   `checkBlockTeleF`, `checkBlockIndsF`, … ARE these functions, cited
//!   beside their pure twins.  The executed recursor stage conses through
//!   `blockRecInfosTF`'s records (`arena::inductives::rec_check`), so
//!   `consBlockRecs` and `consBlockRecsBare` are not ported.
//! * **`blockCapsAt`'s record is built by branches**, not `&&`/`!`
//!   (AENEAS_FINDINGS F18).
//! * **`checkBlockPositivity`'s `find?` is the environment** (the
//!   positivity module's note), and so is `blockNestCtx`'s.
//! * **A list reversal is not needed**: the formers are consed in block order
//!   with member 0 deepest, which over the oldest-first `IFEnv` is pushing in
//!   block order.

use super::block_shape;
use super::block_shape::{shape_member_names, shape_n_idxs, with_sort, BlockShape, MemberShape};
use super::positivity;
use super::positivity::{nest_holes, nest_root, nest_state_empty, nest_uniform, NestCtx, NestFieldKind, NestState};
use super::struct_parts;
use super::sum_install;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IIndCaps};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_FORALL_E};
use crate::arena::monad::{fail, fail_dangling_e, intern_e_sort, view_bind, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The messages (con-leche's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former telescope`, as code points.
pub const M_TELE: [u32; 33] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: type former result sort`, as code points.
pub const M_TELE_SORT: [u32; 35] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 114, 101, 115, 117, 108, 116, 32, 115, 111, 114, 116,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `block: domain index`, as code points.
pub const M_DOM_IDX: [u32; 19] = [
    98, 108, 111, 99, 107, 58, 32, 100, 111, 109, 97, 105, 110, 32, 105, 110, 100, 101, 120,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `parameters of all inductive datatypes must match`, as code points.
pub const M_PARAMS: [u32; 48] = [
    112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 111, 102, 32, 97, 108, 108, 32, 105, 110,
    100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 32, 109, 117,
    115, 116, 32, 109, 97, 116, 99, 104,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `block: type former telescope`, as code points.
pub const M_BLOCK_TELE: [u32; 28] = [
    98, 108, 111, 99, 107, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101, 114, 32, 116,
    101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `mutually inductive types must live in the same universe`, as code points.
pub const M_UNIVERSE: [u32; 55] = [
    109, 117, 116, 117, 97, 108, 108, 121, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116,
    121, 112, 101, 115, 32, 109, 117, 115, 116, 32, 108, 105, 118, 101, 32, 105, 110, 32, 116, 104,
    101, 32, 115, 97, 109, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `block: no type former`, as code points.
pub const M_NO_FORMER: [u32; 21] = [
    98, 108, 111, 99, 107, 58, 32, 110, 111, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101,
    114,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: a positivity normal form outside the block's level parameters`, as code points.
pub const M_NF_LPS: [u32; 73] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 32, 112, 111, 115, 105, 116, 105,
    118, 105, 116, 121, 32, 110, 111, 114, 109, 97, 108, 32, 102, 111, 114, 109, 32, 111, 117, 116,
    115, 105, 100, 101, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 39, 115, 32, 108, 101, 118,
    101, 108, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: abstracted constructor fields`, as code points.
pub const M_ABS_FIELDS: [u32; 41] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 98, 115, 116, 114, 97, 99, 116, 101,
    100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 102, 105, 101, 108, 100, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: no type former`, as code points.
pub const M_REC_NO_FORMER: [u32; 26] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 110, 111, 32, 116, 121, 112, 101, 32,
    102, 111, 114, 109, 101, 114,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: type former telescope`, as code points.
pub const M_REC_TELE: [u32; 33] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: a member is not a stored former`, as code points.
pub const M_NOT_FORMER: [u32; 43] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 32, 109, 101, 109, 98, 101, 114, 32,
    105, 115, 32, 110, 111, 116, 32, 97, 32, 115, 116, 111, 114, 101, 100, 32, 102, 111, 114, 109,
    101, 114,
];

// ---------------------------------------------------------------------------
// The capability record, per member
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:49-81 blockCapsAt
/// Lean twin: `cs.map (·.1.name)` — the constructors' names, in order.
pub fn ctor_name_list(cs: &Vec<(IConstantVal, u64)>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(cs[i].0.name.dup2());
        ctor_name_list(cs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:49-81 blockCapsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:46-80 blockCapsAt` — **the
/// capability record of member `mi`**: at a member with ONE constructor, η
/// (index-free, the block not recursive: official's `is_non_rec_structure`)
/// and unit-likeness (and no field); at every member the block's members, its
/// parameter count, the member's index count and its constructors.
/// (`p.members.getD mi default`: the default member has no constructor and no
/// index.)
pub fn block_caps_at(p: &BlockShape, mi: u64, is_rec: bool) -> IIndCaps {
    let names: Vec<NIdx> = shape_member_names(p);
    if mi < p.members.len() as u64 && p.members[mi as usize].ctors.len() == 1 {
        let n_idx: u64 = p.members[mi as usize].n_idx;
        let c_name: NIdx = p.members[mi as usize].ctors[0].0.name.dup2();
        let c_fields: u64 = p.members[mi as usize].ctors[0].1;
        let eta: bool = if n_idx != 0 {
            false
        } else if is_rec {
            false
        } else {
            true
        };
        let unitlike: bool = if n_idx != 0 {
            false
        } else if c_fields != 0 {
            false
        } else if is_rec {
            false
        } else {
            true
        };
        let mut ctors: Vec<NIdx> = Vec::new();
        ctors.push(c_name.dup2());
        IIndCaps {
            eta,
            eta_ctor: c_name,
            eta_params: p.n_p,
            eta_fields: c_fields,
            unitlike,
            unit_params: p.n_p,
            all: names,
            nparams: p.n_p,
            n_idx,
            ctors,
        }
    } else {
        let (cs, n_idx): (Vec<NIdx>, u64) = if mi < p.members.len() as u64 {
            (ctor_name_list(&p.members[mi as usize].ctors, 0, Vec::new()), p.members[mi as usize].n_idx)
        } else {
            (Vec::new(), 0)
        };
        let mut caps: IIndCaps = env::i_ind_caps_default();
        caps.all = names;
        caps.nparams = p.n_p;
        caps.n_idx = n_idx;
        caps.ctors = cs;
        caps
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: piDomsMentionAny`, as code points.
pub const M_FUEL_PI_DOMS: [u32; 32] = [102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 68, 111, 109, 115, 77, 101, 110, 116, 105, 111, 110, 65, 110, 121];

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:83-88 Expr.piDomsMentionAny
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:82-94 piDomsMentionAny` —
/// does some binder domain of the SYNTACTIC `∀`-telescope of `e` mention one
/// of `names`?  No reduction; the `||` short-circuits.  Fueled, one unit per
/// binder, as the twin is (a walk over handles has no structural measure;
/// task #105): the callers pass `core::CORE_WALK_FUEL`.
pub fn pi_doms_mention_any(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    fuel: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_PI_DOMS)))
    } else if e.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, e) {
            None => fail_dangling_e(),
            Some((ty, b)) => match positivity::mentions_any_const(pers, st, names, &ty) {
                Err(er) => Err(er),
                Ok(true) => Ok(true),
                Ok(false) => pi_doms_mention_any(pers, st, names, fuel - 1, &b),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockIsRec
/// Lean twin: `ms.ctors.any fun c => c.1.type.piDomsMentionAny names`.
pub fn ctors_mention_any(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= cs.len() {
        Ok(false)
    } else {
        match pi_doms_mention_any(pers, st, names, core::CORE_WALK_FUEL, &cs[i].0.ty) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => ctors_mention_any(pers, st, names, cs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockIsRec
/// Lean twin: `p.members.any fun ms => …` — from member `i` on.
pub fn members_mention_any(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    ms: &Vec<MemberShape>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ms.len() {
        Ok(false)
    } else {
        match ctors_mention_any(pers, st, names, &ms[i].ctors, 0) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => members_mention_any(pers, st, names, ms, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:90-102 blockIsRec
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:96-102 blockIsRec` —
/// **official's `is_rec`**: does SOME member of the block occur in SOME binder
/// domain of the syntactic telescope of SOME DECLARED constructor type?
pub fn block_is_rec(pers: &PersTier, st: &AState, p: &BlockShape) -> Result<bool, CheckError> {
    let names: Vec<NIdx> = shape_member_names(p);
    members_mention_any(pers, st, &names, &p.members, 0)
}

// ---------------------------------------------------------------------------
// Stage 1: the formers
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:106-117 checkBlockTele
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:27-36 checkBlockTeleF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:106-119 checkBlockTele` —
/// one member's type former: the constant check, official's telescope loop
/// and the result sort, without the environment cons.
pub fn check_block_tele(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    ms: &MemberShape,
) -> Result<(IConstantVal, LIdx), CheckError> {
    match checker_base::check_constant_val(pers, st, mode, fe, &ms.cv_t, false) {
        Err(e) => Err(e),
        Ok(()) => match sum_install::check_sum_tele(pers, st, n_p + ms.n_idx, &ms.cv_t) {
            Err(e) => Err(e),
            Ok((cv_ta, s)) => match expr_ops::strip_pis(pers, st, n_p + ms.n_idx, &cv_ta.ty) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::internal(code_points(&M_TELE))),
                Ok(Some(q)) => match intern_e_sort(pers, st, s.dup2()) {
                    Err(e) => Err(e),
                    Ok(srt) => {
                        if q.1.eq2(&srt) {
                            Ok((cv_ta, s))
                        } else {
                            fail(core_types::internal(code_points(&M_TELE_SORT)))
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:119-126 checkBlockTeles
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:38-45 checkBlockTelesF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:121-130 checkBlockTeles` —
/// the members' type formers from `i` on, in block order.
pub fn check_block_teles(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<(IConstantVal, LIdx)>,
) -> Result<Vec<(IConstantVal, LIdx)>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        match check_block_tele(pers, st, mode, fe, n_p, &ms[i]) {
            Err(e) => Err(e),
            Ok(r) => {
                let mut o: Vec<(IConstantVal, LIdx)> = out;
                o.push(r);
                check_block_teles(pers, st, mode, fe, n_p, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:128-142 checkBlockDomsAt
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:47-56 checkBlockDomsAtF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:132-146 checkBlockDomsAt` —
/// **the parameter-domain agreement's comparison**: binder `j - 1`'s domain
/// against member 0's, defeq at depth `off + j - 1`, from the last binder to
/// the first; a mismatch is official's REJECT.
#[allow(clippy::too_many_arguments)]
pub fn check_block_doms_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    off: u64,
    fvs: &Vec<EIdx>,
    doms: &Vec<EIdx>,
    j: u64,
) -> Result<(), CheckError> {
    if j == 0 {
        Ok(())
    } else {
        let k: u64 = j - 1;
        match positivity::eidx_get(fvs, k) {
            None => fail(core_types::internal(code_points(&M_DOM_IDX))),
            Some(a) => match positivity::eidx_get(doms, k) {
                None => fail(core_types::internal(code_points(&M_DOM_IDX))),
                Some(b) => match expr_ops::fvar_type_d(pers, st, &a) {
                    Err(e) => Err(e),
                    Ok(at) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, off + k, &at, &b) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::invalid(code_points(&M_PARAMS))),
                        Ok(true) => check_block_doms_at(pers, st, mode, fe, off, fvs, doms, k),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:144-164 checkBlockAgree
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:58-73 checkBlockAgreeF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:148-167 checkBlockAgree` —
/// **official's two agreements between the members** from `i` on: every
/// member's parameter domains are DEFINITIONALLY member 0's, and every
/// member's result sort is equivalent to member 0's.  Both REJECT.
#[allow(clippy::too_many_arguments)]
pub fn check_block_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    cv_ta0: &IConstantVal,
    s0: &LIdx,
    rest: &Vec<(IConstantVal, LIdx)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rest.len() {
        Ok(())
    } else {
        match core::open_pis_at_fvars_f(pers, st, n_p, &cv_ta0.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::internal(code_points(&M_BLOCK_TELE))),
            Ok(Some(tq0)) => match core::open_pis_at_fvars_f(pers, st, n_p, &rest[i].0.ty, 0) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::invalid(code_points(&M_PARAMS))),
                Ok(Some(tq)) => {
                    if tq.0.len() != tq0.0.len() {
                        fail(core_types::invalid(code_points(&M_PARAMS)))
                    } else {
                        match checker_base::fvar_type_ds(pers, st, &tq0.0, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(doms) => match check_block_doms_at(pers, st, mode, fe, 0, &tq.0, &doms, n_p) {
                                Err(e) => Err(e),
                                Ok(()) => {
                                    let s: LIdx = rest[i].1.dup2();
                                    match core::lvl_eq(pers, st, &s, s0) {
                                        Err(e) => Err(e),
                                        Ok(o) => match core::lift_fueled(o) {
                                            Err(e) => Err(e),
                                            Ok(false) => fail(core_types::invalid(code_points(&M_UNIVERSE))),
                                            Ok(true) => check_block_agree(pers, st, mode, fe, n_p, cv_ta0, s0, rest, i + 1),
                                        },
                                    }
                                }
                            },
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:166-172 consBlockInds
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:75-80 consBlockIndsF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:169-177 consBlockInds` —
/// the members' formers consed, in block order (member 0 deepest), each with
/// ITS capability record at the block's `is_rec` verdict.
pub fn cons_block_inds(p1: &BlockShape, is_rec: bool, cvs: &Vec<IConstantVal>, i: usize, fe: IFEnv) -> IFEnv {
    if i >= cvs.len() {
        fe
    } else {
        let caps: IIndCaps = block_caps_at(p1, i as u64, is_rec);
        let fe2: IFEnv = env::ifenv_push(fe, IConstantInfo::IndInfo(env::i_constant_val_dup(&cvs[i]), caps));
        cons_block_inds(p1, is_rec, cvs, i + 1, fe2)
    }
}

/// con-leche: none — `p.members.map (·.declared)`
/// Lean twin: the members' formers as declared, from `i` on, in block order.
pub fn member_declared(ms: &Vec<MemberShape>, i: usize, out: Vec<IConstantVal>) -> Vec<IConstantVal> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<IConstantVal> = out;
        o.push(env::i_constant_val_dup(&ms[i].declared));
        member_declared(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:174-186 checkBlockInds
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:82-92 checkBlockIndsF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:179-194 checkBlockInds` —
/// **stage 1**: the k type formers, checked, agreed and consed — official's
/// `declare_inductive_types`, which puts every former in the environment
/// before any constructor is looked at.  Takes the index by value and
/// returns it extended; the formers are consed as declared.
pub fn check_block_inds(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    is_rec: bool,
) -> Result<(IFEnv, BlockShape), CheckError> {
    if p.members.len() == 0 {
        fail(core_types::internal(code_points(&M_NO_FORMER)))
    } else {
        let n_p: u64 = p.n_p;
        match check_block_tele(pers, st, mode, &fe, n_p, &p.members[0]) {
            Err(e) => Err(e),
            Ok((cv_ta0, s0)) => match check_block_teles(pers, st, mode, &fe, n_p, &p.members, 1, Vec::new()) {
                Err(e) => Err(e),
                Ok(cvs) => match check_block_agree(pers, st, mode, &fe, n_p, &cv_ta0, &s0, &cvs, 0) {
                    Err(e) => Err(e),
                    Ok(()) => match with_sort(pers, st, block_shape::block_shape_dup(p), s0) {
                        Err(e) => Err(e),
                        Ok(p1) => {
                            let declared: Vec<IConstantVal> = member_declared(&p.members, 0, Vec::new());
                            let fe1: IFEnv = cons_block_inds(&p1, is_rec, &declared, 0, fe);
                            Ok((fe1, p1))
                        }
                    },
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Stage 1b: the constructors, and the positivity check
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:190-196 BlockShape.nestCtx
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:198-207 BlockShape.nestCtx` —
/// **the block's positivity context** at the canonical parameter variables
/// `fvs_p`, with the members' formers at their telescopes; its lookup is the
/// environment the walk is handed (the positivity module's note); `lvls` the
/// block's own levels, interned.
pub fn shape_nest_ctx(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    fvs_p: Vec<EIdx>,
) -> Result<NestCtx, CheckError> {
    let lps: Vec<NIdx> = block_shape::shape_lps(p);
    match struct_parts::param_levels(pers, st, &lps) {
        Err(e) => Err(e),
        Ok(lvls) => Ok(NestCtx {
            names: shape_member_names(p),
            lps,
            n_p: p.n_p,
            n_idxs: shape_n_idxs(&p.members, 0, Vec::new()),
            params: fvs_p,
            sort: p.res_sort.dup2(),
            lvls,
            formers: block_shape::shape_formers(&p.members, 0, Vec::new()),
        }),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:198-207 checkBlockCtors
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:96-103 checkBlockCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:209-219 checkBlockCtors` —
/// the constructors of every member from `i` on (against the member's former
/// at its telescope), at the environment holding ALL the formers.
#[allow(clippy::too_many_arguments)]
pub fn check_block_ctors(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe0: &IFEnv,
    fe: &IFEnv,
    p: &BlockShape,
    i: usize,
) -> Result<(), CheckError> {
    if i >= p.members.len() {
        Ok(())
    } else {
        let lps: Vec<NIdx> = block_shape::shape_lps(p);
        match sum_install::check_sum_ctors(
            pers,
            st,
            mode,
            fe0,
            fe,
            &p.members[i].cv_t.name,
            &lps,
            p.n_p,
            p.members[i].n_idx,
            &p.res_sort,
            p.is_prop,
            p.large,
            &p.members[i].cv_t,
            &p.members[i].ctors,
            0,
        ) {
            Err(e) => Err(e),
            Ok(()) => check_block_ctors(pers, st, mode, fe0, fe, p, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:225-247 checkAbsCtorSorts
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:221-240 checkAbsCtorSorts` —
/// **the fields' universes at the holes**: each constructor's positivity
/// normal form within the block's level parameters (internal), its fields
/// opened above the holes and their sorts bounded by the block's (the root's
/// line of `checkStructFieldSortsI`); pairwise, stopping at the shorter list.
#[allow(clippy::too_many_arguments)]
pub fn check_abs_ctor_sorts(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    is_prop: bool,
    cs: &Vec<(IConstantVal, u64)>,
    os: &Vec<(Vec<NestFieldKind>, EIdx)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= cs.len() || i >= os.len() {
        Ok(())
    } else {
        let ty_n: EIdx = os[i].1.dup2();
        let n_f: u64 = cs[i].1;
        match checker_base::all_level_params_defined(pers, st, &ctx.lps, &ty_n) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::internal(code_points(&M_NF_LPS))),
            Ok(true) => {
                let hi: u64 = positivity::hi_at(ctx, 0);
                match core::open_pis_at_fvars_f(pers, st, n_f, &ty_n, hi) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::internal(code_points(&M_ABS_FIELDS))),
                    Ok(Some(xq)) => {
                        let none: Vec<EIdx> = Vec::new();
                        match sum_install::check_struct_field_sorts_i(
                            pers,
                            st,
                            mode,
                            fe,
                            is_prop,
                            false,
                            &ctx.sort,
                            hi,
                            &xq.0,
                            &none,
                            n_f,
                        ) {
                            Err(e) => Err(e),
                            Ok(()) => check_abs_ctor_sorts(pers, st, mode, fe, ctx, is_prop, cs, os, i + 1),
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:249-255 checkAbsCtorSortsAll
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:242-250 checkAbsCtorSortsAll`
/// — `checkAbsCtorSorts` on every member's constructors from `i` on; the
/// block's `isEquiv sort 0 == some true` read once.
#[allow(clippy::too_many_arguments)]
pub fn check_abs_ctor_sorts_all(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ctx: &NestCtx,
    is_prop: bool,
    css: &Vec<Vec<(IConstantVal, u64)>>,
    oss: &Vec<Vec<(Vec<NestFieldKind>, EIdx)>>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= css.len() || i >= oss.len() {
        Ok(())
    } else {
        match check_abs_ctor_sorts(pers, st, mode, fe, ctx, is_prop, &css[i], &oss[i], 0) {
            Err(e) => Err(e),
            Ok(()) => check_abs_ctor_sorts_all(pers, st, mode, fe, ctx, is_prop, css, oss, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:257-270 blockNestCtx
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:252-264 blockNestCtx` — **the
/// walk's context** of a block: the canonical parameter variables are the
/// first former's opened telescope, with the members' holes.  con-leche's
/// `find?` argument has no counterpart: the port's `NestCtx` carries no
/// lookup (each walk is handed the environment).
pub fn block_nest_ctx(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
) -> Result<(NestCtx, Vec<EIdx>), CheckError> {
    if p.members.len() == 0 {
        fail(core_types::internal(code_points(&M_REC_NO_FORMER)))
    } else {
        match core::open_pis_at_fvars_f(pers, st, p.n_p, &p.members[0].cv_t.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::internal(code_points(&M_REC_TELE))),
            Ok(Some(pq)) => match shape_nest_ctx(pers, st, p, pq.0) {
                Err(e) => Err(e),
                Ok(ctx) => match nest_holes(pers, st, &ctx, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::internal(code_points(&M_NOT_FORMER))),
                    Ok(Some(holes)) => Ok((ctx, holes)),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:272-274 nestOutKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:266-270 nestOutKinds` — the field
/// kinds of the root frame's outputs, from member `i` on.
pub fn nest_out_kinds(
    outs: &Vec<Vec<(Vec<NestFieldKind>, EIdx)>>,
    i: usize,
    out: Vec<Vec<Vec<NestFieldKind>>>,
) -> Vec<Vec<Vec<NestFieldKind>>> {
    if i >= outs.len() {
        out
    } else {
        let mut o: Vec<Vec<Vec<NestFieldKind>>> = out;
        o.push(split_kinds(&outs[i], 0, Vec::new()));
        nest_out_kinds(outs, i + 1, o)
    }
}

/// con-leche: none — `os.map (·.1)`, the kinds copied
/// Lean twin: one member's constructors' kinds.
pub fn split_kinds(os: &Vec<(Vec<NestFieldKind>, EIdx)>, i: usize, out: Vec<Vec<NestFieldKind>>) -> Vec<Vec<NestFieldKind>> {
    if i >= os.len() {
        out
    } else {
        let mut o: Vec<Vec<NestFieldKind>> = out;
        o.push(kinds_dup(&os[i].0, 0, Vec::new()));
        split_kinds(os, i + 1, o)
    }
}

/// con-leche: none — a `List NestFieldKind` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/Positivity.lean:398-406 NestFieldKind`.
pub fn kinds_dup(ks: &Vec<NestFieldKind>, i: usize, out: Vec<NestFieldKind>) -> Vec<NestFieldKind> {
    if i >= ks.len() {
        out
    } else {
        let mut o: Vec<NestFieldKind> = out;
        o.push(positivity::nest_field_kind_dup(&ks[i]));
        kinds_dup(ks, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:276-291 checkBlockPositivity
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:272-287 checkBlockPositivity`
/// — **the block's positivity, on its stored constructors**, at the walk's
/// context: official's uniform-occurrence check, the root frame from the
/// empty state, the fields' universes at the holes.  Returns the root frame's
/// outputs (each constructor's field kinds and normal form) and the walk's
/// state.
#[allow(clippy::type_complexity)]
pub fn check_block_positivity(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
) -> Result<(Vec<Vec<(Vec<NestFieldKind>, EIdx)>>, NestState), CheckError> {
    let ctors_as: Vec<Vec<(IConstantVal, u64)>> = block_shape::member_ctors(&p.members, 0, Vec::new());
    match block_nest_ctx(pers, st, p) {
        Err(e) => Err(e),
        Ok((ctx, holes)) => match nest_uniform(pers, st, &ctx, &ctors_as, 0) {
            Err(e) => Err(e),
            Ok(()) => match nest_root(pers, st, mode, fe, &ctx, &holes, &ctors_as, 0, nest_state_empty(), Vec::new()) {
                Err(e) => Err(e),
                Ok((outs, ns)) => match core::zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => match core::lvl_eq(pers, st, &ctx.sort, &z) {
                        Err(e) => Err(e),
                        Ok(eq) => {
                            let is_prop: bool = match eq {
                                Some(true) => true,
                                Some(false) => false,
                                None => false,
                            };
                            match check_abs_ctor_sorts_all(pers, st, mode, fe, &ctx, is_prop, &ctors_as, &outs, 0) {
                                Err(e) => Err(e),
                                Ok(()) => Ok((outs, ns)),
                            }
                        }
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Stage 2: the tail
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:295-305 checkBlockIdxSorts
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:107-115 checkBlockIdxSortsF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:291-302 checkBlockIdxSorts` —
/// every member's INDEX binders from `i` on have sorts: the member's telescope
/// opened at variables, each index domain's sort inferred (no bound is
/// checked).
pub fn check_block_idx_sorts(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &BlockShape,
    i: usize,
) -> Result<(), CheckError> {
    if i >= p.members.len() {
        Ok(())
    } else {
        let n_idx: u64 = p.members[i].n_idx;
        match core::open_pis_at_fvars_f(pers, st, p.n_p + n_idx, &p.members[i].cv_t.ty, 0) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::internal(code_points(&M_REC_TELE))),
            Ok(Some(tq)) => {
                let idx_fvs: Vec<EIdx> = core::drop_eidx_n(&tq.0, p.n_p);
                let none: Vec<EIdx> = Vec::new();
                match sum_install::check_struct_field_sorts_i(
                    pers, st, mode, fe, true, false, &p.res_sort, p.n_p, &idx_fvs, &none, n_idx,
                ) {
                    Err(e) => Err(e),
                    Ok(()) => check_block_idx_sorts(pers, st, mode, fe, p, i + 1),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockInstall.lean:307-311 consBlockCtors
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:117-120 consBlockCtorsF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockInstall.lean:304-310 consBlockCtors` —
/// the members' constructors consed from member `i` on, in block order.
pub fn cons_block_ctors(n_p: u64, ctors_as: &Vec<Vec<(IConstantVal, u64)>>, i: usize, fe: IFEnv) -> IFEnv {
    if i >= ctors_as.len() {
        fe
    } else {
        let fe2: IFEnv = sum_install::cons_sum_ctors(n_p, &ctors_as[i], 0, fe);
        cons_block_ctors(n_p, ctors_as, i + 1, fe2)
    }
}
