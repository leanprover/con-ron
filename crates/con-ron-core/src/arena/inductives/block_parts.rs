//! `arena::inductives::block_parts` — the k-ary block: the record and the
//! recogniser.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockParts.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockParts.lean` over handles: the record a
//! block on the uniform route is read into (`MemberShape`, `RecShape`,
//! `BlockShape`, `BlockParts`), its projections, and the recogniser
//! (`blockSplit`, `recTargetOf`, `blockCounts?`, `blockGroups`,
//! `blockShape?`, `blockParts?`) with the recursor records' name and level
//! pins the recursor stage throws on.
//!
//! ## The twin's deviations
//!
//! * **`BlockParts extends BlockShape` is a `shape` field**, as
//!   `NativeParts` was.
//! * **The level lists are compared as interned lists**: `lps.map .param` is
//!   `struct_parts::param_levels`, and `us == lvls` is handle equality.
//! * **A projection that reads a term takes the state** (`withSort`'s
//!   `Level.isEquiv`, `recTargetOf`'s telescope).
//! * **`BlockShape.offs` and `BlockShape.recTgtAt` are not ported**: nothing
//!   the executed checker runs reads them (the model does); the skip list
//!   says so.
//! * **The `…all`/`…any`/`find?`/`filter`/`map` closures are index
//!   recursions** (§3.4).

use super::field_tele::pi_binders;
use super::positivity::{member_idx_at, names_contain, names_find_idx};
use super::struct_parts;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IRecRule};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::monad::{fail_dangling_e, intern_n_node, view, view_bind, view_const, AState};
use crate::arena::store::{ENodeView, NNodeView, PersTier};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr_ops::sub_nat;
use crate::ron::hashmap::{Dup, Eq2};

// ---------------------------------------------------------------------------
// The record
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:54-69 MemberShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean MemberShape` — one
/// member of a block: its type former, its own index count and its
/// constructors (member-local, in block order, each with its field count).
pub struct MemberShape {
    pub cv_t: IConstantVal,
    pub n_idx: u64,
    pub ctors: Vec<(IConstantVal, u64)>,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:54-69 MemberShape
/// The record copy.
pub fn member_shape_dup(m: &MemberShape) -> MemberShape {
    MemberShape {
        cv_t: env::i_constant_val_dup(&m.cv_t),
        n_idx: m.n_idx,
        ctors: ctors_dup(&m.ctors, 0, Vec::new()),
    }
}

/// con-leche: none — a `List (ConstantVal × Nat)` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean MemberShape`.
pub fn ctors_dup(
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Vec<(IConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<(IConstantVal, u64)> = out;
        o.push((env::i_constant_val_dup(&cs[i].0), cs[i].1));
        ctors_dup(cs, i + 1, o)
    }
}

/// con-leche: none — a `List (List (ConstantVal × Nat))` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean MemberShape`.
pub fn ctorss_dup(
    css: &Vec<Vec<(IConstantVal, u64)>>,
    i: usize,
    out: Vec<Vec<(IConstantVal, u64)>>,
) -> Vec<Vec<(IConstantVal, u64)>> {
    if i >= css.len() {
        out
    } else {
        let mut o: Vec<Vec<(IConstantVal, u64)>> = out;
        o.push(ctors_dup(&css[i], 0, Vec::new()));
        ctorss_dup(css, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:71-96 RecShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean RecShape` — **one
/// recursor of a block, as the stream carries it**: its constant, the
/// record's own rule prefix `rP` and major index `mI`, the member its MAJOR
/// names (`k`: none — a nested block's auxiliary recursor), and its rules'
/// right-hand sides as exported.
pub struct RecShape {
    pub cv_r: IConstantVal,
    pub r_p: u64,
    pub m_i: u64,
    pub tgt: u64,
    pub rhss: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:71-96 RecShape
/// The record copy.
pub fn rec_shape_dup(r: &RecShape) -> RecShape {
    RecShape {
        cv_r: env::i_constant_val_dup(&r.cv_r),
        r_p: r.r_p,
        m_i: r.m_i,
        tgt: r.tgt,
        rhss: env::eidx_vec_dup(&r.rhss),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:98-121 BlockShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape` — the
/// pieces of a recognised block at any number of members: the members, the
/// recursors, the SHARED parameter count, elimination level parameter
/// (`.anonymous` for a small eliminator) and result sort, and the two flags.
pub struct BlockShape {
    pub members: Vec<MemberShape>,
    pub recs: Vec<RecShape>,
    pub n_p: u64,
    pub elim: NIdx,
    pub res_sort: LIdx,
    pub large: bool,
    pub is_prop: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:98-121 BlockShape
/// The record copy.
pub fn block_shape_dup(p: &BlockShape) -> BlockShape {
    BlockShape {
        members: members_dup(&p.members, 0, Vec::new()),
        recs: recs_dup(&p.recs, 0, Vec::new()),
        n_p: p.n_p,
        elim: p.elim.dup2(),
        res_sort: p.res_sort.dup2(),
        large: p.large,
        is_prop: p.is_prop,
    }
}

/// con-leche: none — a `List MemberShape` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape`.
pub fn members_dup(ms: &Vec<MemberShape>, i: usize, out: Vec<MemberShape>) -> Vec<MemberShape> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<MemberShape> = out;
        o.push(member_shape_dup(&ms[i]));
        members_dup(ms, i + 1, o)
    }
}

/// con-leche: none — a `List RecShape` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape`.
pub fn recs_dup(rs: &Vec<RecShape>, i: usize, out: Vec<RecShape>) -> Vec<RecShape> {
    if i >= rs.len() {
        out
    } else {
        let mut o: Vec<RecShape> = out;
        o.push(rec_shape_dup(&rs[i]));
        recs_dup(rs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:123-127 numCtorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean numCtorsOf` — the
/// constructors of a list of members (`ms[i..]`), counted.
pub fn num_ctors_of(ms: &Vec<MemberShape>, i: usize) -> u64 {
    if i >= ms.len() {
        0
    } else {
        (ms[i].ctors.len() as u64) + num_ctors_of(ms, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:131-132 BlockShape.k
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.k` — the
/// number of members.
pub fn shape_k(p: &BlockShape) -> u64 {
    p.members.len() as u64
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:133-134 BlockShape.numCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.numCtors`
/// — the number of constructors of the whole block.
pub fn shape_num_ctors(p: &BlockShape) -> u64 {
    num_ctors_of(&p.members, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:137-138 BlockShape.memberNames
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.memberNames`
/// — the members' names, in block order (an index recursion from `i`).
pub fn member_names(ms: &Vec<MemberShape>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(ms[i].cv_t.name.dup2());
        member_names(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:137-138 BlockShape.memberNames
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.memberNames`.
pub fn shape_member_names(p: &BlockShape) -> Vec<NIdx> {
    member_names(&p.members, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:139-140 BlockShape.nIdxs
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.nIdxs` —
/// the members' index counts, in block order.
pub fn shape_n_idxs(ms: &Vec<MemberShape>, i: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<u64> = out;
        o.push(ms[i].n_idx);
        shape_n_idxs(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:141-144 BlockShape.lps
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.lps` — the
/// block's level parameters (member 0's; `[]` at no member).
pub fn shape_lps(p: &BlockShape) -> Vec<NIdx> {
    if p.members.len() == 0 {
        Vec::new()
    } else {
        env::nidx_vec_dup(&p.members[0].cv_t.level_params)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:145-147 BlockShape.allCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.allCtors`
/// — the constructors of the whole block, in block order.
pub fn all_ctors(ms: &Vec<MemberShape>, i: usize, out: Vec<(IConstantVal, u64)>) -> Vec<(IConstantVal, u64)> {
    if i >= ms.len() {
        out
    } else {
        let o: Vec<(IConstantVal, u64)> = ctors_dup(&ms[i].ctors, 0, out);
        all_ctors(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:154-160 BlockShape.rulePrefixAt
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.rulePrefixAt`
/// — recursor `r`'s rule prefix, the RECORD's (`0`, the default record's, off
/// the list).
pub fn rule_prefix_at(p: &BlockShape, r: u64) -> u64 {
    if r < p.recs.len() as u64 {
        p.recs[r as usize].r_p
    } else {
        0
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:162-165 BlockShape.majorIdxAt
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.majorIdxAt`
/// — recursor `r`'s major-premise index, the RECORD's.
pub fn major_idx_at(p: &BlockShape, r: u64) -> u64 {
    if r < p.recs.len() as u64 {
        p.recs[r as usize].m_i
    } else {
        0
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:167-171 BlockShape.withSort
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockShape.withSort` —
/// the record completed with the former stage's result sort, `isProp`
/// recomputed from it.
pub fn with_sort(pers: &PersTier, st: &mut AState, p: BlockShape, s: LIdx) -> Result<BlockShape, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match core::lvl_eq(pers, st, &s, &z) {
            Err(e) => Err(e),
            Ok(eq) => {
                let is_prop: bool = match eq {
                    Some(true) => true,
                    Some(false) => false,
                    None => false,
                };
                let mut q: BlockShape = p;
                q.res_sort = s;
                q.is_prop = is_prop;
                Ok(q)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:198-201 BlockParts
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockParts` — a
/// recognised block: its shape (`extends BlockShape`, a field here).
pub struct BlockParts {
    pub shape: BlockShape,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:203-206 BlockParts.complete
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean BlockParts.complete`
/// — **the record completed by the formers' stage**: the shape the formers'
/// run returned.
pub fn complete(_p0: &BlockParts, p1: BlockShape) -> BlockParts {
    BlockParts { shape: p1 }
}

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:231-237 blockSplitRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockSplitRecs` — the
/// closing recursors from `i` on: `none` at anything else.
pub fn block_split_recs(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
) -> Option<Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>> {
    if i >= block.len() {
        Some(out)
    } else {
        match &block[i] {
            IConstantInfo::RecInfo(cv, m_i, r_p, rules) => {
                let mut o: Vec<(IConstantVal, u64, u64, Vec<IRecRule>)> = out;
                o.push((env::i_constant_val_dup(cv), *m_i, *r_p, env::i_rec_rules_dup(rules)));
                block_split_recs(block, i + 1, o)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:239-244 blockSplitCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockSplitCtors` —
/// the constructors from `i` on, then the recursors.
#[allow(clippy::type_complexity)]
pub fn block_split_ctors(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64)>,
) -> Option<(Vec<(IConstantVal, u64, u64)>, Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>)> {
    if i < block.len() && is_ctor_info(&block[i]) {
        let mut o: Vec<(IConstantVal, u64, u64)> = out;
        o.push(ctor_info_parts(&block[i]));
        block_split_ctors(block, i + 1, o)
    } else {
        match block_split_recs(block, i, Vec::new()) {
            None => None,
            Some(rs) => Some((out, rs)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:239-244 blockSplitCtors
/// Lean twin: the cited `.ctorInfo … :: rest` pattern's test, its own function
/// so the element's loan ends before the recursion (extraction rule 1).
pub fn is_ctor_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::CtorInfo(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:239-244 blockSplitCtors
/// Lean twin: the `.ctorInfo cvC nP nF` pattern's fields, copied out.  Reached
/// only past `is_ctor_info`; the other arm is the default the total function
/// needs.
pub fn ctor_info_parts(ci: &IConstantInfo) -> (IConstantVal, u64, u64) {
    match ci {
        IConstantInfo::CtorInfo(cv, n_p, n_f) => (env::i_constant_val_dup(cv), *n_p, *n_f),
        _ => (env::i_constant_info_dummy_val(), 0, 0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:246-252 blockSplit
/// Lean twin: the `.indInfo cvT _` pattern's test.
pub fn is_ind_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::IndInfo(_, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:246-252 blockSplit
/// Lean twin: the `.indInfo cvT _` pattern's constant, copied out.
pub fn ind_info_val(ci: &IConstantInfo) -> IConstantVal {
    match ci {
        IConstantInfo::IndInfo(cv, _) => env::i_constant_val_dup(cv),
        _ => env::i_constant_info_dummy_val(),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:246-252 blockSplit
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockSplit` — the
/// type formers from `i` on, the constructors and the recursors.
#[allow(clippy::type_complexity)]
pub fn block_split(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<IConstantVal>,
) -> Option<(
    Vec<IConstantVal>,
    Vec<(IConstantVal, u64, u64)>,
    Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
)> {
    if i < block.len() && is_ind_info(&block[i]) {
        let mut o: Vec<IConstantVal> = out;
        o.push(ind_info_val(&block[i]));
        block_split(block, i + 1, o)
    } else {
        match block_split_ctors(block, i, Vec::new()) {
            None => None,
            Some((cs, rs)) => Some((out, cs, rs)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:254-271 recTargetOf
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean recTargetOf` — **the
/// member a recursor's MAJOR names**: strip the `mI` binders the record
/// claims, the next binder is the major, and its domain's head constant is
/// read against the member names; `names.length` — no member — otherwise.
pub fn rec_target_of(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    m_i: u64,
    ty: &EIdx,
) -> Result<u64, CheckError> {
    let none: u64 = names.len() as u64;
    match expr_ops::strip_pis(pers, st, m_i, ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(none),
        Ok(Some(q)) => {
            if q.1.tag() == ETAG_FORALL_E {
                match view_bind(pers, st, &q.1) {
                    None => fail_dangling_e(),
                    Some((dom, _, _)) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &dom) {
                        Err(e) => Err(e),
                        Ok(hd) => {
                            if hd.tag() == ETAG_CONST {
                                match view_const(pers, st, &hd) {
                                    None => fail_dangling_e(),
                                    Some((n, _)) => match names_find_idx(names, &n, 0) {
                                        Some(t) => Ok(t),
                                        None => Ok(none),
                                    },
                                }
                            } else {
                                Ok(none)
                            }
                        }
                    },
                }
            } else {
                Ok(none)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockCounts?` — **one
/// member's parameter and index counts**, read as official reads them: off
/// the member's own telescope when it is a syntactic one ending in a sort,
/// else off the argument sums of a recursor whose major names the member.
#[allow(clippy::too_many_arguments)]
pub fn block_counts(
    pers: &PersTier,
    st: &AState,
    n_pd: u64,
    k: u64,
    n_c: u64,
    n_r: u64,
    cv_t: &IConstantVal,
    r: Option<(u64, u64)>,
) -> Result<Option<(u64, u64)>, CheckError> {
    match pi_binders(pers, st, CORE_WALK_FUEL, &cv_t.ty, Vec::new()) {
        Err(e) => Err(e),
        Ok((bs, res)) => match view(pers, st, &res) {
            Err(e) => Err(e),
            Ok(ENodeView::Sort(_)) => {
                let n: u64 = bs.len() as u64;
                if n_pd <= n {
                    Ok(Some((n_pd, n - n_pd)))
                } else {
                    Ok(None)
                }
            }
            Ok(_) => Ok(block_counts_rec(n_pd, k, n_c, n_r, r)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:273-299 blockCounts?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockCounts?` — the
/// def-headed former's arm: the counts off the recursor's sums.
pub fn block_counts_rec(n_pd: u64, k: u64, n_c: u64, n_r: u64, r: Option<(u64, u64)>) -> Option<(u64, u64)> {
    match r {
        None => None,
        Some((m_i, r_p)) => {
            if r_p < n_c + k || m_i < r_p {
                None
            } else if sub_nat(r_p, n_c + k) == n_pd {
                Some((n_pd, sub_nat(m_i, r_p)))
            } else if k < n_r && n_pd + n_r + n_c <= r_p {
                Some((n_pd, sub_nat(m_i, r_p)))
            } else {
                None
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:301-308 ctorMember?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean ctorMember?` — the
/// member a constructor belongs to: the one its RESULT names (at the block's
/// own levels `lvls`, `lps.map .param` interned).
pub fn ctor_member(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    n_p: u64,
    c: &(IConstantVal, u64),
) -> Result<Option<u64>, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + c.1, &c.0.ty) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(q)) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &q.1) {
            Err(e) => Err(e),
            Ok(hd) => member_idx_at(pers, st, names, lvls, &hd),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:310-323 blockGroups
/// Lean twin: `cs.filter fun c => ctorMember? names lps nP c == some m` — member
/// `m`'s constructors, in block order.
#[allow(clippy::too_many_arguments)]
pub fn block_group(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    n_p: u64,
    m: u64,
    cs: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<(IConstantVal, u64)>,
) -> Result<Vec<(IConstantVal, u64)>, CheckError> {
    if i >= cs.len() {
        Ok(out)
    } else {
        match ctor_member(pers, st, names, lvls, n_p, &cs[i]) {
            Err(e) => Err(e),
            Ok(Some(t)) => {
                if t == m {
                    let mut o: Vec<(IConstantVal, u64)> = out;
                    o.push((env::i_constant_val_dup(&cs[i].0), cs[i].1));
                    block_group(pers, st, names, lvls, n_p, m, cs, i + 1, o)
                } else {
                    block_group(pers, st, names, lvls, n_p, m, cs, i + 1, out)
                }
            }
            Ok(None) => block_group(pers, st, names, lvls, n_p, m, cs, i + 1, out),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:310-323 blockGroups
/// Lean twin: `(List.range k).map fun m => …` — the groups from member `m` on.
#[allow(clippy::too_many_arguments)]
pub fn block_groups_from(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    n_p: u64,
    k: u64,
    m: u64,
    cs: &Vec<(IConstantVal, u64)>,
    out: Vec<Vec<(IConstantVal, u64)>>,
) -> Result<Vec<Vec<(IConstantVal, u64)>>, CheckError> {
    if m >= k {
        Ok(out)
    } else {
        match block_group(pers, st, names, lvls, n_p, m, cs, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(g) => {
                let mut o: Vec<Vec<(IConstantVal, u64)>> = out;
                o.push(g);
                block_groups_from(pers, st, names, lvls, n_p, k, m + 1, cs, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:310-323 blockGroups
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockGroups` — **the
/// constructors grouped by member**, in block order: at ONE member all of
/// them, nothing read; at two or more read off the result head (a constructor
/// whose head is no member lands in no group).
pub fn block_groups(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    n_p: u64,
    k: u64,
    cs: &Vec<(IConstantVal, u64)>,
) -> Result<Vec<Vec<(IConstantVal, u64)>>, CheckError> {
    if k == 1 {
        let mut out: Vec<Vec<(IConstantVal, u64)>> = Vec::new();
        out.push(ctors_dup(cs, 0, Vec::new()));
        Ok(out)
    } else {
        block_groups_from(pers, st, names, lvls, n_p, k, 0, cs, Vec::new())
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:325-333 blockRecLpsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockRecLpsOk` — the
/// recursors from `i` on carry the block's level parameters, the elimination
/// parameter in front at the large eliminator.
pub fn block_rec_lps_ok_from(p: &BlockShape, lps: &Vec<NIdx>, i: usize) -> bool {
    if i >= p.recs.len() {
        true
    } else if rec_lps_ok(p, lps, &p.recs[i].cv_r.level_params) {
        block_rec_lps_ok_from(p, lps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:325-333 blockRecLpsOk
/// Lean twin: one recursor's level parameters against `elim :: lps` / `lps`.
pub fn rec_lps_ok(p: &BlockShape, lps: &Vec<NIdx>, rl: &Vec<NIdx>) -> bool {
    if p.large {
        if rl.len() == lps.len() + 1 {
            rl[0].eq2(&p.elim) && nidx_vec_beq_off(rl, 1, lps, 0)
        } else {
            false
        }
    } else {
        core::nidx_vec_beq(rl, lps)
    }
}

/// con-leche: none — `a.drop o == b` over name-handle lists
/// Lean twin: the tail comparison of `rc.cvR.levelParams == p.elim :: p.lps`.
pub fn nidx_vec_beq_off(a: &Vec<NIdx>, o: usize, b: &Vec<NIdx>, i: usize) -> bool {
    if o + i >= a.len() && i >= b.len() {
        true
    } else if o + i >= a.len() || i >= b.len() {
        false
    } else if a[o + i].eq2(&b[i]) {
        nidx_vec_beq_off(a, o, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:325-333 blockRecLpsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockRecLpsOk` —
/// **the recursor records' level-parameter pin**.
pub fn block_rec_lps_ok(p: &BlockShape) -> bool {
    let lps: Vec<NIdx> = shape_lps(p);
    block_rec_lps_ok_from(p, &lps, 0)
}

/// con-leche: none — the recursor-name suffix `rec`, as code points
/// Lean twin: `"rec"`.
pub const REC_SUFFIX: [u32; 3] = [114, 101, 99];

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:335-357 blockRecNameSetOk
/// Lean twin: `p.members.map fun ms => ms.cvT.name.str "rec"` — the generated
/// names, interned, in block order.
pub fn want_rec_names(
    pers: &PersTier,
    st: &mut AState,
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        match intern_n_node(pers, st, NNodeView::Str(ms[i].cv_t.name.dup2(), code_points(&REC_SUFFIX))) {
            Err(e) => Err(e),
            Ok(n) => {
                let mut o: Vec<NIdx> = out;
                o.push(n);
                want_rec_names(pers, st, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: none — `rs.map (·.cvR.name)`
/// Lean twin: the recursors' names, in the stream's order.
pub fn rec_names(rs: &Vec<RecShape>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= rs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(rs[i].cv_r.name.dup2());
        rec_names(rs, i + 1, o)
    }
}

/// con-leche: none — `xs.all (ys.contains ·)` over name-handle lists
/// Lean twin: `want.all (fun n => got.contains n)`.
pub fn names_all_in(xs: &Vec<NIdx>, ys: &Vec<NIdx>, i: usize) -> bool {
    if i >= xs.len() {
        true
    } else if names_contain(ys, &xs[i], 0) {
        names_all_in(xs, ys, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:335-357 blockRecNameSetOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockRecNameSetOk` —
/// **the recursor names, as a SET**: exactly `T_m.rec` at every member, each
/// once.
pub fn block_rec_name_set_ok(pers: &PersTier, st: &mut AState, p: &BlockShape) -> Result<bool, CheckError> {
    match want_rec_names(pers, st, &p.members, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(want) => {
            let got: Vec<NIdx> = rec_names(&p.recs, 0, Vec::new());
            Ok(got.len() == want.len() && names_all_in(&want, &got, 0) && names_all_in(&got, &want, 0))
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:359-368 blockRecNamesUnreserved
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockRecNamesUnreserved`
/// — **no recursor from `i` on takes a name the environment's own guards
/// look up** (`reservedRecName`).
pub fn block_rec_names_unreserved(st: &mut AState, rs: &Vec<RecShape>, i: usize) -> Result<bool, CheckError> {
    if i >= rs.len() {
        Ok(true)
    } else {
        let n: NIdx = rs[i].cv_r.name.dup2();
        match core::reserved_rec_name(st, &n) {
            Err(e) => Err(e),
            Ok(true) => Ok(false),
            Ok(false) => block_rec_names_unreserved(st, rs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:370-383 blockMemberCounts?
/// Lean twin: `rs.find? fun q => recTargetOf names q.2.1 q.1.type == m` — the
/// first recursor whose major names member `m`, its `(mI, rP)`.
pub fn rec_for_member(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    m: u64,
    i: usize,
) -> Result<Option<(u64, u64)>, CheckError> {
    if i >= rs.len() {
        Ok(None)
    } else {
        match rec_target_of(pers, st, names, rs[i].1, &rs[i].0.ty) {
            Err(e) => Err(e),
            Ok(t) => {
                if t == m {
                    Ok(Some((rs[i].1, rs[i].2)))
                } else {
                    rec_for_member(pers, st, names, rs, m, i + 1)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:370-383 blockMemberCounts?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockMemberCounts?` —
/// **the members' index counts**, one `blockCounts?` per member (from member
/// `m`, the former `cv_ts[m]`), in order.
#[allow(clippy::too_many_arguments)]
pub fn block_member_counts(
    pers: &PersTier,
    st: &AState,
    n_pd: u64,
    k: u64,
    n_c: u64,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    m: u64,
    cv_ts: &Vec<IConstantVal>,
    out: Vec<u64>,
) -> Result<Option<Vec<u64>>, CheckError> {
    if m >= cv_ts.len() as u64 {
        Ok(Some(out))
    } else {
        match rec_for_member(pers, st, names, rs, m, 0) {
            Err(e) => Err(e),
            Ok(r) => match block_counts(pers, st, n_pd, k, n_c, rs.len() as u64, &cv_ts[m as usize], r) {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(c)) => {
                    let mut o: Vec<u64> = out;
                    o.push(c.1);
                    block_member_counts(pers, st, n_pd, k, n_c, names, rs, m + 1, cv_ts, o)
                }
            },
        }
    }
}

/// con-leche: none — `cvTs.map (·.name)`
/// Lean twin: the formers' names, in block order.
pub fn former_names(cvs: &Vec<IConstantVal>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= cvs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(cvs[i].name.dup2());
        former_names(cvs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: the reserved-name and level-parameter pins on the formers:
/// `cvTs.all fun c => reservedBasisNames.contains c.name == false` and
/// `cvTs.all fun c => c.levelParams == lps`, in one pass.
pub fn formers_pinned(reserved: &Vec<NIdx>, cvs: &Vec<IConstantVal>, lps: &Vec<NIdx>, i: usize) -> bool {
    if i >= cvs.len() {
        true
    } else if names_contain(reserved, &cvs[i].name, 0) || !core::nidx_vec_beq(&cvs[i].level_params, lps) {
        false
    } else {
        formers_pinned(reserved, cvs, lps, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `rs.all fun r => reservedBasisNames.contains r.1.name == false`.
pub fn recs_unreserved(reserved: &Vec<NIdx>, rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>, i: usize) -> bool {
    if i >= rs.len() {
        true
    } else if names_contain(reserved, &rs[i].0.name, 0) {
        false
    } else {
        recs_unreserved(reserved, rs, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `cs.all fun c => c.2.1 == nP && c.1.levelParams == lps &&
/// reservedBasisNames.contains c.1.name == false`.
pub fn ctors_pinned(
    reserved: &Vec<NIdx>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    n_p: u64,
    lps: &Vec<NIdx>,
    i: usize,
) -> bool {
    if i >= cs.len() {
        true
    } else if cs[i].1 == n_p
        && core::nidx_vec_beq(&cs[i].0.level_params, lps)
        && !names_contain(reserved, &cs[i].0.name, 0)
    {
        ctors_pinned(reserved, cs, n_p, lps, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `cs.map fun c => (c.1, c.2.2)`
/// Lean twin: the constructors with their field counts.
pub fn ctors_nf(cs: &Vec<(IConstantVal, u64, u64)>, i: usize, out: Vec<(IConstantVal, u64)>) -> Vec<(IConstantVal, u64)> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<(IConstantVal, u64)> = out;
        o.push((env::i_constant_val_dup(&cs[i].0), cs[i].2));
        ctors_nf(cs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `((cvTs.zip nIdxs).zip groups).map …` — the members, zipped to the
/// shortest of the three lists.
pub fn zip_members(
    cvs: &Vec<IConstantVal>,
    n_idxs: &Vec<u64>,
    groups: &Vec<Vec<(IConstantVal, u64)>>,
    i: usize,
    out: Vec<MemberShape>,
) -> Vec<MemberShape> {
    if i >= cvs.len() || i >= n_idxs.len() || i >= groups.len() {
        out
    } else {
        let mut o: Vec<MemberShape> = out;
        o.push(MemberShape {
            cv_t: env::i_constant_val_dup(&cvs[i]),
            n_idx: n_idxs[i],
            ctors: ctors_dup(&groups[i], 0, Vec::new()),
        });
        zip_members(cvs, n_idxs, groups, i + 1, o)
    }
}

/// con-leche: none — `rules.map RecRule.rhs`
/// Lean twin: the exported rules' right-hand sides.
pub fn rule_rhss(rules: &Vec<IRecRule>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= rules.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(rules[i].rhs.dup2());
        rule_rhss(rules, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `rs.map fun r => ⟨r.1, rP, mI, recTargetOf names mI r.1.type,
/// rules.map RecRule.rhs⟩` — **the recursors, in the stream's own order**, each
/// with the member its MAJOR names.
pub fn rec_shapes(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    i: usize,
    out: Vec<RecShape>,
) -> Result<Vec<RecShape>, CheckError> {
    if i >= rs.len() {
        Ok(out)
    } else {
        match rec_target_of(pers, st, names, rs[i].1, &rs[i].0.ty) {
            Err(e) => Err(e),
            Ok(tgt) => {
                let mut o: Vec<RecShape> = out;
                o.push(RecShape {
                    cv_r: env::i_constant_val_dup(&rs[i].0),
                    r_p: rs[i].2,
                    m_i: rs[i].1,
                    tgt,
                    rhss: rule_rhss(&rs[i].3, 0, Vec::new()),
                });
                rec_shapes(pers, st, names, rs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockShape?` — **the
/// block's shape**: split into formers, constructors and recursors (at least
/// one of each of the first and the last), the members' counts, the
/// reserved-name and level pins, and then the record.
pub fn block_shape(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    block: &Vec<IConstantInfo>,
) -> Result<Option<BlockShape>, CheckError> {
    match block_split(block, 0, Vec::new()) {
        None => Ok(None),
        Some((cv_ts, cs, rs)) => {
            if cv_ts.len() == 0 || rs.len() == 0 {
                Ok(None)
            } else {
                let names: Vec<NIdx> = former_names(&cv_ts, 0, Vec::new());
                let k: u64 = cv_ts.len() as u64;
                match block_member_counts(pers, st, n_pd, k, cs.len() as u64, &names, &rs, 0, &cv_ts, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(n_idxs)) => block_shape_at(pers, st, n_pd, &cv_ts, &cs, &rs, names, n_idxs),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockShape?` — the
/// pins, the result sort (member 0's, or the placeholder `0` the install's
/// whnf loop replaces), the groups, the recursors and which eliminator they
/// are.
#[allow(clippy::too_many_arguments)]
pub fn block_shape_at(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    cv_ts: &Vec<IConstantVal>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    names: Vec<NIdx>,
    n_idxs: Vec<u64>,
) -> Result<Option<BlockShape>, CheckError> {
    let lps: Vec<NIdx> = env::nidx_vec_dup(&cv_ts[0].level_params);
    let n_p: u64 = n_pd;
    match core::reserved_basis_names(st) {
        Err(e) => Err(e),
        Ok(reserved) => {
            if formers_pinned(&reserved, cv_ts, &lps, 0)
                && recs_unreserved(&reserved, rs, 0)
                && ctors_pinned(&reserved, cs, n_p, &lps, 0)
            {
                let n0: u64 = if n_idxs.len() == 0 { 0 } else { n_idxs[0] };
                match expr_ops::strip_pis(pers, st, n_p + n0, &cv_ts[0].ty) {
                    Err(e) => Err(e),
                    Ok(Some(q)) => match view(pers, st, &q.1) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Sort(s)) => {
                            block_shape_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, s)
                        }
                        Ok(_) => match core::zero_level(st) {
                            Err(e) => Err(e),
                            Ok(z) => block_shape_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, z),
                        },
                    },
                    Ok(None) => match core::zero_level(st) {
                        Err(e) => Err(e),
                        Ok(z) => block_shape_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, z),
                    },
                }
            } else {
                Ok(None)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockShape?` — at the
/// result sort `s`: `isProp`, the groups, the members, the recursors, and the
/// eliminator read off recursor 0's level parameters (a fresh one in front of
/// the block's is the LARGE eliminator).
#[allow(clippy::too_many_arguments)]
pub fn block_shape_sort(
    pers: &PersTier,
    st: &mut AState,
    cv_ts: &Vec<IConstantVal>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    rs: &Vec<(IConstantVal, u64, u64, Vec<IRecRule>)>,
    names: Vec<NIdx>,
    n_idxs: Vec<u64>,
    lps: Vec<NIdx>,
    n_p: u64,
    s: LIdx,
) -> Result<Option<BlockShape>, CheckError> {
    match core::zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match core::lvl_eq(pers, st, &s, &z) {
            Err(e) => Err(e),
            Ok(eq) => {
                let is_prop: bool = match eq {
                    Some(true) => true,
                    Some(false) => false,
                    None => false,
                };
                let ctors: Vec<(IConstantVal, u64)> = ctors_nf(cs, 0, Vec::new());
                match struct_parts::param_levels(pers, st, &lps) {
                    Err(e) => Err(e),
                    Ok(lvls) => {
                        let k: u64 = cv_ts.len() as u64;
                        match block_groups(pers, st, &names, &lvls, n_p, k, &ctors) {
                            Err(e) => Err(e),
                            Ok(groups) => {
                                let members: Vec<MemberShape> = zip_members(cv_ts, &n_idxs, &groups, 0, Vec::new());
                                match rec_shapes(pers, st, &names, rs, 0, Vec::new()) {
                                    Err(e) => Err(e),
                                    Ok(recs_l) => {
                                        let rl0: Vec<NIdx> = env::nidx_vec_dup(&rs[0].0.level_params);
                                        block_shape_elim(pers, st, members, recs_l, n_p, s, is_prop, &lps, &rl0)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:385-442 blockShape?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockShape?` —
/// WHICH ELIMINATOR the recursors are: `elim :: relps` with `relps == lps` and
/// `elim` fresh is the large one; anything else is the small one, at
/// `.anonymous` (interned).
#[allow(clippy::too_many_arguments)]
pub fn block_shape_elim(
    pers: &PersTier,
    st: &mut AState,
    members: Vec<MemberShape>,
    recs: Vec<RecShape>,
    n_p: u64,
    s: LIdx,
    is_prop: bool,
    lps: &Vec<NIdx>,
    rl0: &Vec<NIdx>,
) -> Result<Option<BlockShape>, CheckError> {
    let large: bool = if rl0.len() == 0 {
        false
    } else if nidx_vec_beq_off(rl0, 1, lps, 0) && !names_contain(lps, &rl0[0], 0) {
        true
    } else {
        false
    };
    if large {
        Ok(Some(BlockShape {
            members,
            recs,
            n_p,
            elim: rl0[0].dup2(),
            res_sort: s,
            large: true,
            is_prop,
        }))
    } else {
        match intern_n_node(pers, st, NNodeView::Anonymous) {
            Err(e) => Err(e),
            Ok(anon) => Ok(Some(BlockShape {
                members,
                recs,
                n_p,
                elim: anon,
                res_sort: s,
                large: false,
                is_prop,
            })),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockParts.lean:444-449 blockParts?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockParts.lean blockParts?` —
/// recognise a block for the uniform route, at any number of members: its
/// SHAPE.
pub fn block_parts(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    block: &Vec<IConstantInfo>,
) -> Result<Option<BlockParts>, CheckError> {
    match block_shape(pers, st, n_pd, block) {
        Err(e) => Err(e),
        Ok(None) => Ok(None),
        Ok(Some(p)) => Ok(Some(BlockParts { shape: p })),
    }
}
