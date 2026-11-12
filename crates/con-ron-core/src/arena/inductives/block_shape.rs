//! `arena::inductives::block_shape` — the k-ary block: the record and the
//! reader.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockShape.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockShape.lean` over handles: the record a
//! block is read into (`MemberShape`, `RecShape`, `BlockShape`), its
//! projections, and the reader (`blockSplit`, `recTargetOf`, `blockCounts`,
//! `blockGroups`, `readBlock`) with the recursor records' name and level pins
//! the recursor stage throws on.  A block the reader cannot read is an
//! invalid input: the reader's value is the cited `Except`, the inner
//! `Result` of `Result<Result<BlockShape, CheckError>, CheckError>` (the outer
//! one is the arena's own failure, a dangling handle or exhausted fuel).
//!
//! ## The twin's deviations
//!
//! * **The level lists are compared as interned lists**: `lps.map .param` is
//!   `struct_parts::param_levels`, and `us == lvls` is handle equality.
//! * **A projection that reads a term takes the state** (`withSort`'s
//!   `Level.isEquiv`, `recTargetOf`'s telescope).
//! * **`BlockShape.recTgtAt` is not ported**: nothing the executed checker
//!   runs reads it (the model does); the skip list says so.
//! * **The `…all`/`…any`/`find?`/`filter`/`map` closures are index
//!   recursions** (§3.4); a `find?` whose hit only names the error is an
//!   `all` scan.
//! * **The error messages drop con-leche's interpolated names and counts**
//!   (§3.1), and with them the recursor name `blockCounts`' `r` carries.

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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:53-70 MemberShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:41-55 MemberShape` — one
/// member of a block: its type former at its telescope (what the block's
/// check reads, `reduceMember`), its type former as the stream declares it
/// (what is installed), its own index count and its constructors
/// (member-local, in block order, each with its field count).
pub struct MemberShape {
    pub cv_t: IConstantVal,
    pub declared: IConstantVal,
    pub n_idx: u64,
    pub ctors: Vec<(IConstantVal, u64)>,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:53-70 MemberShape
/// The record copy.
pub fn member_shape_dup(m: &MemberShape) -> MemberShape {
    MemberShape {
        cv_t: env::i_constant_val_dup(&m.cv_t),
        declared: env::i_constant_val_dup(&m.declared),
        n_idx: m.n_idx,
        ctors: ctors_dup(&m.ctors, 0, Vec::new()),
    }
}

/// con-leche: none — a `List (ConstantVal × Nat)` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:41-55 MemberShape`.
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:72-102 RecShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:57-77 RecShape` — **one
/// recursor of a block, as the stream carries it**: its constant, the
/// record's own rule prefix `rP` and major index `mI`, the member its MAJOR
/// names (`k`: none — a nested block's auxiliary recursor), and its rules as
/// exported (constructor, field count, right-hand side; the install-computed
/// fields at their parse placeholders): what the install stores, the checks
/// having compared them with the generated ones (`streamRecsCheck`), and the
/// record's K flag (official's `is_k`): what is installed, the job checking it
/// (`streamRecCheck`).
pub struct RecShape {
    pub cv_r: IConstantVal,
    pub r_p: u64,
    pub m_i: u64,
    pub tgt: u64,
    pub rules: Vec<IRecRule>,
    pub is_k: bool,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:72-102 RecShape
/// The record copy.
pub fn rec_shape_dup(r: &RecShape) -> RecShape {
    RecShape {
        cv_r: env::i_constant_val_dup(&r.cv_r),
        r_p: r.r_p,
        m_i: r.m_i,
        tgt: r.tgt,
        rules: env::i_rec_rules_dup(&r.rules),
        is_k: r.is_k,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:104-108 MemberShape.structCtor?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:79-84 MemberShape.structCtor?` — a
/// structure-like member's constructor: its only one, at no index.
pub fn member_struct_ctor(ms: &MemberShape) -> Option<(IConstantVal, u64)> {
    if ms.ctors.len() == 1 && ms.n_idx == 0 {
        Some((env::i_constant_val_dup(&ms.ctors[0].0), ms.ctors[0].1))
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:110-133 BlockShape
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:86-106 BlockShape` — the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:110-133 BlockShape
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:135-136 BlockShape.formers
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:108-110 BlockShape.formers` — the
/// members' formers from `i` on, at the telescopes the check reads, in block
/// order.
pub fn shape_formers(ms: &Vec<MemberShape>, i: usize, out: Vec<IConstantVal>) -> Vec<IConstantVal> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<IConstantVal> = out;
        o.push(env::i_constant_val_dup(&ms[i].cv_t));
        shape_formers(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:138-140 BlockShape.memberCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:112-115 BlockShape.memberCtors` —
/// the members' constructors from `i` on, per member, as declared.
pub fn member_ctors(
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<Vec<(IConstantVal, u64)>>,
) -> Vec<Vec<(IConstantVal, u64)>> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<Vec<(IConstantVal, u64)>> = out;
        o.push(ctors_dup(&ms[i].ctors, 0, Vec::new()));
        member_ctors(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:142-145 BlockShape.ctorGroups
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean BlockShape.ctorGroups` — the
/// members' constructors from `i` on, grouped by member, each group under its
/// member's name: what the install conses, the name becoming each
/// constructor's `induct`.
pub fn ctor_groups(
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<(NIdx, Vec<(IConstantVal, u64)>)>,
) -> Vec<(NIdx, Vec<(IConstantVal, u64)>)> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<(NIdx, Vec<(IConstantVal, u64)>)> = out;
        o.push((ms[i].cv_t.name.dup2(), ctors_dup(&ms[i].ctors, 0, Vec::new())));
        ctor_groups(ms, i + 1, o)
    }
}

/// con-leche: none — a `List MemberShape` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:86-106 BlockShape`.
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
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:86-106 BlockShape`.
pub fn recs_dup(rs: &Vec<RecShape>, i: usize, out: Vec<RecShape>) -> Vec<RecShape> {
    if i >= rs.len() {
        out
    } else {
        let mut o: Vec<RecShape> = out;
        o.push(rec_shape_dup(&rs[i]));
        recs_dup(rs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:147-151 numCtorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:117-121 numCtorsOf` — the
/// constructors of a list of members (`ms[i..]`), counted.
pub fn num_ctors_of(ms: &Vec<MemberShape>, i: usize) -> u64 {
    if i >= ms.len() {
        0
    } else {
        (ms[i].ctors.len() as u64) + num_ctors_of(ms, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:155-156 BlockShape.k
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:123-125 BlockShape.k` — the
/// number of members.
pub fn shape_k(p: &BlockShape) -> u64 {
    p.members.len() as u64
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:157-158 BlockShape.numCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:127-129 BlockShape.numCtors`
/// — the number of constructors of the whole block.
pub fn shape_num_ctors(p: &BlockShape) -> u64 {
    num_ctors_of(&p.members, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:159-160 BlockShape.memberNames
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:131-133 BlockShape.memberNames`
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:159-160 BlockShape.memberNames
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:131-133 BlockShape.memberNames`.
pub fn shape_member_names(p: &BlockShape) -> Vec<NIdx> {
    member_names(&p.members, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:161-162 BlockShape.nIdxs
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:135-137 BlockShape.nIdxs` —
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:163-166 BlockShape.lps
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:139-144 BlockShape.lps` — the
/// block's level parameters (member 0's; `[]` at no member).
pub fn shape_lps(p: &BlockShape) -> Vec<NIdx> {
    if p.members.len() == 0 {
        Vec::new()
    } else {
        env::nidx_vec_dup(&p.members[0].cv_t.level_params)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:167-169 BlockShape.allCtors
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:146-149 BlockShape.allCtors`
/// — the constructors of the whole block, in block order.
pub fn all_ctors(ms: &Vec<MemberShape>, i: usize, out: Vec<(IConstantVal, u64)>) -> Vec<(IConstantVal, u64)> {
    if i >= ms.len() {
        out
    } else {
        let o: Vec<(IConstantVal, u64)> = ctors_dup(&ms[i].ctors, 0, out);
        all_ctors(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:176-182 BlockShape.rulePrefixAt
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:151-157 BlockShape.rulePrefixAt`
/// — recursor `r`'s rule prefix, the RECORD's (`0`, the default record's, off
/// the list).
pub fn rule_prefix_at(p: &BlockShape, r: u64) -> u64 {
    if r < p.recs.len() as u64 {
        p.recs[r as usize].r_p
    } else {
        0
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:184-187 BlockShape.majorIdxAt
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:159-164 BlockShape.majorIdxAt`
/// — recursor `r`'s major-premise index, the RECORD's.
pub fn major_idx_at(p: &BlockShape, r: u64) -> u64 {
    if r < p.recs.len() as u64 {
        p.recs[r as usize].m_i
    } else {
        0
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:189-193 BlockShape.withSort
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:166-176 BlockShape.withSort` —
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

// ---------------------------------------------------------------------------
// Recognition
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:226-232 blockSplitRecs
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:180-189 blockSplitRecs` — the
/// closing recursors from `i` on: `none` at anything else.
pub fn block_split_recs(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
) -> Option<Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>> {
    if i >= block.len() {
        Some(out)
    } else {
        match &block[i] {
            IConstantInfo::RecInfo(cv, m_i, r_p, is_k, rules) => {
                let mut o: Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)> = out;
                o.push((env::i_constant_val_dup(cv), *m_i, *r_p, *is_k, env::i_rec_rules_dup(rules)));
                block_split_recs(block, i + 1, o)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:234-239 blockSplitCtors
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_shape::block_split_ctors_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:191-203 blockSplitCtors` —
/// the constructors from `i` on, then the recursors.
#[allow(clippy::type_complexity)]
pub fn block_split_ctors(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<(IConstantVal, u64, u64)>,
) -> Option<(Vec<(IConstantVal, u64, u64)>, Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>)> {
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:234-239 blockSplitCtors
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_shape::is_ctor_info_refines, then delete this line
/// Lean twin: the cited `.ctorInfo … :: rest` pattern's test, its own function
/// so the element's loan ends before the recursion (extraction rule 1).
pub fn is_ctor_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::CtorInfo(_, _, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:234-239 blockSplitCtors
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_shape::ctor_info_parts_refines, then delete this line
/// Lean twin: the `.ctorInfo cvC nP nF` pattern's fields, copied out.  Reached
/// only past `is_ctor_info`; the other arm is the default the total function
/// needs.
pub fn ctor_info_parts(ci: &IConstantInfo) -> (IConstantVal, u64, u64) {
    match ci {
        IConstantInfo::CtorInfo(cv, n_p, n_f, _) => (env::i_constant_val_dup(cv), *n_p, *n_f),
        _ => (env::i_constant_info_dummy_val(), 0, 0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:241-247 blockSplit
/// Lean twin: the `.indInfo cvT _` pattern's test.
pub fn is_ind_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::IndInfo(_, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:241-247 blockSplit
/// Lean twin: the `.indInfo cvT _` pattern's constant, copied out.
pub fn ind_info_val(ci: &IConstantInfo) -> IConstantVal {
    match ci {
        IConstantInfo::IndInfo(cv, _) => env::i_constant_val_dup(cv),
        _ => env::i_constant_info_dummy_val(),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:241-247 blockSplit
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:205-217 blockSplit` — the
/// type formers from `i` on, the constructors and the recursors.
#[allow(clippy::type_complexity)]
pub fn block_split(
    block: &Vec<IConstantInfo>,
    i: usize,
    out: Vec<IConstantVal>,
) -> Option<(
    Vec<IConstantVal>,
    Vec<(IConstantVal, u64, u64)>,
    Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:249-266 recTargetOf
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:219-241 recTargetOf` — **the
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
                    Some((dom, _)) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, &dom) {
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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive type declares more parameters than its type has binders`, as code points.
pub const M_PARAMS_EXCEED: [u32; 65] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 100, 101, 99, 108, 97,
    114, 101, 115, 32, 109, 111, 114, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32,
    116, 104, 97, 110, 32, 105, 116, 115, 32, 116, 121, 112, 101, 32, 104, 97, 115, 32, 98, 105,
    110, 100, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `no recursor of the block eliminates the inductive type`, as code points.
pub const M_NO_REC_ELIM: [u32; 54] = [
    110, 111, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 111, 102, 32, 116, 104, 101, 32, 98,
    108, 111, 99, 107, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 115, 32, 116, 104, 101, 32,
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the argument counts of a recursor do not fit the block`, as code points.
pub const M_REC_COUNTS: [u32; 54] = [
    116, 104, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 99, 111, 117, 110, 116, 115, 32,
    111, 102, 32, 97, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 100, 111, 32, 110, 111, 116,
    32, 102, 105, 116, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107,
];

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:268-303 blockCounts
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:249-272 blockCounts` — **one
/// member's parameter and index counts**, read as official reads them: off
/// the member's own telescope when it is a syntactic one ending in a sort,
/// else off the argument sums of a recursor whose major names the member.  A
/// member that cannot be counted is an invalid input, with the reason (the
/// inner `Result`, the cited `Except`).
///
/// Deviation: the cited `r` carries the recursor's name for the error text;
/// the port drops the interpolation (§3.1), so `r` is the two counts.
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
) -> Result<Result<(u64, u64), CheckError>, CheckError> {
    match pi_binders(pers, st, CORE_WALK_FUEL, &cv_t.ty, Vec::new()) {
        Err(e) => Err(e),
        Ok((bs, res)) => match view(pers, st, &res) {
            Err(e) => Err(e),
            Ok(ENodeView::Sort(_)) => {
                let n: u64 = bs.len() as u64;
                if n_pd <= n {
                    Ok(Ok((n_pd, n - n_pd)))
                } else {
                    Ok(Err(CheckError::Invalid(code_points(&M_PARAMS_EXCEED))))
                }
            }
            Ok(_) => Ok(block_counts_rec(n_pd, k, n_c, n_r, r)),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:268-303 blockCounts
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:249-272 blockCounts` — the
/// def-headed former's arm: the counts off the recursor's sums, or the reason
/// they cannot be read.
pub fn block_counts_rec(n_pd: u64, k: u64, n_c: u64, n_r: u64, r: Option<(u64, u64)>) -> Result<(u64, u64), CheckError> {
    match r {
        None => Err(CheckError::Invalid(code_points(&M_NO_REC_ELIM))),
        Some((m_i, r_p)) => {
            if r_p < n_c + k || m_i < r_p {
                Err(rec_counts_error())
            } else if sub_nat(r_p, n_c + k) == n_pd {
                Ok((n_pd, sub_nat(m_i, r_p)))
            } else if k < n_r && n_pd + n_r + n_c <= r_p {
                Ok((n_pd, sub_nat(m_i, r_p)))
            } else {
                Err(rec_counts_error())
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:268-303 blockCounts.recCountsError
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:243-247 recCountsError` — a recursor whose argument counts do
/// not fit the block (the cited names and counts dropped, §3.1).
pub fn rec_counts_error() -> CheckError {
    CheckError::Invalid(code_points(&M_REC_COUNTS))
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:305-312 ctorMember?
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:274-283 ctorMember?` — the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:314-327 blockGroups
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:314-327 blockGroups
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:314-327 blockGroups
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:285-299 blockGroups` — **the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:329-337 blockRecLpsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:301-309 blockRecLpsOk` — the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:329-337 blockRecLpsOk
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:329-337 blockRecLpsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:301-309 blockRecLpsOk` —
/// **the recursor records' level-parameter pin**.
pub fn block_rec_lps_ok(p: &BlockShape) -> bool {
    let lps: Vec<NIdx> = shape_lps(p);
    block_rec_lps_ok_from(p, &lps, 0)
}

/// con-leche: none — the recursor-name suffix `rec`, as code points
/// Lean twin: `"rec"`.
pub const REC_SUFFIX: [u32; 3] = [114, 101, 99];

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:339-361 blockRecNameSetOk
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:339-361 blockRecNameSetOk
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:311-319 blockRecNameSetOk` —
/// **the recursor names, as a SET**: exactly `T_m.rec` at every member, each
/// once.  Takes the members and the recursors apart, so that the caller's
/// `{ p with recs := own }` is an argument, not a record copy.
pub fn block_rec_name_set_ok(
    pers: &PersTier,
    st: &mut AState,
    members: &Vec<MemberShape>,
    recs: &Vec<RecShape>,
) -> Result<bool, CheckError> {
    match want_rec_names(pers, st, members, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(want) => {
            let got: Vec<NIdx> = rec_names(recs, 0, Vec::new());
            Ok(got.len() == want.len() && names_all_in(&want, &got, 0) && names_all_in(&got, &want, 0))
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:363-372 blockRecNamesUnreserved
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:321-329 blockRecNamesUnreserved`
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:374-388 blockMemberCounts
/// Lean twin: `rs.find? fun q => recTargetOf names q.2.1 q.1.type == m` — the
/// first recursor whose major names member `m`, its `(mI, rP)`.
pub fn rec_for_member(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:374-388 blockMemberCounts
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:331-350 blockMemberCounts` —
/// **the members' index counts**, one `blockCounts` per member (from member
/// `m`, the former `cv_ts[m]`), in order; the first member that cannot be
/// counted gives the error.
#[allow(clippy::too_many_arguments)]
pub fn block_member_counts(
    pers: &PersTier,
    st: &AState,
    n_pd: u64,
    k: u64,
    n_c: u64,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
    m: u64,
    cv_ts: &Vec<IConstantVal>,
    out: Vec<u64>,
) -> Result<Result<Vec<u64>, CheckError>, CheckError> {
    if m >= cv_ts.len() as u64 {
        Ok(Ok(out))
    } else {
        match rec_for_member(pers, st, names, rs, m, 0) {
            Err(e) => Err(e),
            Ok(r) => match block_counts(pers, st, n_pd, k, n_c, rs.len() as u64, &cv_ts[m as usize], r) {
                Err(e) => Err(e),
                Ok(Err(e)) => Ok(Err(e)),
                Ok(Ok(c)) => {
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `cvTs.all fun c => c.levelParams == lps` — no type former
/// declares other universe parameters than member 0 (the cited
/// `cvTs.find? (fun c => c.levelParams != lps)` misses).
pub fn formers_lps_ok(cvs: &Vec<IConstantVal>, lps: &Vec<NIdx>, i: usize) -> bool {
    if i >= cvs.len() {
        true
    } else if !core::nidx_vec_beq(&cvs[i].level_params, lps) {
        false
    } else {
        formers_lps_ok(cvs, lps, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `cs.all fun c => c.2.1 == nP` — every constructor declares the
/// block's parameter count (the cited `cs.find? (fun c => c.2.1 != nP)`
/// misses).
pub fn ctors_params_ok(cs: &Vec<(IConstantVal, u64, u64)>, n_p: u64, i: usize) -> bool {
    if i >= cs.len() {
        true
    } else if cs[i].1 != n_p {
        false
    } else {
        ctors_params_ok(cs, n_p, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `cs.all fun c => c.1.levelParams == lps` — every constructor
/// declares the block's universe parameters (the cited
/// `cs.find? (fun c => c.1.levelParams != lps)` misses).
pub fn ctors_lps_ok(cs: &Vec<(IConstantVal, u64, u64)>, lps: &Vec<NIdx>, i: usize) -> bool {
    if i >= cs.len() {
        true
    } else if !core::nidx_vec_beq(&cs[i].0.level_params, lps) {
        false
    } else {
        ctors_lps_ok(cs, lps, i + 1)
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
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
            declared: env::i_constant_val_dup(&cvs[i]),
            n_idx: n_idxs[i],
            ctors: ctors_dup(&groups[i], 0, Vec::new()),
        });
        zip_members(cvs, n_idxs, groups, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `rs.map fun r => ⟨r.1, rP, mI, recTargetOf names mI r.1.type,
/// rules⟩` — **the recursors, in the stream's own order**, each
/// with the member its MAJOR names.
pub fn rec_shapes(
    pers: &PersTier,
    st: &AState,
    names: &Vec<NIdx>,
    rs: &Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
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
                    rules: env::i_rec_rules_dup(&rs[i].4),
                    is_k: rs[i].3,
                });
                rec_shapes(pers, st, names, rs, i + 1, o)
            }
        }
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block: its records are not the inductive types, then the constructors, then the recursors`, as code points.
pub const M_ORDER: [u32; 99] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 58, 32, 105, 116, 115,
    32, 114, 101, 99, 111, 114, 100, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101,
    32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115, 44, 32, 116, 104,
    101, 110, 32, 116, 104, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 44,
    32, 116, 104, 101, 110, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block declares no inductive type`, as code points.
pub const M_NO_TYPE: [u32; 42] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 100, 101, 99, 108,
    97, 114, 101, 115, 32, 110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121,
    112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive block carries no recursor records; the input must carry the recursors of every inductive block`, as code points.
pub const M_NO_RECS: [u32; 104] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 32, 99, 97, 114, 114,
    105, 101, 115, 32, 110, 111, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 101, 99, 111,
    114, 100, 115, 59, 32, 116, 104, 101, 32, 105, 110, 112, 117, 116, 32, 109, 117, 115, 116, 32,
    99, 97, 114, 114, 121, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 32,
    111, 102, 32, 101, 118, 101, 114, 121, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98,
    108, 111, 99, 107,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `inductive type declares other universe parameters than the block's first type`, as code points.
pub const M_TYPE_LEVELS: [u32; 77] = [
    105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 32, 100, 101, 99, 108, 97,
    114, 101, 115, 32, 111, 116, 104, 101, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 98,
    108, 111, 99, 107, 39, 115, 32, 102, 105, 114, 115, 116, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `constructor declares another parameter count than the block`, as code points.
pub const M_CTOR_PARAMS: [u32; 59] = [
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 100, 101, 99, 108, 97, 114, 101, 115,
    32, 97, 110, 111, 116, 104, 101, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 99,
    111, 117, 110, 116, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `constructor declares other universe parameters than its type`, as code points.
pub const M_CTOR_LEVELS_ONE: [u32; 60] = [
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 100, 101, 99, 108, 97, 114, 101, 115,
    32, 111, 116, 104, 101, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97,
    109, 101, 116, 101, 114, 115, 32, 116, 104, 97, 110, 32, 105, 116, 115, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `constructor declares other universe parameters than the block's inductive types`, as code points.
pub const M_CTOR_LEVELS: [u32; 79] = [
    99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 100, 101, 99, 108, 97, 114, 101, 115,
    32, 111, 116, 104, 101, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97,
    109, 101, 116, 101, 114, 115, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 98, 108, 111, 99,
    107, 39, 115, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115,
];

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:352-422 readBlock` — **read a
/// declared inductive block**: split into formers, constructors and recursors
/// (at least one of each of the first and the last), the members' counts, the
/// universe and parameter declarations, and then the record.  A block that
/// cannot be read is an invalid input, and the inner `Result` (the cited
/// `Except`) says why; the outer one is the arena's own failure.  The messages
/// drop con-leche's interpolated names and counts (§3.1).
pub fn read_block(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    block: &Vec<IConstantInfo>,
) -> Result<Result<BlockShape, CheckError>, CheckError> {
    match block_split(block, 0, Vec::new()) {
        None => Ok(Err(CheckError::Invalid(code_points(&M_ORDER)))),
        Some((cv_ts, cs, rs)) => {
            if cv_ts.len() == 0 {
                Ok(Err(CheckError::Invalid(code_points(&M_NO_TYPE))))
            } else if rs.len() == 0 {
                Ok(Err(CheckError::Invalid(code_points(&M_NO_RECS))))
            } else {
                let names: Vec<NIdx> = former_names(&cv_ts, 0, Vec::new());
                let k: u64 = cv_ts.len() as u64;
                match block_member_counts(pers, st, n_pd, k, cs.len() as u64, &names, &rs, 0, &cv_ts, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(Err(e)) => Ok(Err(e)),
                    Ok(Ok(n_idxs)) => read_block_at(pers, st, n_pd, &cv_ts, &cs, &rs, names, n_idxs),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:352-422 readBlock` — the
/// universe and parameter declarations' three tests (formers' universe
/// parameters, constructors' parameter counts, constructors' universe
/// parameters, each the first failure's reason), then the result sort
/// (member 0's, or the placeholder `0` the check's whnf loop replaces).
#[allow(clippy::too_many_arguments)]
pub fn read_block_at(
    pers: &PersTier,
    st: &mut AState,
    n_pd: u64,
    cv_ts: &Vec<IConstantVal>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    rs: &Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
    names: Vec<NIdx>,
    n_idxs: Vec<u64>,
) -> Result<Result<BlockShape, CheckError>, CheckError> {
    let lps: Vec<NIdx> = env::nidx_vec_dup(&cv_ts[0].level_params);
    let n_p: u64 = n_pd;
    if !formers_lps_ok(cv_ts, &lps, 0) {
        Ok(Err(CheckError::Invalid(code_points(&M_TYPE_LEVELS))))
    } else if !ctors_params_ok(cs, n_p, 0) {
        Ok(Err(CheckError::Invalid(code_points(&M_CTOR_PARAMS))))
    } else if !ctors_lps_ok(cs, &lps, 0) {
        if cv_ts.len() == 1 {
            Ok(Err(CheckError::Invalid(code_points(&M_CTOR_LEVELS_ONE))))
        } else {
            Ok(Err(CheckError::Invalid(code_points(&M_CTOR_LEVELS))))
        }
    } else {
        let n0: u64 = if n_idxs.len() == 0 { 0 } else { n_idxs[0] };
        match expr_ops::strip_pis(pers, st, n_p + n0, &cv_ts[0].ty) {
            Err(e) => Err(e),
            Ok(Some(q)) => match view(pers, st, &q.1) {
                Err(e) => Err(e),
                Ok(ENodeView::Sort(s)) => read_block_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, s),
                Ok(_) => match core::zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => read_block_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, z),
                },
            },
            Ok(None) => match core::zero_level(st) {
                Err(e) => Err(e),
                Ok(z) => read_block_sort(pers, st, cv_ts, cs, rs, names, n_idxs, lps, n_p, z),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:352-422 readBlock` — at the
/// result sort `s`: `isProp`, the groups, the members, the recursors, and the
/// eliminator read off recursor 0's level parameters (a fresh one in front of
/// the block's is the LARGE eliminator).
#[allow(clippy::too_many_arguments)]
pub fn read_block_sort(
    pers: &PersTier,
    st: &mut AState,
    cv_ts: &Vec<IConstantVal>,
    cs: &Vec<(IConstantVal, u64, u64)>,
    rs: &Vec<(IConstantVal, u64, u64, bool, Vec<IRecRule>)>,
    names: Vec<NIdx>,
    n_idxs: Vec<u64>,
    lps: Vec<NIdx>,
    n_p: u64,
    s: LIdx,
) -> Result<Result<BlockShape, CheckError>, CheckError> {
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
                                        read_block_elim(pers, st, members, recs_l, n_p, s, is_prop, &lps, &rl0)
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

/// con-leche: ConLeche/Kernel/Inductives/BlockShape.lean:390-463 readBlock
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockShape.lean:352-422 readBlock` —
/// WHICH ELIMINATOR the recursors are: `elim :: relps` with `relps == lps` and
/// `elim` fresh is the large one; anything else is the small one, at
/// `.anonymous` (interned).
#[allow(clippy::too_many_arguments)]
pub fn read_block_elim(
    pers: &PersTier,
    st: &mut AState,
    members: Vec<MemberShape>,
    recs: Vec<RecShape>,
    n_p: u64,
    s: LIdx,
    is_prop: bool,
    lps: &Vec<NIdx>,
    rl0: &Vec<NIdx>,
) -> Result<Result<BlockShape, CheckError>, CheckError> {
    let large: bool = if rl0.len() == 0 {
        false
    } else if nidx_vec_beq_off(rl0, 1, lps, 0) && !names_contain(lps, &rl0[0], 0) {
        true
    } else {
        false
    };
    if large {
        Ok(Ok(BlockShape {
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
            Ok(anon) => Ok(Ok(BlockShape {
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
