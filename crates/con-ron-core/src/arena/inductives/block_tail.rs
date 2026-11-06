//! `arena::inductives::block_tail` — the uniform install's pass and tail.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockTail.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockTail.lean` over handles — `checkBlock`,
//! the uniform route's entry — at the executed tier's discipline:
//! `ConLeche/Cached/CheckerC.lean`'s `checkBlockKS`/`checkBlockPassS`/
//! `checkBlockTailS`, whose flushes at the environment transitions are the
//! arena's (task #97g item 4; the arena has one core, the cached one).
//!
//! ## The twin's deviations
//!
//! * **`BlockPass` is not generic** in the environment representation:
//!   con-leche parameterises it because it has two (`Env` and `FEnv`); the
//!   arena has one.
//! * **The index is threaded by value**, and the recursor stage hands it
//!   back (`arena::inductives::gen_rec`'s module note); the recursors' cons
//!   reads the constructors' environment at its visibility bound while it
//!   pushes above it (`blockRecInfosTF`'s fixed `find?`/`resolves`).
//! * **`checkBlockTablesF`'s walkers are the arena's** (`struct_install`'s
//!   `check_struct_proj_table`, the one table install).
//! * **The generated install is pushed in place and popped**
//!   (`cons_block_recs_temp`, `gen_rec::class_fe_r_pop`), where con-leche's
//!   cached driver reads an overlay on the constructors' index
//!   (`FEnv.overlay`): the same read-only environment, a flush entering and
//!   leaving it, and no copy of the index.

use super::block_install;
use super::block_parts;
use super::block_parts::{complete, shape_member_names, BlockParts, BlockShape};
use super::class_read::ClassRead;
use super::gen_rec;
use super::positivity::{nest_seeds, NestCtorNf, NestFieldKind};
use super::rec_check;
use super::rec_check::TargetMajor;
use super::stored_recs;
use super::struct_install;
use super::struct_parts;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{fail, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::ron::hashmap::Dup;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: duplicate constructor`, as code points.
pub const M_DUP_CTOR: [u32; 33] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 100, 117, 112, 108, 105, 99, 97, 116,
    101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
];

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:24-42 BlockPass
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::BlockPass_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:44-61 BlockPass` — **what one
/// pass over the formers, the constructors and the classes yields**: the
/// environment holding all k formers, the checked formers, the completed
/// record, the checked constructors and their fields' sorts per member,
/// the positivity function's kinds and normal forms, the canonical
/// parameters, the pre-pass's reading, the classes, and the positivity
/// check's table.
pub struct BlockPass {
    pub env1: IFEnv,
    pub cv_tas: Vec<IConstantVal>,
    pub p: BlockParts,
    pub ctors_as: Vec<Vec<(IConstantVal, u64)>>,
    pub sortsss: Vec<Vec<Vec<LIdx>>>,
    pub kinds: Vec<Vec<Vec<NestFieldKind>>>,
    pub nfs: Vec<Vec<EIdx>>,
    pub params: Vec<EIdx>,
    pub rd: ClassRead,
    pub cls: Vec<TargetMajor>,
    pub tbl: Vec<NestCtorNf>,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_pass_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:127-141 checkBlockPassS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_pass_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:63-84 checkBlockPass` — **one
/// pass over the formers, the constructors and the classes** at the block's
/// `is_rec` verdict: the formers (and the flush entering the environment
/// that holds them all), the constructors, the classes, and the positivity
/// check as ONE walk — the members' root frame, then every outside class.
pub fn check_block_pass(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p0: &BlockParts,
    is_rec: bool,
) -> Result<BlockPass, CheckError> {
    match block_install::check_block_inds(pers, st, mode, fe, p0, is_rec) {
        Err(e) => Err(e),
        Ok((fe1, cv_tas, p1)) => {
            let pc: BlockParts = complete(p0, p1);
            core::flush_caches(st);
            match block_install::check_block_ctors(pers, st, mode, &fe1, &fe1, &pc.shape, &cv_tas, 0, Vec::new(), Vec::new()) {
                Err(e) => Err(e),
                Ok((ctors_as, sortsss)) => check_block_pass_classes(pers, st, mode, fe1, cv_tas, pc, ctors_as, sortsss),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_pass_classes_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:127-141 checkBlockPassS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_pass_classes_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:63-84 checkBlockPass` — the
/// walk's context, the classes, the root frame and the seeds.
#[allow(clippy::too_many_arguments)]
pub fn check_block_pass_classes(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe1: IFEnv,
    cv_tas: Vec<IConstantVal>,
    pc: BlockParts,
    ctors_as: Vec<Vec<(IConstantVal, u64)>>,
    sortsss: Vec<Vec<Vec<LIdx>>>,
) -> Result<BlockPass, CheckError> {
    match block_install::block_nest_ctx(pers, st, &fe1, &pc.shape, &cv_tas) {
        Err(e) => Err(e),
        Ok((ctx, holes)) => match gen_rec::check_block_classes(pers, st, mode, &fe1, &pc.shape, &ctx.params, &ctors_as) {
            Err(e) => Err(e),
            Ok((rd, ms)) => match block_install::check_block_positivity(pers, st, mode, &fe1, &pc, &cv_tas, &ctors_as) {
                Err(e) => Err(e),
                Ok((kinds, nfs, pos)) => match gen_rec::class_seeds(pers, st, &ctx, &holes, &ms, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(seeds) => match nest_seeds(pers, st, mode, &fe1, &ctx, &seeds, 0, pos) {
                        Err(e) => Err(e),
                        Ok(ns) => {
                            let params: Vec<EIdx> = crate::arena::env::eidx_vec_dup(&ctx.params);
                            Ok(BlockPass {
                                env1: fe1,
                                cv_tas,
                                p: pc,
                                ctors_as,
                                sortsss,
                                kinds,
                                nfs,
                                params,
                                rd,
                                cls: ms,
                                tbl: ns.ctor_nfs,
                            })
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:64-78 checkBlockRec
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_rec_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:86-94 checkBlockRec` — **the
/// recursor stage on the uniform route**: the GENERATED recursor stage at the
/// constructors' environment, on the stream's own recursor family (the raw
/// `block`), the pass's classes and table, and the container bit.
#[allow(clippy::too_many_arguments)]
pub fn check_block_rec(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockParts,
    nested: bool,
    params: &Vec<EIdx>,
    tbl: &Vec<NestCtorNf>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    block: &Vec<IConstantInfo>,
    cv_tas: &Vec<IConstantVal>,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    gen_rec::gen_rec_check(pers, st, mode, fe, &p.shape, nested, params, tbl, rd, ms, cv_tas, block)
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-101 checkBlockTables
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tables_refines, then delete this line
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:152-160 checkBlockTablesF
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tables_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:96-114 checkBlockTables` — **the
/// projection table at every STRUCTURE-LIKE member** (one constructor, no
/// index) from member `i` on: the member's table; nothing at any other
/// member.
pub fn check_block_tables(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    ctors_as: &Vec<Vec<(IConstantVal, u64)>>,
    sortsss: &Vec<Vec<Vec<LIdx>>>,
    i: usize,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    if i >= p.members.len() || i >= ctors_as.len() || i >= sortsss.len() {
        Ok(fe)
    } else if ctors_as[i].len() == 1 && sortsss[i].len() == 1 && p.members[i].n_idx == 0 {
        let c_a: IConstantVal = crate::arena::env::i_constant_val_dup(&ctors_as[i][0].0);
        let n_f: u64 = ctors_as[i][0].1;
        match struct_parts::struct_proj_guards(pers, st, &c_a.ty, p.n_p, n_f, &sortsss[i][0]) {
            Err(e) => Err(e),
            Ok(guards) => {
                let lps: Vec<NIdx> = block_parts::shape_lps(p);
                match struct_install::check_struct_proj_table(
                    pers,
                    st,
                    &p.members[i].cv_t.name,
                    &c_a.name,
                    &lps,
                    p.n_p,
                    n_f,
                    &p.res_sort,
                    guards,
                    &c_a,
                    fe,
                ) {
                    Err(e) => Err(e),
                    Ok(fe2) => check_block_tables(pers, st, p, ctors_as, sortsss, i + 1, fe2),
                }
            }
        }
    } else {
        check_block_tables(pers, st, p, ctors_as, sortsss, i + 1, fe)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:80-91 consBlockRecsT
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::cons_block_recs_temp_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:143-163 checkBlockTailS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::cons_block_recs_temp_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:116-133 consBlockRecsTemp` — **the
/// generated install, pushed TEMPORARILY**: each generated recursor from `m` on
/// with its rules at its major (the lookups at the constructors' bound `vis2`).
/// Returns the rows the pushes displaced, for `gen_rec::class_fe_r_pop`.
#[allow(clippy::too_many_arguments)]
pub fn cons_block_recs_temp(
    pers: &PersTier,
    vis2: u64,
    st: &mut AState,
    p: &BlockShape,
    m: u64,
    out: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    fe: IFEnv,
    prevs: Vec<(NIdx, Option<(u64, u64)>)>,
) -> Result<(IFEnv, Vec<(NIdx, Option<(u64, u64)>)>), CheckError> {
    if m >= out.len() as u64 {
        Ok((fe, prevs))
    } else {
        let cv: IConstantVal = env::i_constant_val_dup(&out[m as usize].0);
        let n: NIdx = cv.name.dup2();
        let m_i: u64 = block_parts::major_idx_at(p, m);
        let r_p: u64 = block_parts::rule_prefix_at(p, m);
        match rec_check::tgt_stored_rules(pers, vis2, st, &fe, &cv, r_p, &out[m as usize].1, &out[m as usize].2) {
            Err(e) => Err(e),
            Ok(rules) => {
                let mut fe2: IFEnv = fe;
                let prev: Option<(u64, u64)> = env::ifenv_push_temp(&mut fe2, IConstantInfo::RecInfo(cv, m_i, r_p, rules));
                let mut ps: Vec<(NIdx, Option<(u64, u64)>)> = prevs;
                ps.push((n, prev));
                cons_block_recs_temp(pers, vis2, st, p, m + 1, out, fe2, ps)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:103-115 checkBlockTail
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tail_stored_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:143-163 checkBlockTailS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tail_stored_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:135-148 checkBlockTailStored` —
/// **the stored recursors against the generated ones, and their install**: the
/// generated install pushed, a flush entering it, the comparison, the pushes
/// undone, a flush leaving it, and the stored recursors consed at their majors.
#[allow(clippy::too_many_arguments)]
pub fn check_block_tail_stored(
    pers: &PersTier,
    vis2: u64,
    st: &mut AState,
    mode: &CheckMode,
    p: &BlockShape,
    out: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    match cons_block_recs_temp(pers, vis2, st, p, 0, out, fe, Vec::new()) {
        Err(e) => Err(e),
        Ok((fe_g, prevs)) => {
            core::flush_caches(st);
            match stored_recs::stored_recs_check(pers, st, mode, &fe_g, &p.recs, out, 0) {
                Err(e) => Err(e),
                Ok(()) => {
                    let fe2: IFEnv = gen_rec::class_fe_r_pop(fe_g, &prevs, prevs.len());
                    core::flush_caches(st);
                    let stored: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)> =
                        stored_recs::stored_out(&p.recs, out, 0, Vec::new());
                    rec_check::cons_block_recs_t(pers, vis2, st, p, 0, &stored, fe2)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:103-115 checkBlockTail
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tail_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:143-163 checkBlockTailS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_tail_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:150-166 checkBlockTail` — **the
/// install after the pass**: the index binders' sorts, the constructors
/// consed (and the flush entering that environment), the recursor stage, the
/// stored recursors against the generated ones and consed at their majors, and
/// the projection tables.
pub fn check_block_tail(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    block: &Vec<IConstantInfo>,
    q: BlockPass,
) -> Result<IFEnv, CheckError> {
    match block_install::check_block_idx_sorts(pers, st, mode, &q.env1, &q.p.shape, &q.cv_tas, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(_isorts) => {
            let fe2: IFEnv = block_install::cons_block_ctors(q.p.shape.n_p, &q.ctors_as, 0, q.env1);
            core::flush_caches(st);
            let vis2: u64 = fe2.visible_below;
            let nested: bool = rec_check::block_nested_bit(&q.p.shape, &q.kinds);
            match check_block_rec(pers, st, mode, fe2, &q.p, nested, &q.params, &q.tbl, &q.rd, &q.cls, block, &q.cv_tas) {
                Err(e) => Err(e),
                Ok((fe2b, out)) => match check_block_tail_stored(pers, vis2, st, mode, &q.p.shape, &out, fe2b) {
                    Err(e) => Err(e),
                    Ok(fe3) => check_block_tables(pers, st, &q.p.shape, &q.ctors_as, &q.sortsss, 0, fe3),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:150-163 checkBlock
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:187-198 checkBlockKS
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove block_tail::check_block_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:168-181 checkBlock` — **check
/// and install a block on the uniform route**: the distinct names, the flush,
/// the pass at official's `is_rec`, and the install after it.
pub fn check_block(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    p0: &BlockParts,
) -> Result<IFEnv, CheckError> {
    let ctor_names: Vec<NIdx> =
        rec_check::ctor_names(&block_parts::all_ctors(&p0.shape.members, 0, Vec::new()), 0, Vec::new());
    if !checker_base::name_nodup(&ctor_names) || !checker_base::name_nodup(&shape_member_names(&p0.shape)) {
        fail(core_types::invalid(code_points(&M_DUP_CTOR)))
    } else {
        core::flush_caches(st);
        match block_install::block_raw_rec(pers, st, p0) {
            Err(e) => Err(e),
            Ok(raw) => match check_block_pass(pers, st, mode, fe, p0, raw) {
                Err(e) => Err(e),
                Ok(q) => check_block_tail(pers, st, mode, block, q),
            },
        }
    }
}
