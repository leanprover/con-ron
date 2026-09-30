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
//!   pushes above it (`consBlockRecsTF`'s fixed `find?`/`resolves`).
//! * **`checkBlockTablesF`'s walkers are the arena's** (`struct_install`'s
//!   `check_struct_proj_table`, the one table install).

use super::block_install;
use super::block_parts;
use super::block_parts::{complete, shape_member_names, BlockParts, BlockShape};
use super::class_read::ClassRead;
use super::gen_rec;
use super::positivity::{nest_seeds, NestCtorNf, NestFieldKind};
use super::rec_check;
use super::rec_check::TargetMajor;
use super::struct_install;
use super::struct_parts;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv};
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{fail, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: duplicate constructor`, as code points.
pub const M_DUP_CTOR: [u32; 33] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 100, 117, 112, 108, 105, 99, 97, 116,
    101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
];

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:25-52 BlockPass
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean BlockPass` — **what one
/// pass over the formers, the constructors and the classes yields**: the
/// environment holding all k formers, the annotated formers, the completed
/// record, the annotated constructors and their fields' sorts per member,
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:54-74 checkBlockPass
/// con-leche: ConLeche/Cached/CheckerC.lean:136-154 checkBlockPassS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlockPass` — **one
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:54-74 checkBlockPass
/// con-leche: ConLeche/Cached/CheckerC.lean:136-154 checkBlockPassS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlockPass` — the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:76-91 checkBlockRec
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlockRec` — **the
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:108-123 checkBlockTables
/// con-leche: ConLeche/Kernel/Inductives/BlockInstallF.lean:191-204 checkBlockTablesF
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlockTables` — **the
/// projection table at every STRUCTURE-LIKE member** (one constructor, no
/// index) from member `i` on: the member's table at the tagged tower's
/// projection offset `1`; nothing at any other member.
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
                    1,
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:125-138 checkBlockTail
/// con-leche: ConLeche/Cached/CheckerC.lean:156-169 checkBlockTailS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlockTail` — **the
/// install after the pass**: the index binders' sorts, the constructors
/// consed (and the flush entering that environment), the recursor stage, the
/// recursors consed at their majors, and the projection tables.
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
                Ok((fe2b, out)) => match rec_check::cons_block_recs_t(pers, vis2, st, &q.p.shape, 0, &out, fe2b) {
                    Err(e) => Err(e),
                    Ok(fe3) => check_block_tables(pers, st, &q.p.shape, &q.ctors_as, &q.sortsss, 0, fe3),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:140-148 checkBlock
/// con-leche: ConLeche/Cached/CheckerC.lean:171-179 checkBlockKS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean checkBlock` — **check
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
