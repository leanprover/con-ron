//! `arena::inductives::block_tail` — the inductive block's check.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockTail.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockTail.lean` over handles — `checkBlock`,
//! the block's check and install — at the executed tier's discipline:
//! `ConLeche/Cached/CheckerC.lean`'s `checkBlockKS`/`checkBlockPassS`/
//! `checkBlockTailS`/`reduceMemberS`, whose flushes at the environment
//! transitions are the arena's (task #97g item 4; the arena has one core, the
//! cached one).
//!
//! ## The twin's deviations
//!
//! * **`BlockPass` is not generic** in the environment representation:
//!   con-leche parameterises it because it has two (`Env` and `FEnv`); the
//!   arena has one.
//! * **The index is threaded by value**, and the recursor stage hands it
//!   back (`arena::inductives::gen_rec`'s module note).
//! * **The generated install is pushed in place and popped**
//!   (`cons_block_recs_temp`, `gen_rec::class_fe_r_pop`), where con-leche's
//!   cached driver reads an overlay on the constructors' index
//!   (`FEnv.overlay`): the same read-only environment, a flush entering and
//!   leaving it, and no copy of the index.
//! * **The block's install is pushed onto the constructors' environment the
//!   checks built**, not onto a kept copy of the environment the block was
//!   checked at: `check_block_tail` hands that environment back, and it holds
//!   exactly `blockFormers p₀` and `blockCtors p₀` above the original (the
//!   formers are consed as declared, and `blockCapsAt` reads neither the sort
//!   the pass completes nor the members' reduced telescopes).  So the push of
//!   the recursors and the tables there (`install::block_recs`, the tables
//!   `install::block_tables` built once after the pass) is con-leche's
//!   `pushDelta (blockConstants p₀) Q` on the original, with no copy of the
//!   index.

use super::block_install;
use super::block_shape;
use super::block_shape::{shape_member_names, BlockShape, MemberShape};
use super::class_read::ClassRead;
use super::gen_rec;
use super::positivity;
use super::positivity::{nest_seeds, NestCtorNf, NestFieldKind};
use super::rec_check;
use super::rec_check::TargetMajor;
use super::stream_recs;
use super::struct_install;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IProjTable};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::install;
use crate::arena::monad::{fail, AState};
use crate::arena::pins;
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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// ``direct rec: a family at a `Bool` constructor's name``, as code points.
pub const M_BOOL_NAME: [u32; 51] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 32, 102, 97, 109, 105, 108, 121, 32,
    97, 116, 32, 97, 32, 96, 66, 111, 111, 108, 96, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 39, 115, 32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `this family stored at a definition`, as code points (the interpolated name dropped).
pub const M_AT_DEFINITION: [u32; 34] = [
    116, 104, 105, 115, 32, 102, 97, 109, 105, 108, 121, 32, 115, 116, 111, 114, 101, 100, 32, 97,
    116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: a type former's declared type and its reduct differ`, as code points.
pub const M_REDUCT_DIFFERS: [u32; 63] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 97, 32, 116, 121, 112, 101, 32, 102,
    111, 114, 109, 101, 114, 39, 115, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 116, 121, 112,
    101, 32, 97, 110, 100, 32, 105, 116, 115, 32, 114, 101, 100, 117, 99, 116, 32, 100, 105, 102,
    102, 101, 114,
];

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:24-42 BlockPass
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:50-62 BlockPass` — **what one
/// pass over the formers, the constructors and the classes yields**: the
/// environment holding all k formers, the completed record (the sort read),
/// the positivity function's field kinds, the canonical parameters, the
/// pre-pass's reading, the classes, and the positivity check's table.
pub struct BlockPass {
    pub env1: IFEnv,
    pub p: BlockShape,
    pub kinds: Vec<Vec<Vec<NestFieldKind>>>,
    pub params: Vec<EIdx>,
    pub rd: ClassRead,
    pub cls: Vec<TargetMajor>,
    pub tbl: Vec<NestCtorNf>,
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
/// con-leche: ConLeche/Cached/CheckerC.lean:187-201 checkBlockPassS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:64-83 checkBlockPass` — **one
/// pass over the formers, the constructors and the classes** at the block's
/// `is_rec` verdict: the formers (and the flush entering the environment
/// that holds them all), the constructors, the classes, and the positivity
/// check as ONE walk — the members' root frame, then every outside class.
pub fn check_block_pass(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p0: &BlockShape,
    is_rec: bool,
) -> Result<BlockPass, CheckError> {
    match block_install::check_block_inds(pers, st, mode, fe, p0, is_rec) {
        Err(e) => Err(e),
        Ok((fe1, p1)) => {
            core::flush_caches(st);
            match block_install::check_block_ctors(pers, st, mode, &fe1, &fe1, &p1, 0) {
                Err(e) => Err(e),
                Ok(()) => check_block_pass_classes(pers, st, mode, fe1, p1),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:44-62 checkBlockPass
/// con-leche: ConLeche/Cached/CheckerC.lean:187-201 checkBlockPassS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:64-83 checkBlockPass` — the
/// walk's context, the classes, the root frame and the seeds.
pub fn check_block_pass_classes(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe1: IFEnv,
    p1: BlockShape,
) -> Result<BlockPass, CheckError> {
    match block_install::block_nest_ctx(pers, st, &p1) {
        Err(e) => Err(e),
        Ok((ctx, holes)) => match gen_rec::check_block_classes(pers, st, mode, &fe1, &p1, &ctx.params) {
            Err(e) => Err(e),
            Ok((rd, ms)) => match block_install::check_block_positivity(pers, st, mode, &fe1, &p1) {
                Err(e) => Err(e),
                Ok((outs, pos)) => match gen_rec::class_seeds(pers, st, &ctx, &holes, &ms, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(seeds) => match nest_seeds(pers, st, mode, &fe1, &ctx, &seeds, 0, pos) {
                        Err(e) => Err(e),
                        Ok(ns) => {
                            let params: Vec<EIdx> = env::eidx_vec_dup(&ctx.params);
                            Ok(BlockPass {
                                env1: fe1,
                                p: p1,
                                kinds: block_install::nest_out_kinds(&outs, 0, Vec::new()),
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

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:64-77 checkBlockRec
/// con-leche: ConLeche/Cached/CheckerC.lean:203-223 checkBlockTailS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::check_block_rec_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:85-94 checkBlockRec` — **the
/// installer's recursor stage**: the GENERATED recursor stage at the
/// constructors' environment, on the stream's own recursor family (the raw
/// `block`), the pass's classes and table, and the container bit.
#[allow(clippy::too_many_arguments)]
#[allow(clippy::type_complexity)]
pub fn check_block_rec(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    p: &BlockShape,
    nested: bool,
    params: &Vec<EIdx>,
    tbl: &Vec<NestCtorNf>,
    rd: &ClassRead,
    ms: &Vec<TargetMajor>,
    block: &Vec<IConstantInfo>,
) -> Result<(IFEnv, Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>), CheckError> {
    gen_rec::gen_rec_check(pers, st, mode, fe, p, nested, params, tbl, rd, ms, block)
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:79-90 consBlockRecsT
/// con-leche: ConLeche/Cached/CheckerC.lean:203-223 checkBlockTailS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::cons_block_recs_temp_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:96-108 consBlockRecsTemp` — **the
/// checked family consed, at its majors, TEMPORARILY**: the records
/// `rec_check::block_rec_infos_tf` built (each recursor with its rules at ITS
/// major) from `i` on, pushed in place.  Returns the rows the pushes
/// displaced, for `gen_rec::class_fe_r_pop`.
pub fn cons_block_recs_temp(
    infos: &Vec<IConstantInfo>,
    i: usize,
    fe: IFEnv,
    prevs: Vec<(NIdx, Option<u64>)>,
) -> (IFEnv, Vec<(NIdx, Option<u64>)>) {
    if i >= infos.len() {
        (fe, prevs)
    } else {
        let n: NIdx = env::i_constant_info_name(&infos[i]);
        let mut fe2: IFEnv = fe;
        let prev: Option<u64> = env::ifenv_push_temp(&mut fe2, env::i_constant_info_dup(&infos[i]));
        let mut ps: Vec<(NIdx, Option<u64>)> = prevs;
        ps.push((n, prev));
        cons_block_recs_temp(infos, i + 1, fe2, ps)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:92-98 checkBlockTables
/// con-leche: ConLeche/Cached/IndTail.lean:204-209 checkBlockTablesC
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:110-118 checkBlockTables` — **the
/// checks of the block's projection tables** (`install::block_tables`) from
/// table `i` on, at the environment holding the formers and the constructors.
pub fn check_block_tables(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    q: &Vec<IProjTable>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= q.len() {
        Ok(())
    } else {
        match struct_install::check_struct_proj_table(pers, st, &q[i], fe) {
            Err(e) => Err(e),
            Ok(()) => check_block_tables(pers, st, fe, q, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:100-112 checkBlockTail
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::check_block_tail_stream_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:203-223 checkBlockTailS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::check_block_tail_stream_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:120-145 checkBlockTail` —
/// **the stream's recursors against the generated ones**: the K flags, then
/// the generated family pushed at its majors, a flush entering it, the
/// comparison, the pushes undone, a flush leaving it, and the checks of the
/// block's projection tables `q` at the constructors' environment, which is
/// handed back.
pub fn check_block_tail_stream(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    p: &BlockShape,
    out: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    q: &Vec<IProjTable>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    match stream_recs::stream_k_check(p, &p.recs, out, 0) {
        Err(e) => Err(e),
        Ok(()) => match rec_check::block_rec_infos_tf(pers, st, p, 0, out, Vec::new()) {
            Err(e) => Err(e),
            Ok(infos) => {
                let (fe_g, prevs) = cons_block_recs_temp(&infos, 0, fe, Vec::new());
                core::flush_caches(st);
                match stream_recs::stream_recs_check(pers, st, mode, &fe_g, &p.recs, out, 0) {
                    Err(e) => Err(e),
                    Ok(()) => {
                        let fe2: IFEnv = gen_rec::class_fe_r_pop(fe_g, &prevs, prevs.len());
                        core::flush_caches(st);
                        match check_block_tables(pers, st, &fe2, q, 0) {
                            Err(e) => Err(e),
                            Ok(()) => Ok(fe2),
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:100-112 checkBlockTail
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::check_block_tail_refines, then delete this line
/// con-leche: ConLeche/Cached/CheckerC.lean:203-223 checkBlockTailS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::check_block_tail_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:120-145 checkBlockTail` — **the
/// checks after the pass**: the index binders' sorts, the constructors consed
/// (and the flush entering that environment), the generated recursors, the
/// stream's recursors against them and the block's projection tables
/// `tables`.  Returns the constructors' environment (the module note's last
/// deviation).
pub fn check_block_tail(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    block: &Vec<IConstantInfo>,
    q: BlockPass,
    tables: &Vec<IProjTable>,
) -> Result<IFEnv, CheckError> {
    match block_install::check_block_idx_sorts(pers, st, mode, &q.env1, &q.p, 0) {
        Err(e) => Err(e),
        Ok(()) => {
            let groups: Vec<(NIdx, Vec<(IConstantVal, u64)>)> =
                block_shape::ctor_groups(&q.p.members, 0, Vec::new());
            let fe2: IFEnv = block_install::cons_block_ctors(q.p.n_p, &groups, 0, q.env1);
            core::flush_caches(st);
            let nested: bool = rec_check::block_nested_bit(&q.p, &q.kinds);
            match check_block_rec(pers, st, mode, fe2, &q.p, nested, &q.params, &q.tbl, &q.rd, &q.cls, block) {
                Err(e) => Err(e),
                Ok((fe2b, out)) => check_block_tail_stream(pers, st, mode, &q.p, &out, tables, fe2b),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The block's check
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:116-122 declinedAtDefinition
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:149-153 declinedAtDefinition` — **the
/// families declined at a definition**: the names a literal's constructor
/// form applies, and `Bool`.
pub fn declined_at_definition(st: &AState) -> Result<Vec<NIdx>, CheckError> {
    match pins::pin_string_of_list(st) {
        Err(e) => Err(e),
        Ok(a) => match pins::pin_list_nil(st) {
            Err(e) => Err(e),
            Ok(b) => match pins::pin_list_cons(st) {
                Err(e) => Err(e),
                Ok(c) => match pins::pin_char_of_nat(st) {
                    Err(e) => Err(e),
                    Ok(d) => match pins::pin_bool(st) {
                        Err(e) => Err(e),
                        Ok(f) => {
                            let mut ns: Vec<NIdx> = Vec::new();
                            ns.push(a);
                            ns.push(b);
                            ns.push(c);
                            ns.push(d);
                            ns.push(f);
                            Ok(ns)
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:124-136 reduceMember
/// con-leche: ConLeche/Cached/CheckerC.lean:225-236 reduceMemberS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::reduce_member_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:155-172 reduceMember` — **a
/// member's former at its telescope**, official's `whnf` loop where the
/// declared type does not show it: the declared type checked, reduced, and
/// the two compared; a member already at its telescope as it is.
pub fn reduce_member(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ms: &MemberShape,
    n_p: u64,
) -> Result<MemberShape, CheckError> {
    match core::former_def_headed(pers, st, &ms.cv_t) {
        Err(e) => Err(e),
        Ok(false) => Ok(block_shape::member_shape_dup(ms)),
        Ok(true) => match declined_at_definition(st) {
            Err(e) => Err(e),
            Ok(declined) => {
                if positivity::names_contain(&declined, &ms.cv_t.name, 0) {
                    fail(core_types::not_implemented(code_points(&M_AT_DEFINITION)))
                } else {
                    reduce_member_checked(pers, st, mode, fe, ms, n_p)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:124-136 reduceMember
/// con-leche: ConLeche/Cached/CheckerC.lean:225-236 reduceMemberS
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove block_tail::reduce_member_checked_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:155-172 reduceMember` — the inner
/// `do` block: the constant check, the reduct (`reducedFormer`) and the
/// definitional comparison of the two types.
pub fn reduce_member_checked(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    ms: &MemberShape,
    n_p: u64,
) -> Result<MemberShape, CheckError> {
    match checker_base::check_constant_val(pers, st, mode, fe, &ms.cv_t, false) {
        Err(e) => Err(e),
        Ok(()) => match positivity::reduced_former(pers, st, mode, fe, &ms.cv_t, n_p + ms.n_idx) {
            Err(e) => Err(e),
            Ok(cv_r) => match core::is_def_eq_core(pers, st, mode, fe, core::CHECK_FUEL, 0, &ms.cv_t.ty, &cv_r.ty) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::invalid(code_points(&M_REDUCT_DIFFERS))),
                Ok(true) => Ok(MemberShape {
                    cv_t: cv_r,
                    declared: env::i_constant_val_dup(&ms.declared),
                    n_idx: ms.n_idx,
                    ctors: block_shape::ctors_dup(&ms.ctors, 0, Vec::new()),
                }),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:138-145 reduceMembers
/// con-leche: ConLeche/Cached/CheckerC.lean:238-245 reduceMembersS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:174-184 reduceMembers` — the members
/// from `i` on, each at its telescope, a flush before each (the cached
/// twin's).
pub fn reduce_members(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    ms: &Vec<MemberShape>,
    i: usize,
    out: Vec<MemberShape>,
) -> Result<Vec<MemberShape>, CheckError> {
    if i >= ms.len() {
        Ok(out)
    } else {
        core::flush_caches(st);
        match reduce_member(pers, st, mode, fe, &ms[i], n_p) {
            Err(e) => Err(e),
            Ok(m) => {
                let mut o: Vec<MemberShape> = out;
                o.push(m);
                reduce_members(pers, st, mode, fe, n_p, ms, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:147-163 checkBlock
/// con-leche: ConLeche/Cached/CheckerC.lean:247-259 checkBlockKS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:186-216 checkBlock` — **check
/// an inductive block and install it**: the distinct names, no member at a
/// `Bool` constructor's name, each former reduced to its telescope once
/// (official's `check_inductive_types`), the flush, the pass at official's
/// `is_rec` (`blockIsRec`, read off the block as declared), the projection
/// tables read off the block, the checks after it (the tables' among them),
/// and the block's install (`install::block_recs` and the same tables on the
/// constructors' environment: the module note's last deviation).
pub fn check_block(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    p0: &BlockShape,
) -> Result<IFEnv, CheckError> {
    let ctor_names: Vec<NIdx> =
        rec_check::ctor_names(&block_shape::all_ctors(&p0.members, 0, Vec::new()), 0, Vec::new());
    let names: Vec<NIdx> = shape_member_names(p0);
    if !checker_base::name_nodup(&ctor_names) || !checker_base::name_nodup(&names) {
        fail(core_types::invalid(code_points(&M_DUP_CTOR)))
    } else {
        match pins::pin_bool_true(st) {
            Err(e) => Err(e),
            Ok(bt) => match pins::pin_bool_false(st) {
                Err(e) => Err(e),
                Ok(bf) => {
                    if positivity::names_contain(&names, &bt, 0) || positivity::names_contain(&names, &bf, 0) {
                        fail(core_types::invalid(code_points(&M_BOOL_NAME)))
                    } else {
                        check_block_reduced(pers, st, mode, fe, block, p0)
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:147-163 checkBlock
/// con-leche: ConLeche/Cached/CheckerC.lean:247-259 checkBlockKS
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockTail.lean:186-216 checkBlock` — after the
/// name checks: the members reduced, the flush, the pass, the projection
/// tables read off the block once (an internal error where a constructor is
/// too short for them), the tail, which checks those tables, and the install,
/// which pushes the same tables.
pub fn check_block_reduced(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: IFEnv,
    block: &Vec<IConstantInfo>,
    p0: &BlockShape,
) -> Result<IFEnv, CheckError> {
    match reduce_members(pers, st, mode, &fe, p0.n_p, &p0.members, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(ms) => {
            core::flush_caches(st);
            match block_install::block_is_rec(pers, st, p0) {
                Err(e) => Err(e),
                Ok(is_rec) => {
                    let mut p: BlockShape = block_shape::block_shape_dup(p0);
                    p.members = ms;
                    match check_block_pass(pers, st, mode, fe, &p, is_rec) {
                        Err(e) => Err(e),
                        Ok(q) => match install::block_tables(pers, st, p0, &p0.members, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(o) => match checker_base::unwrap_or(
                                o,
                                core_types::internal(code_points(&struct_install::M_TBL_BODIES)),
                            ) {
                                Err(e) => Err(e),
                                Ok(tables) => match check_block_tail(pers, st, mode, block, q, &tables) {
                                    Err(e) => Err(e),
                                    Ok(fe2) => match install::block_recs(pers, st, p0, &p0.recs, 0, Vec::new()) {
                                        Err(e) => Err(e),
                                        Ok(recs) => Ok(install::push_delta(fe2, recs, tables)),
                                    },
                                },
                            },
                        },
                    }
                }
            }
        }
    }
}
