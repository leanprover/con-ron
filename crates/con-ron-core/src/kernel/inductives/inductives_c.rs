//! The **cached drivers of the two inductive routes** —
//! `ConLeche/Cached/CheckerC.lean`'s stages for the direct (fixpoint) and the
//! modeled block, i.e. what the shipped binary actually executes.
//!
//! Those stages "mirror their `ConLeche/Kernel/Checker.lean` counterparts
//! clause by clause; the differences are exactly: `flushC` at environment
//! transitions, `FEnv.push` maintaining the index, and *every* environment
//! lookup routed through the index" (the cited file's own section note).  The
//! port has one spelling of the index already (`super`'s module note 1), so
//! what is left here is the **`flushC` policy** — the one thing DESIGN.md
//! §3.1 insists must be mirrored, because a flush changes the memo hit/miss
//! pattern — plus the two block drivers themselves.
//!
//! **Where this module belongs.**  `Cached/CheckerC.lean` as a whole is task
//! #24's (`cached/checker_c.rs`); only its inductive-route stages are here,
//! so that task #25 can land the routes without touching another task's file.
//! Task #24's `checkDeclC`/`installDeclC` layer calls `check_native_s` and
//! `check_ind_decl_s` and needs nothing else from here.

use crate::cached::state_c;
use crate::cached::state_c::CState;
use crate::kernel::basis_pins;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal, IndCaps};
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::modeled;
use crate::kernel::inductives::native_install;
use crate::kernel::inductives::native_install::NativePass;
use crate::kernel::inductives::native_parts::NativeParts;
use crate::kernel::inductives::struct_install;
use crate::kernel::name::Name;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The modeled route's drivers (`CheckerC.lean:100-175, 233-277`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CheckerC.lean:105-113 checkIndMemberS
/// One non-recursor member, through the index: **one flush entering the
/// member's environment**, then `checkIndMember`'s body.
pub fn check_ind_member_s(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    caps: &IndCaps,
    fe: FEnv,
    ci: &ConstantInfo,
) -> CheckM<FEnv> {
    state_c::flush_c(st);
    modeled::check_ind_member(mode, st, block_names, caps, fe, ci)
}

/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// `nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe`, as an index
/// recursion over the filtered members.
pub fn check_ind_members_s(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    caps: &IndCaps,
    fe: FEnv,
    nonrecs: &Vec<ConstantInfo>,
    i: usize,
) -> CheckM<FEnv> {
    if i >= nonrecs.len() {
        Ok(fe)
    } else {
        match check_ind_member_s(mode, st, block_names, caps, fe, &nonrecs[i]) {
            Err(err) => Err(err),
            Ok(fe2) => check_ind_members_s(mode, st, block_names, caps, fe2, nonrecs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:115-129 provisionRecsS
/// Phase 0 of the recursor group, through the index: **one flush per
/// recursor** before its constant is checked, then `provisionRecs`' step.
pub fn provision_recs_s(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe_acc: FEnv,
    recs: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<(ConstantVal, u64, u64, Vec<env::RecRule>)>,
) -> CheckM<(FEnv, Vec<(ConstantVal, u64, u64, Vec<env::RecRule>)>)> {
    if i >= recs.len() {
        Ok((fe_acc, out))
    } else {
        state_c::flush_c(st);
        match modeled::provision_recs_step(mode, st, block_names, fe_acc, &recs[i]) {
            Err(err) => Err(err),
            Ok(q) => {
                let mut out = out;
                out.push((q.1, q.2, q.3, q.4));
                provision_recs_s(mode, st, block_names, q.0, recs, i + 1, out)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:131-151 checkIndRecsS
/// The recursor group, through the index: **all iota-rule checks run at
/// `envSelf`** — one flush entering the phase, none inside the fold (the
/// fold's accumulator environments are never passed to the operations).  The
/// ruled recursors are installed on the `env₂` snapshot of the index.
///
/// Deviation: the flush the cited code puts between `provisionRecsS` and the
/// fold is spelled here, and the per-recursor flush of `provisionRecsS` is
/// `provision_recs_s`'s; `modeled::check_ind_recs` holds the rest of the body
/// (including the two `fenv::dup`s its module note explains).
pub fn check_ind_recs_s(
    mode: &CheckMode,
    st: &mut CState,
    block_names: &Vec<Name>,
    fe2: FEnv,
    recs: &Vec<ConstantInfo>,
) -> CheckM<FEnv> {
    const M_EQ: [u32; 44] = [
        109, 111, 100, 101, 108, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32,
        114, 101, 113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 69, 113, 32, 98, 97,
        115, 105, 115, 32, 32, 32, 32, 32, 32,
    ];
    if recs.len() == 0 {
        Ok(fe2)
    } else if !basis_pins::eq_basis_pinned(&fe2) {
        Err(core_types::not_implemented(core_types::code_points(&M_EQ)))
    } else {
        let f = modeled::BlockRename { block_names };
        let fe_env: FEnv = fenv::dup(&fe2);
        match provision_recs_s(
            mode,
            st,
            block_names,
            fenv::dup(&fe2),
            recs,
            0,
            Vec::new(),
        ) {
            Err(err) => Err(err),
            Ok(pq) => {
                state_c::flush_c(st);
                modeled::check_ind_recs_fold(mode, st, &fe_env, &pq.0, &f, &pq.1, 0, fe2)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:168-175 installProjFnStepS
/// One projection-function install step, through the index: **one flush**
/// before the projection's own checks (the artifact lookup goes through the
/// index).
pub fn install_proj_fn_step_s(
    mode: &CheckMode,
    st: &mut CState,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    fe: FEnv,
    i: u64,
) -> CheckM<FEnv> {
    if fenv::find(&fe, &crate::kernel::core_k::proj_model_name(t, i)).is_some() {
        state_c::flush_c(st);
        modeled::check_proj_fn(mode, st, fe, t, ctor_name, lps, n_p, n_f, i)
    } else {
        Ok(fe)
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// `(List.range nF).foldlM (installProjFnStepS …) fe₃`, as an index recursion.
pub fn install_proj_fns_s(
    mode: &CheckMode,
    st: &mut CState,
    t: &Name,
    ctor_name: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    fe: FEnv,
    i: u64,
) -> CheckM<FEnv> {
    if i >= n_f {
        Ok(fe)
    } else {
        match install_proj_fn_step_s(mode, st, t, ctor_name, lps, n_p, n_f, fe, i) {
            Err(err) => Err(err),
            Ok(fe2) => install_proj_fns_s(mode, st, t, ctor_name, lps, n_p, n_f, fe2, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// **The modeled inductive block**, returning the extended index: every member
/// is checked against its `_model` counterpart, then stored as a real
/// inductive-kind constant.  A single-constructor block determines its
/// capability record first (recorded on the inductive) and, when
/// structure-like (`ctorTargetsFam`), additionally installs the projection
/// functions the model documents.
pub fn check_ind_decl_s(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    block: &Vec<ConstantInfo>,
) -> CheckM<FEnv> {
    const M_ORDER: [u32; 40] = [
        114, 101, 99, 117, 114, 115, 111, 114, 32, 98, 101, 102, 111, 114, 101, 32, 111, 116,
        104, 101, 114, 32, 98, 108, 111, 99, 107, 32, 109, 101, 109, 98, 101, 114, 115, 32,
        32, 32, 32, 32,
    ];
    let recs: Vec<ConstantInfo> = modeled::filter_recs(block, true);
    let nonrecs: Vec<ConstantInfo> = modeled::filter_recs(block, false);
    if !env::block_rec_suffix_ok(block) {
        Err(core_types::not_implemented(core_types::code_points(&M_ORDER)))
    } else {
        let block_names: Vec<Name> = modeled::block_names_of(block);
        match modeled::single_ind_ctor(block) {
            Some(sq) => check_ind_decl_struct_s(
                mode, st, fe, &block_names, &nonrecs, &recs, sq.0, sq.1, sq.2, sq.3,
            ),
            None => {
                let caps: IndCaps = env::ind_caps_default();
                match check_ind_members_s(mode, st, &block_names, &caps, fe, &nonrecs, 0) {
                    Err(err) => Err(err),
                    Ok(fe2) => check_ind_recs_s(mode, st, &block_names, fe2, &recs),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:233-268 checkIndDeclSF
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:781-834 checkModeled
/// The single-type-former, single-constructor arm of the modeled driver: the
/// capability record, the members, the recursors, the eta constructor
/// residual, the projection name family's freshness and — at a structure-like
/// block — the projection functions.
pub fn check_ind_decl_struct_s(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    block_names: &Vec<Name>,
    nonrecs: &Vec<ConstantInfo>,
    recs: &Vec<ConstantInfo>,
    cv_t: ConstantVal,
    cv_c: ConstantVal,
    n_p: u64,
    n_f: u64,
) -> CheckM<FEnv> {
    const M_ETA: [u32; 47] = [
        109, 111, 100, 101, 108, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101,
        58, 32, 101, 116, 97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32,
        114, 101, 115, 105, 100, 117, 97, 108, 32, 32, 32, 32,
    ];
    const M_FAM: [u32; 28] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 97,
        109, 105, 108, 121, 32, 116, 97, 107, 101, 110,
    ];
    let caps: IndCaps = modeled::ind_block_caps(mode, &fe, &cv_t, &cv_c, n_p, n_f);
    let eta: bool = caps.eta;
    match check_ind_members_s(mode, st, block_names, &caps, fe, nonrecs, 0) {
        Err(err) => Err(err),
        Ok(fe2) => match check_ind_recs_s(mode, st, block_names, fe2, recs) {
            Err(err) => Err(err),
            Ok(fe3) => {
                if !modeled::ctor_residual_ok(
                    mode,
                    &fe3,
                    &cv_t.name,
                    &cv_c.name,
                    &cv_t.level_params,
                    n_p,
                    n_f,
                    eta,
                ) {
                    Err(core_types::not_implemented(core_types::code_points(&M_ETA)))
                } else if !struct_install::proj_fn_family_free_from(
                    &fe3,
                    &cv_t.name,
                    n_f,
                    0,
                ) {
                    Err(core_types::invalid(core_types::code_points(&M_FAM)))
                } else if modeled::ctor_targets_fam(
                    &cv_c.ty,
                    &cv_t.name,
                    &cv_t.level_params,
                    n_p,
                    n_f,
                ) {
                    install_proj_fns_s(
                        mode,
                        st,
                        &cv_t.name,
                        &cv_c.name,
                        &cv_t.level_params,
                        n_p,
                        n_f,
                        fe3,
                        0,
                    )
                } else {
                    Ok(fe3)
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The direct route's driver (`CheckerC.lean:177-231`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CheckerC.lean:177-190 checkNativePassS
/// `checkNativePass` through the index: **one flush per environment
/// transition** — the cited flush sits between the former's stage and the
/// constructors' — and `checkNativePass`'s body otherwise.
///
/// The flush sits **exactly** where the cited `flushC` does, between the
/// former's stage and the constructors': `native_install` splits the pass
/// into `check_native_pass_former` and `check_native_pass_ctors` for that
/// reason, and the pure `check_native_pass` is their composition without a
/// flush.  So no memo *policy* differs from the cited code (DESIGN.md §3.1).
pub fn check_native_pass_s(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p0: &NativeParts,
    is_rec: bool,
) -> CheckM<(NativePass, bool)> {
    match native_install::check_native_pass_former(mode, st, fe, p0, is_rec) {
        Err(err) => Err(err),
        Ok(q) => {
            state_c::flush_c(st);
            native_install::check_native_pass_ctors(mode, st, q.0, q.1, q.2, p0, q.3)
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:192-215 checkNativeTailS
/// `checkNativeTail` through the index: **one flush entering the recursor's
/// environment**: the cited `flushC` sits after `consSumCtorsF` and before
/// `checkNativeRecF`, and `native_install`'s three-way split
/// (`check_native_tail_guards`, `check_native_cons`, `check_native_install`)
/// puts it there exactly.
pub fn check_native_tail_s(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    q: NativePass,
) -> CheckM<FEnv> {
    match native_install::check_native_tail_guards(mode, st, fe, &q) {
        Err(err) => Err(err),
        Ok(()) => {
            let cq = native_install::check_native_cons(q);
            state_c::flush_c(st);
            native_install::check_native_install(mode, st, cq.0, cq.1, cq.2, cq.3, cq.4)
        }
    }
}

/// con-leche: ConLeche/Cached/CheckerC.lean:217-231 checkNativeS
/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// **`checkNative` through the index**: the distinct constructor names, one
/// flush, the pass at the syntactic `is_rec` reading, again at the classified
/// verdict where the reading overshot, and the install after it.  This is the
/// entry `Cached/ParsedC.lean:239` calls on a recognised direct block.
pub fn check_native_s(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    p0: &NativeParts,
) -> CheckM<FEnv> {
    const M_DUP: [u32; 33] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 100, 117, 112, 108, 105, 99,
        97, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
    ];
    const M_SETTLE: [u32; 57] = [
        100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 99, 97,
        112, 97, 98, 105, 108, 105, 116, 121, 32, 114, 101, 99, 111, 114, 100, 32, 100, 105,
        100, 32, 110, 111, 116, 32, 115, 101, 116, 116, 108, 101, 32, 32, 32, 32, 32, 32, 32,
        32, 32,
    ];
    let names: Vec<Name> = native_install::ctor_names(&p0.shape.ctors);
    if !crate::kernel::level::name_nodup(&names) {
        Err(core_types::invalid(core_types::code_points(&M_DUP)))
    } else {
        state_c::flush_c(st);
        match check_native_pass_s(mode, st, fe, p0, native_install::native_raw_rec(p0)) {
            Err(err) => Err(err),
            Ok(q) => {
                if q.1 {
                    check_native_tail_s(mode, st, fe, q.0)
                } else {
                    let is_rec2: bool = native_install::native_is_rec(&q.0.p.kinds);
                    state_c::flush_c(st);
                    match check_native_pass_s(mode, st, fe, p0, is_rec2) {
                        Err(err) => Err(err),
                        Ok(q2) => {
                            if q2.1 {
                                check_native_tail_s(mode, st, fe, q2.0)
                            } else {
                                Err(core_types::internal(core_types::code_points(
                                    &M_SETTLE,
                                )))
                            }
                        }
                    }
                }
            }
        }
    }
}
