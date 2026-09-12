//! `ConLeche/Kernel/Inductives/StructInstall.lean` and its index-threaded
//! twins `ConLeche/Kernel/Inductives/StructInstallF.lean` — the two
//! strategy-independent stages every direct install shares: the binder-domain
//! comparison run at each binder's own frame, and the projection table.
//!
//! Both `StructInstallF.lean` declarations that are not a twin — the
//! `StructWalkers` record and `StructWalkers.plain` — are cited here and
//! dissolved (`super`'s module note 3).

use crate::cached::core_c;
use crate::cached::state_c::CState;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal, ProjTable};
use crate::kernel::expr::Expr;
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::inductives::checker_local;
use crate::kernel::inductives::struct_parts;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:32-51 checkStructDomsAt
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
/// The reference kernels' binder-domain comparisons, run binder by binder
/// **at its own frame**: the `j`-th opened variable's annotation against the
/// `j`-th expected domain, at frame `off + j`.  Walks from the last binder to
/// the first, as cited.
///
/// The `Array` twin (`checkStructDomsAtFA`, equal to the list one at
/// `List.toArray`) is the same function: the port has one list type.
pub fn check_struct_doms_at(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    off: u64,
    fvs: &Vec<Expr>,
    doms: &Vec<Expr>,
    j: u64,
) -> CheckM<()> {
    const M_IDX: [u32; 36] = [
        100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32,
        100, 111, 109, 97, 105, 110, 32, 105, 110, 100, 101, 120, 32, 32, 32, 32, 32, 32,
    ];
    const M_MIS: [u32; 44] = [
        100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32,
        98, 105, 110, 100, 101, 114, 32, 100, 111, 109, 97, 105, 110, 32, 109, 105, 115, 109,
        97, 116, 99, 104, 32, 32, 32, 32,
    ];
    if j == 0 {
        Ok(())
    } else {
        let i: u64 = j - 1;
        if (i as usize) >= fvs.len() {
            Err(core_types::internal(core_types::code_points(&M_IDX)))
        } else if (i as usize) >= doms.len() {
            Err(core_types::internal(core_types::code_points(&M_IDX)))
        } else {
            let a: Expr = expr_ops::fvar_type_d(&fvs[i as usize]);
            match core_c::defeq(
                mode,
                core_k::check_fuel(),
                st,
                fe,
                off + i,
                &a,
                &doms[i as usize],
            ) {
                Err(err) => Err(err),
                Ok(false) => {
                    Err(core_types::not_implemented(core_types::code_points(&M_MIS)))
                }
                Ok(true) => check_struct_doms_at(mode, st, fe, off, fvs, doms, i),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:50-67 StructWalkers
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:69-71 StructWalkers.plain
/// con-leche: ConLeche/Cached/CheckerC.lean:52-56 structWalkersC
/// The projection table's own body-scoping guard, which is the one place the
/// **walkers record** shows through: `w.resolve fe b` and
/// `w.projBodies T nP nF cty`.  The port calls the two walkers by name —
/// `core_k::consts_resolve` and `struct_parts::struct_proj_bodies`, both
/// memoized — because con-leche's `structWalkersC_eq_plain` says the record is
/// the specification (`super`'s module note 3).  The `(List.range nF).all` of
/// the cited `unless`.
pub fn proj_bodies_scoped_from(
    fe: &FEnv,
    lps: &Vec<Name>,
    n_p: u64,
    bodies: &Vec<Expr>,
    i: usize,
) -> bool {
    if i >= bodies.len() {
        true
    } else if expr_ops::has_fvar(&bodies[i]) {
        false
    } else if !checker_local::all_level_params_defined(lps, &bodies[i]) {
        false
    } else if !core_k::consts_resolve(fe, &bodies[i]) {
        false
    } else if !expr_ops::loose_bvars_bounded(n_p + 1, &bodies[i]) {
        false
    } else {
        proj_bodies_scoped_from(fe, lps, n_p, bodies, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
/// The projection-function name family's freshness test,
/// `(List.range nF).all (fun j => (fe.find? (projFnName T j)).isNone)`.
/// Shared with `Modeled.lean`'s two sites, which spell the same `all`.
pub fn proj_fn_family_free_from(fe: &FEnv, t: &Name, n_f: u64, j: u64) -> bool {
    if j >= n_f {
        true
    } else if fenv::find(fe, &env::proj_fn_name(t, j)).is_some() {
        false
    } else {
        proj_fn_family_free_from(fe, t, n_f, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
/// **The projection table.**  One constant per structure: the fields'
/// result-type bodies read off the *annotated* constructor type by
/// substitution alone (`structProjBodies`), the per-field guard levels, the
/// constructor and the counts.  Nothing is annotated, inferred or pinned
/// here — a `.proj T i e` use instantiates `bodies[i]` at its own arguments
/// after the official `infer_proj` guard test.
///
/// Deviations: the index is threaded by value and returned (task #14's `FEnv`
/// ruling — `fenv::push` is the cited `fe.push`), `Array Expr` is
/// `Vec<Expr>`, and the two `∧`/`all` conjunctions are the helpers above.
pub fn check_struct_proj_table(
    t: &Name,
    c: &Name,
    lps: &Vec<Name>,
    n_p: u64,
    n_f: u64,
    res_sort: &Level,
    guards: Vec<Level>,
    off: u64,
    cv_ca: &ConstantVal,
    fe: FEnv,
) -> CheckM<FEnv> {
    const M_BODIES: [u32; 41] = [
        100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32,
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 98, 111, 100, 105, 101, 115, 32,
        32, 32, 32, 32, 32,
    ];
    const M_SCOPE: [u32; 48] = [
        100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32,
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 98, 111, 100, 121, 32, 115, 99,
        111, 112, 105, 110, 103, 32, 32, 32, 32, 32, 32, 32,
    ];
    const M_FAM: [u32; 28] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 97,
        109, 105, 108, 121, 32, 116, 97, 107, 101, 110,
    ];
    const M_TBL: [u32; 22] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 116,
        97, 107, 101, 110,
    ];
    match struct_parts::struct_proj_bodies(t, n_p, n_f, &cv_ca.ty) {
        None => Err(core_types::internal(core_types::code_points(&M_BODIES))),
        Some(bodies) => {
            let scoped = if bodies.len() as u64 == n_f {
                proj_bodies_scoped_from(&fe, lps, n_p, &bodies, 0)
            } else {
                false
            };
            if !scoped {
                Err(core_types::internal(core_types::code_points(&M_SCOPE)))
            } else if !proj_fn_family_free_from(&fe, t, n_f, 0) {
                Err(core_types::invalid(core_types::code_points(&M_FAM)))
            } else if fenv::find(&fe, &env::proj_table_name(t)).is_some() {
                Err(core_types::invalid(core_types::code_points(&M_TBL)))
            } else {
                Ok(fenv::push(
                    fe,
                    ConstantInfo::ProjInfo(ProjTable {
                        struct_name: name::dup(t),
                        level_params: prop_when::names_copy(lps),
                        num_params: n_p,
                        ctor: name::dup(c),
                        num_fields: n_f,
                        struct_sort: crate::kernel::level::dup(res_sort),
                        bodies,
                        guards,
                        off,
                    }),
                ))
            }
        }
    }
}
