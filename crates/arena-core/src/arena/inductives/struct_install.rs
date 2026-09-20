//! `arena::inductives::struct_install` — the projection table's checks.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StructInstall.lean`, which
//! is `ConLeche/Kernel/Inductives/StructInstall.lean` whole over handles: the
//! binder-domain walk and the projection TABLE the fixpoint route stores at a
//! structure-like block.
//!
//! **The `…F` twins collapse into these** (task #97c's deviation 1): con-leche
//! carries each of this module's two functions twice — once over `Env` and once
//! over `FEnv` (`ConLeche/Kernel/Inductives/StructInstallF.lean`), and
//! `checkStructDomsAtFA` a third time over `Array`.  The arena has ONE
//! environment type, so the twin is one function citing all of them;
//! `arena::inductives::struct_install_f` carries the `F`-suffixed NAMES as
//! one-line delegations, exactly as `arena::fenv` does for `Core.lean`'s.
//!
//! `StructWalkers` has no twin here either: the arena's `consts_resolve_f_fast`
//! and `struct_proj_bodies` ARE the memoised walks that record exists to
//! substitute, and a record of two closures is what DESIGN.md §3.4 forbids.

use super::ind_base;
use super::struct_parts;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IProjTable};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{fail, AState};
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::ron::hashmap::Dup;

// ---------------------------------------------------------------------------
// The messages (con-ron-core's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct structure: domain index      `, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_DOM_IDX: [u32; 36] = [
    100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 100, 111,
    109, 97, 105, 110, 32, 105, 110, 100, 101, 120, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct structure: binder domain mismatch    `, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_DOM_MIS: [u32; 44] = [
    100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 98, 105,
    110, 100, 101, 114, 32, 100, 111, 109, 97, 105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct structure: projection bodies      `, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_TBL_BODIES: [u32; 41] = [
    100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 112, 114,
    111, 106, 101, 99, 116, 105, 111, 110, 32, 98, 111, 100, 105, 101, 115, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct structure: projection body scoping       `, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_TBL_SCOPE: [u32; 48] = [
    100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 112, 114,
    111, 106, 101, 99, 116, 105, 111, 110, 32, 98, 111, 100, 121, 32, 115, 99, 111, 112, 105, 110,
    103, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection name family taken`, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_TBL_FAM: [u32; 28] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 102, 97, 109, 105,
    108, 121, 32, 116, 97, 107, 101, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection table taken`, as code points — `con_ron_core::kernel::inductives::struct_install`'s own, so the differential test can compare error text.
pub const M_TBL_TAKEN: [u32; 22] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 116, 97, 107,
    101, 110,
];

// ---------------------------------------------------------------------------
// The binder-domain walk (`StructInstall.lean:25-40` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:32-51 checkStructDomsAt
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:27-36 checkStructDomsAtF
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:38-48 checkStructDomsAtFA
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:32-40 checkStructDomsAt`
/// — the reference kernels' binder-domain comparisons, run binder by binder
/// **at its own frame**: the `j`-th opened variable's annotation against the
/// `j`-th expected domain, at frame `off + j`.  Walks from the last binder to
/// the first, as the twin's `j + 1` recursion does.
pub fn check_struct_doms_at(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    off: u64,
    fvs: &Vec<EIdx>,
    doms: &Vec<EIdx>,
    k: u64,
) -> Result<(), CheckError> {
    if k == 0 {
        Ok(())
    } else {
        let j: u64 = k - 1;
        let a: Option<EIdx> = if (j as usize) < fvs.len() {
            Some(fvs[j as usize].dup2())
        } else {
            None
        };
        let b: Option<EIdx> = if (j as usize) < doms.len() {
            Some(doms[j as usize].dup2())
        } else {
            None
        };
        match ind_base::unwrap_or(a, core_types::internal(code_points(&M_DOM_IDX))) {
            Err(e) => Err(e),
            Ok(fv) => match ind_base::unwrap_or(b, core_types::internal(code_points(&M_DOM_IDX))) {
                Err(e) => Err(e),
                Ok(dom) => match expr_ops::fvar_type_d(st, &fv) {
                    Err(e) => Err(e),
                    Ok(ty) => match core::is_def_eq_core(
                        st,
                        mode,
                        fe,
                        core::CHECK_FUEL,
                        off + j,
                        &ty,
                        &dom,
                    ) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::not_implemented(code_points(&M_DOM_MIS))),
                        Ok(true) => check_struct_doms_at(st, mode, fe, off, fvs, doms, j),
                    },
                },
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The projection table (`StructInstall.lean:42-72` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// con-leche: ConLeche/Kernel/Inductives/StructInstallF.lean:73-95 checkStructProjTableF
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:49-72 checkStructProjTable`
/// — stage 5: **the projection table** (con-leche's task #175 S1).  One
/// constant per structure: the fields' result-type bodies read off the
/// *annotated* constructor type by substitution alone, the per-field guard
/// levels, the constructor and the counts.  `IProjTable.table_name` is the
/// reserved name the install interned, kept rather than recomputed
/// (`arena::env`'s one added field).
#[allow(clippy::too_many_arguments)]
pub fn check_struct_proj_table(
    st: &mut AState,
    t: &NIdx,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    res_sort: &LIdx,
    guards: Vec<LIdx>,
    off: u64,
    cv_ca: &IConstantVal,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    match struct_parts::struct_proj_bodies(st, t, n_p, n_f, &cv_ca.ty) {
        Err(e) => Err(e),
        Ok(o) => match ind_base::unwrap_or(o, core_types::internal(code_points(&M_TBL_BODIES))) {
            Err(e) => Err(e),
            Ok(bodies) => match proj_bodies_scoped(st, &fe, lps, n_p, &bodies, 0) {
                Err(e) => Err(e),
                Ok(scoped_ok) => {
                    if !(bodies.len() as u64 == n_f && scoped_ok) {
                        fail(core_types::internal(code_points(&M_TBL_SCOPE)))
                    } else {
                        check_struct_proj_table_names(
                            st, t, c, lps, n_p, n_f, res_sort, guards, off, bodies, fe,
                        )
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:57-61 checkStructProjTable`
/// — the bodies' scoping, validated once at insertion: fvar-free, level
/// parameters within the structure's, resolving, scoped at the parameters and
/// the subject.  **All four conjuncts run for every body**, as the twin's `do`
/// does; the walk stops at the first body that fails, which is `List.allM`.
pub fn proj_bodies_scoped(
    st: &mut AState,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    n_p: u64,
    bodies: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= bodies.len() {
        Ok(true)
    } else {
        let b: EIdx = bodies[i].dup2();
        match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &b) {
            Err(e) => Err(e),
            Ok(w1) => match ind_base::all_level_params_defined(st, lps, &b) {
                Err(e) => Err(e),
                Ok(w2) => match ind_base::consts_resolve_f_fast(st, fe, &b) {
                    Err(e) => Err(e),
                    Ok(w3) => {
                        match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, n_p + 1, &b) {
                            Err(e) => Err(e),
                            Ok(w4) => {
                                if !w1 && w2 && w3 && w4 {
                                    proj_bodies_scoped(st, fe, lps, n_p, bodies, i + 1)
                                } else {
                                    Ok(false)
                                }
                            }
                        }
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:65-72 checkStructProjTable`
/// — the projection-function name family and the table's own reserved name
/// must be free, and then the table is stored.
#[allow(clippy::too_many_arguments)]
pub fn check_struct_proj_table_names(
    st: &mut AState,
    t: &NIdx,
    c: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    res_sort: &LIdx,
    guards: Vec<LIdx>,
    off: u64,
    bodies: Vec<EIdx>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    match proj_fn_family_free(st, &fe, t, n_f, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_TBL_FAM))),
        Ok(true) => match env::proj_table_name(&mut st.store, t) {
            Err(e) => Err(e),
            Ok(tn) => {
                if env::ifenv_find(&fe, &tn).is_some() {
                    fail(core_types::invalid(code_points(&M_TBL_TAKEN)))
                } else {
                    let tbl = IProjTable {
                        struct_name: t.dup2(),
                        table_name: tn,
                        level_params: env::nidx_vec_dup(lps),
                        num_params: n_p,
                        ctor: c.dup2(),
                        num_fields: n_f,
                        struct_sort: res_sort.dup2(),
                        bodies,
                        guards,
                        off,
                    };
                    Ok(env::ifenv_push(fe, IConstantInfo::ProjInfo(tbl)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:53-86 checkStructProjTable
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:66-67 checkStructProjTable`
/// — the `(List.range nF).allM` of the projection-function name family, as a
/// counted recursion.  `arena::inductives::modeled`'s `proj_fn_family_free` is
/// the same test at the modeled route's own call site; the twin writes it out
/// at both.
pub fn proj_fn_family_free(
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if j >= n_f {
        Ok(true)
    } else {
        match env::proj_fn_name(&mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(pn) => {
                if env::ifenv_find(fe, &pn).is_none() {
                    proj_fn_family_free(st, fe, t, n_f, j + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}
