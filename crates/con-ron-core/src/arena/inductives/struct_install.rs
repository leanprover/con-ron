//! `arena::inductives::struct_install` — the projection table's checks.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StructInstall.lean`, which
//! is `ConLeche/Kernel/Inductives/StructInstall.lean` whole over handles: the
//! binder-domain walk and the checks of the projection TABLE a structure-like
//! member installs (the table itself is read off the block,
//! `arena::install::block_tables`).
//!
//! **The cached twins collapse into these**: con-leche carries each of this
//! module's two functions twice — the specification over `Env` and the cached
//! driver's twin over `FEnv` (`checkStructDomsAtC`,
//! `ConLeche/Cached/IndBlock.lean`; `checkStructProjTableC`,
//! `ConLeche/Cached/IndTail.lean`).  The arena has ONE environment type and one
//! tier, so the twin is one function citing both.

use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IFEnv, IProjTable};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx};
use crate::arena::monad::{fail, read_level_m, AState};
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::level;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

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
/// `direct structure: projection table before its structure`, as code points.
pub const M_TBL_ORPHAN: [u32; 55] = [
    100, 105, 114, 101, 99, 116, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 58, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 98, 101, 102, 111, 114, 101, 32, 105, 116, 115, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101,
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

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:30-49 checkStructDomsAt
/// con-leche: ConLeche/Cached/IndBlock.lean:117-125 checkStructDomsAtC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:30-44 checkStructDomsAt`
/// — the reference kernels' binder-domain comparisons, run binder by binder
/// **at its own frame**: the `j`-th opened variable's annotation against the
/// `j`-th expected domain, at frame `off + j`.  Walks from the last binder to
/// the first, as the twin's `j + 1` recursion does.
pub fn check_struct_doms_at(
    pers: &PersTier,
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
        let a: Option<EIdx> = if j < fvs.len() as u64 {
            Some(fvs[j as usize].dup2())
        } else {
            None
        };
        let b: Option<EIdx> = if j < doms.len() as u64 {
            Some(doms[j as usize].dup2())
        } else {
            None
        };
        match checker_base::unwrap_or(a, core_types::internal(code_points(&M_DOM_IDX))) {
            Err(e) => Err(e),
            Ok(fv) => {
                match checker_base::unwrap_or(b, core_types::internal(code_points(&M_DOM_IDX))) {
                    Err(e) => Err(e),
                    Ok(dom) => match expr_ops::fvar_type_d(pers, st, &fv) {
                        Err(e) => Err(e),
                        Ok(ty) => match core::is_def_eq_core(
                            pers,
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
                            Ok(true) => check_struct_doms_at(pers, st, mode, fe, off, fvs, doms, j),
                        },
                    },
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The projection table (`StructInstall.lean:42-72` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:51-73 checkStructProjTable
/// con-leche: ConLeche/Cached/IndTail.lean:195-203 checkStructProjTableC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:46-68 checkStructProjTable`
/// — stage 5: **the projection table's checks** (con-leche's task #175 S1),
/// at the table the block installs (`arena::install::block_tables`): its
/// bodies' scoping at its own level parameters and parameter count, validated
/// once (`proj_bodies_scoped`); the table follows its structure, declared by
/// the same block (the structure must be stored, an internal error
/// otherwise), and its name is not yet taken.  Nothing is pushed.
pub fn check_struct_proj_table(
    pers: &PersTier,
    st: &mut AState,
    t: &IProjTable,
    fe: &IFEnv,
) -> Result<(), CheckError> {
    match proj_bodies_scoped(pers, st, fe, &t.level_params, t.num_params, &t.bodies, 0) {
        Err(e) => Err(e),
        Ok(scoped_ok) => {
            if !(t.bodies.len() as u64 == t.num_fields && scoped_ok) {
                fail(core_types::internal(code_points(&M_TBL_SCOPE)))
            } else if env::ifenv_find(pers, fe, &t.struct_name).is_none() {
                fail(core_types::internal(code_points(&M_TBL_ORPHAN)))
            } else if env::ifenv_find_table(pers, fe, &t.struct_name).is_some() {
                fail(core_types::invalid(code_points(&M_TBL_TAKEN)))
            } else {
                Ok(())
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:51-73 checkStructProjTable
/// con-leche: ConLeche/Cached/IndTail.lean:195-203 checkStructProjTableC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:46-68 checkStructProjTable`
/// — the bodies' scoping, validated once at insertion: fvar-free, level
/// parameters within the structure's, resolving, scoped at the parameters and
/// the subject.  **All four conjuncts run for every body**, as the twin's `do`
/// does; the walk stops at the first body that fails, which is `List.allM`.
pub fn proj_bodies_scoped(
    pers: &PersTier,
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
        match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, &b) {
            Err(e) => Err(e),
            Ok(w1) => match checker_base::all_level_params_defined(pers, st, lps, &b) {
                Err(e) => Err(e),
                Ok(w2) => match checker_base::consts_resolve_f_fast(pers, st, fe, &b) {
                    Err(e) => Err(e),
                    Ok(w3) => {
                        match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, n_p + 1, &b) {
                            Err(e) => Err(e),
                            Ok(w4) => {
                                if !w1 && w2 && w3 && w4 {
                                    proj_bodies_scoped(pers, st, fe, lps, n_p, bodies, i + 1)
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

// ---------------------------------------------------------------------------
// The per-field universe bound
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: field index     `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FLD_IDX: [u32; 28] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 102, 105, 101, 108, 100, 32, 105, 110,
    100, 101, 120, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct sum: large eliminator with a non-propositional field             `, as code points — `con_ron_core::kernel::inductives::sum_install`'s own, so the differential test can compare error text.
pub const M_FLD_ELIM: [u32; 72] = [
    100, 105, 114, 101, 99, 116, 32, 115, 117, 109, 58, 32, 108, 97, 114, 103, 101, 32, 101, 108,
    105, 109, 105, 110, 97, 116, 111, 114, 32, 119, 105, 116, 104, 32, 97, 32, 110, 111, 110, 45,
    112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 102, 105, 101, 108, 100,
    32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `a constructor field lives in a larger universe than its inductive type`, as code points.
pub const M_FLD_BIG: [u32; 70] = [
    97, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 102, 105, 101, 108, 100, 32,
    108, 105, 118, 101, 115, 32, 105, 110, 32, 97, 32, 108, 97, 114, 103, 101, 114, 32, 117, 110,
    105, 118, 101, 114, 115, 101, 32, 116, 104, 97, 110, 32, 105, 116, 115, 32, 105, 110, 100, 117,
    99, 116, 105, 118, 101, 32, 116, 121, 112, 101,
];

/// con-leche: none — `xs.contains x` over a `Vec<EIdx>`
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:72-95 checkStructFieldSortsI`
/// — `idxArgs.contains fv`; handles, so `==` is word equality.
pub fn eidx_contains(xs: &Vec<EIdx>, x: &EIdx, i: usize) -> bool {
    if i >= xs.len() {
        false
    } else if xs[i].eq2(x) {
        true
    } else {
        eidx_contains(xs, x, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:75-99 checkStructFieldSortsI
/// con-leche: ConLeche/Cached/IndPositivity.lean:337-353 checkStructFieldSortsIC
/// con-leche: ConLeche/Cached/IndBlock.lean:127-142 checkStructFieldSortsC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:72-95 checkStructFieldSortsI`
/// — every field's domain has a sort over the opened constructor telescope,
/// under the official per-field universe bound unless the family is
/// propositional.  **Walks the fields from the LAST to the first** (the twin's
/// `j + 1` recursion).
#[allow(clippy::too_many_arguments)]
pub fn check_struct_field_sorts_i(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    is_prop: bool,
    large: bool,
    s: &LIdx,
    n_p: u64,
    fvs: &Vec<EIdx>,
    idx_args: &Vec<EIdx>,
    k: u64,
) -> Result<(), CheckError> {
    if k == 0 {
        Ok(())
    } else {
        let j: u64 = k - 1;
        let at: Option<EIdx> = if j < fvs.len() as u64 {
            Some(fvs[j as usize].dup2())
        } else {
            None
        };
        match checker_base::unwrap_or(at, core_types::internal(code_points(&M_FLD_IDX))) {
            Err(e) => Err(e),
            Ok(fv) => match expr_ops::fvar_type_d(pers, st, &fv) {
                Err(e) => Err(e),
                Ok(fvt) => match core::infer_type_core(pers, st, mode, fe, core::CHECK_FUEL, n_p + j, &fvt) {
                    Err(e) => Err(e),
                    Ok(ty) => match core::ensure_sort_core(pers, st, mode, fe, core::CHECK_FUEL, n_p + j, &ty) {
                        Err(e) => Err(e),
                        Ok(u) => match field_sort_bound(pers, st, is_prop, large, s, &u, &fv, idx_args) {
                            Err(e) => Err(e),
                            Ok(()) => check_struct_field_sorts_i(
                                pers, st, mode, fe, is_prop, large, s, n_p, fvs, idx_args, j,
                            ),
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StructInstall.lean:75-99 checkStructFieldSortsI
/// con-leche: ConLeche/Cached/IndPositivity.lean:337-353 checkStructFieldSortsIC
/// Lean twin: `proof/ConRon/Arena/Inductives/StructInstall.lean:72-95 checkStructFieldSortsI`
/// — one field's universe bound: official's `leq` against the family's sort at
/// a non-propositional family, and the large eliminator's escape hatch
/// (`Prop`-valued or an index argument) at a propositional one.
#[allow(clippy::too_many_arguments)]
pub fn field_sort_bound(
    pers: &PersTier,
    st: &mut AState,
    is_prop: bool,
    large: bool,
    s: &LIdx,
    u: &LIdx,
    fv: &EIdx,
    idx_args: &Vec<EIdx>,
) -> Result<(), CheckError> {
    if !is_prop {
        match read_level_m(pers, st, u) {
            Err(e) => Err(e),
            Ok(lu) => match read_level_m(pers, st, s) {
                Err(e) => Err(e),
                Ok(ls) => match core::lift_fueled(level::leq(&lu, &ls)) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_FLD_BIG))),
                    Ok(true) => Ok(()),
                },
            },
        }
    } else if large {
        match core::zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => match core::lvl_eq(pers, st, u, &z) {
                Err(e) => Err(e),
                Ok(eq) => {
                    let zero: bool = match eq {
                        Some(true) => true,
                        Some(false) => false,
                        None => false,
                    };
                    if zero || eidx_contains(idx_args, fv, 0) {
                        Ok(())
                    } else {
                        fail(core_types::invalid(code_points(&M_FLD_ELIM)))
                    }
                }
            },
        }
    } else {
        Ok(())
    }
}
