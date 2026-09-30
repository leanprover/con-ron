//! `arena::inductives::rec_check` — the recursor stage's class kit.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/RecCheck.lean`, which is
//! `ConLeche/Kernel/Inductives/RecCheck.lean` over handles: the member
//! abstraction (`targetAbs`), the per-component class match
//! (`targetClassMatch`) and the table entries it selects (`targetMajorNfs`),
//! a class resolved from a major (`targetMajorOf`) and typed
//! (`targetMajorPins`), the recursor records' pins (`targetRecPins`), node
//! agreement (`targetK53`), and the stored family's rules (`tgtStoredRules`,
//! `consBlockRecsTF`) with the container bit (`blockNestedBit`).
//!
//! ## The twin's deviations
//!
//! * **`ShadowOps` is not a record**: con-leche writes the stage against a
//!   record of operations per index so that the pure install and the cached
//!   fold run the same code; the arena has one core and one environment
//!   representation, so the operations are `arena::core`'s entry points at
//!   the `IFEnv` and visibility bound they are handed, and the cached
//!   driver's flushes are where `shadowOpsC` puts them (in
//!   `arena::inductives::gen_rec`).  `ShadowOps`, `ShadowOps.ofOps` and
//!   `ShadowOps.fueled` are on the skip list.
//! * **`targetAbs` is ONE memoised walk** (`targetAbs`, `targetAbsGo` and
//!   `targetAbsFast` collapse), as `arena::inductives::positivity`'s walks.
//! * **A function argument is specialised**: `targetParamsDefEq`'s `absM` is
//!   always `targetAbs names lvls holes` (its one caller), `tgtStoredRules`'
//!   `find?`/`resolves` are the constructors' environment at its visibility
//!   bound, `eraseFVarTys`/`targetCanonParams` are `positivity::FvMap`
//!   variants.
//! * **`tgtRs` is not ported**: nothing the executed checker runs reads the
//!   install's old recursor-list format.
//! * **`tgtStoredRules`' fire is computed once per recursor**: con-leche's
//!   `rules.map fun rl => { rl with fire := auxRuleFireR … }` recomputes the
//!   same pure reading per rule.

use super::block_parts;
use super::block_parts::{shape_k, shape_lps, shape_member_names, BlockShape, RecShape};
use super::positivity;
use super::positivity::{
    eidx_get, inst_pis_with, memo_e_probe, names_find_idx, nest_container, nest_kinds_flat,
    nest_occ, nest_occ_any, params_closed, replace_fvars, FvMap, NestCtorNf, NestFieldKind,
};
use super::struct_parts;
use super::sum_install;
use super::field_tele::pi_binders;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LsIdx, NIdx, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::monad::{
    fail, fail_dangling_e, intern_e_app, intern_e_const, intern_e_forall_e, intern_e_fvar, intern_e_lam,
    intern_e_let_e, intern_e_proj, intern_n_node, view, view_bind, view_const, AState,
};
use crate::arena::pins::pin_quot;
use crate::arena::store::{ENodeView, NNodeView, PersTier};
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::hashmap2::HashMap2 as HashMap;

// ---------------------------------------------------------------------------
// The messages (con-leche's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: targetAbs`, as code points.
pub const M_FUEL_TARGET_ABS: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 116, 97, 114, 103,
    101, 116, 65, 98, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major is not a stored inductive`, as code points.
pub const M_NOT_STORED: [u32; 58] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 105, 115, 32, 110, 111, 116, 32,
    97, 32, 115, 116, 111, 114, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the major's type former does not bind its parameters (official: ill-formed inductive type)`, as code points.
pub const M_NO_PARAMS: [u32; 102] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 109, 97, 106, 111,
    114, 39, 115, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101, 114, 32, 100, 111, 101, 115,
    32, 110, 111, 116, 32, 98, 105, 110, 100, 32, 105, 116, 115, 32, 112, 97, 114, 97, 109, 101,
    116, 101, 114, 115, 32, 40, 111, 102, 102, 105, 99, 105, 97, 108, 58, 32, 105, 108, 108, 45,
    102, 111, 114, 109, 101, 100, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121,
    112, 101, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the major's type former is not a telescope ending in a sort (official: type expected)`, as code points.
pub const M_NOT_SORT: [u32; 97] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 109, 97, 106, 111,
    114, 39, 115, 32, 116, 121, 112, 101, 32, 102, 111, 114, 109, 101, 114, 32, 105, 115, 32, 110,
    111, 116, 32, 97, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 101, 110, 100, 105, 110,
    103, 32, 105, 110, 32, 97, 32, 115, 111, 114, 116, 32, 40, 111, 102, 102, 105, 99, 105, 97,
    108, 58, 32, 116, 121, 112, 101, 32, 101, 120, 112, 101, 99, 116, 101, 100, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: member`, as code points.
pub const M_MEMBER: [u32; 18] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 109, 101, 109, 98, 101, 114,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: member constructors`, as code points.
pub const M_MEMBER_CTORS: [u32; 31] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 109, 101, 109, 98, 101, 114, 32, 99,
    111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major premise is not the member at its parameters and its index binders`, as code points.
pub const M_MEMBER_AT: [u32; 98] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101,
    32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 109, 101, 109, 98, 101, 114, 32, 97,
    116, 32, 105, 116, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 110, 100,
    32, 105, 116, 115, 32, 105, 110, 100, 101, 120, 32, 98, 105, 110, 100, 101, 114, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major is Quot, which is no inductive`, as code points.
pub const M_QUOT: [u32; 63] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 105, 115, 32, 81, 117, 111, 116,
    44, 32, 119, 104, 105, 99, 104, 32, 105, 115, 32, 110, 111, 32, 105, 110, 100, 117, 99, 116,
    105, 118, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the major's parameters mention more than the recursor's parameters`, as code points.
pub const M_MAJOR_PARAMS: [u32; 78] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 109, 97, 106, 111,
    114, 39, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 109, 101, 110, 116, 105,
    111, 110, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 114, 101, 99,
    117, 114, 115, 111, 114, 39, 115, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major is an outside inductive at an instantiation that is no auxiliary type of the block (official generates no such auxiliary recursor: 'elim_nested_inductive', 'is_nested')`, as code points.
pub const M_NO_AUX: [u32; 201] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 105, 115, 32, 97, 110, 32, 111,
    117, 116, 115, 105, 100, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 97, 116, 32,
    97, 110, 32, 105, 110, 115, 116, 97, 110, 116, 105, 97, 116, 105, 111, 110, 32, 116, 104, 97,
    116, 32, 105, 115, 32, 110, 111, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 116, 121,
    112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 40, 111, 102, 102,
    105, 99, 105, 97, 108, 32, 103, 101, 110, 101, 114, 97, 116, 101, 115, 32, 110, 111, 32, 115,
    117, 99, 104, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 114, 101, 99, 117, 114, 115,
    111, 114, 58, 32, 96, 101, 108, 105, 109, 95, 110, 101, 115, 116, 101, 100, 95, 105, 110, 100,
    117, 99, 116, 105, 118, 101, 96, 44, 32, 96, 105, 115, 95, 110, 101, 115, 116, 101, 100, 96,
    41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major lives in another universe than the block (Q1)`, as code points.
pub const M_Q1: [u32; 78] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 108, 105, 118, 101, 115, 32, 105,
    110, 32, 97, 110, 111, 116, 104, 101, 114, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 116,
    104, 97, 110, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 40, 81, 49, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's major premise is not an inductive's application`, as code points.
pub const M_NOT_APP: [u32; 74] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 109, 97, 106, 111, 114, 32, 112, 114, 101, 109, 105, 115, 101,
    32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101,
    39, 115, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor's level parameters are not the generated ones`, as code points.
pub const M_REC_LPS: [u32; 70] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 39, 115, 32, 108, 101, 118, 101, 108, 32, 112, 97, 114, 97, 109, 101, 116,
    101, 114, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101,
    114, 97, 116, 101, 100, 32, 111, 110, 101, 115,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: a recursor is named for a pinned basis constant, a literal guard's slot or a certified Nat operation`, as code points.
pub const M_REC_RESERVED: [u32; 112] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 97, 32, 114, 101, 99, 117, 114, 115,
    111, 114, 32, 105, 115, 32, 110, 97, 109, 101, 100, 32, 102, 111, 114, 32, 97, 32, 112, 105,
    110, 110, 101, 100, 32, 98, 97, 115, 105, 115, 32, 99, 111, 110, 115, 116, 97, 110, 116, 44,
    32, 97, 32, 108, 105, 116, 101, 114, 97, 108, 32, 103, 117, 97, 114, 100, 39, 115, 32, 115,
    108, 111, 116, 32, 111, 114, 32, 97, 32, 99, 101, 114, 116, 105, 102, 105, 101, 100, 32, 78,
    97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the block's recursor names are not the generated ones (one T.rec per member)`, as code points.
pub const M_REC_NAMES: [u32; 88] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 98, 108, 111, 99,
    107, 39, 115, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 110, 97, 109, 101, 115, 32, 97,
    114, 101, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100,
    32, 111, 110, 101, 115, 32, 40, 111, 110, 101, 32, 84, 46, 114, 101, 99, 32, 112, 101, 114, 32,
    109, 101, 109, 98, 101, 114, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the block's auxiliary recursor names are not the generated ones (T.rec_1 … T.rec_n)`, as code points.
pub const M_AUX_NAMES: [u32; 95] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 98, 108, 111, 99,
    107, 39, 115, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 114, 101, 99, 117, 114, 115,
    111, 114, 32, 110, 97, 109, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101,
    32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 115, 32, 40, 84, 46, 114,
    101, 99, 95, 49, 32, 8230, 32, 84, 46, 114, 101, 99, 95, 110, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: two recursors of the block share a name`, as code points.
pub const M_REC_DUP: [u32; 51] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 119, 111, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 115, 32, 111, 102, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 115,
    104, 97, 114, 101, 32, 97, 32, 110, 97, 109, 101,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the recursor record is not the generated recursor (constructor grouping)`, as code points.
pub const M_GROUPING: [u32; 84] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 114, 101, 99, 111, 114, 100, 32, 105, 115, 32, 110, 111, 116, 32, 116,
    104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111,
    114, 32, 40, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 103, 114, 111, 117, 112,
    105, 110, 103, 41,
];
/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `target rec: the block does not split`, as code points.
pub const M_NO_SPLIT: [u32; 36] = [
    116, 97, 114, 103, 101, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 98, 108, 111, 99,
    107, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 112, 108, 105, 116,
];

// ---------------------------------------------------------------------------
// The holes: the block's members abstracted to free variables
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:89-109 targetAbs
/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:130-170 targetAbsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetAbsGo` — **the
/// member abstraction of one term**: every member at the block's levels
/// `lvls` becomes its hole; `fvar` annotations are not entered.  Memoised on
/// the node.
pub fn target_abs_go(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    holes: &Vec<EIdx>,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_TARGET_ABS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Sort(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Lit(_)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::FVar(_, _)) => Ok((h.dup2(), memo)),
            Ok(ENodeView::Const(n, us)) => {
                if us.eq2(lvls) {
                    match names_find_idx(names, &n, 0) {
                        Some(t) => match eidx_get(holes, t) {
                            Some(x) => Ok((x, memo)),
                            None => Ok((h.dup2(), memo)),
                        },
                        None => Ok((h.dup2(), memo)),
                    }
                } else {
                    Ok((h.dup2(), memo))
                }
            }
            Ok(v) => match memo_e_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match target_abs_node(pers, st, names, lvls, holes, memo, fuel - 1, h, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, EIdx> = m;
                        m2.insert(h.dup2(), r.dup2());
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:130-170 targetAbsGo
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetAbsGo` — the
/// walk's compound arms, each rebuilt.
#[allow(clippy::too_many_arguments)]
pub fn target_abs_node(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    holes: &Vec<EIdx>,
    memo: HashMap<EIdx, EIdx>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(EIdx, HashMap<EIdx, EIdx>), CheckError> {
    match v {
        ENodeView::App(a, b) => match target_abs_go(pers, st, names, lvls, holes, memo, fuel, &a) {
            Err(e) => Err(e),
            Ok((a2, m)) => match target_abs_go(pers, st, names, lvls, holes, m, fuel, &b) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_app(pers, st, a2, b2) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::Lam(ty, body, bm) => match target_abs_go(pers, st, names, lvls, holes, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((t2, m)) => match target_abs_go(pers, st, names, lvls, holes, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match intern_e_lam(pers, st, t2, b2, bm) {
                    Err(e) => Err(e),
                    Ok(r) => Ok((r, m2)),
                },
            },
        },
        ENodeView::ForallE(ty, body, bm) => {
            match target_abs_go(pers, st, names, lvls, holes, memo, fuel, &ty) {
                Err(e) => Err(e),
                Ok((t2, m)) => match target_abs_go(pers, st, names, lvls, holes, m, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m2)) => match intern_e_forall_e(pers, st, t2, b2, bm) {
                        Err(e) => Err(e),
                        Ok(r) => Ok((r, m2)),
                    },
                },
            }
        }
        ENodeView::LetE(ty, val, body) => match target_abs_go(pers, st, names, lvls, holes, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((t2, m)) => match target_abs_go(pers, st, names, lvls, holes, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((v2, m2)) => match target_abs_go(pers, st, names, lvls, holes, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b2, m3)) => match intern_e_let_e(pers, st, t2, v2, b2) {
                        Err(e) => Err(e),
                        Ok(r) => Ok((r, m3)),
                    },
                },
            },
        },
        ENodeView::Proj(s, i, sub) => match target_abs_go(pers, st, names, lvls, holes, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok((u, m)) => match intern_e_proj(pers, st, s, i, u) {
                Err(e) => Err(e),
                Ok(r) => Ok((r, m)),
            },
        },
        _ => Ok((h.dup2(), memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:240-242 targetAbsFast
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetAbs` — the
/// executed member abstraction (one memoised DAG walk).
pub fn target_abs(
    pers: &PersTier,
    st: &mut AState,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    holes: &Vec<EIdx>,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match target_abs_go(pers, st, names, lvls, holes, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:248-251 targetHoles
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetHoles` — the
/// holes of a rule frame of width `base`: member `t` is `.fvar (base + t)` at
/// its former's type.
pub fn target_holes(
    pers: &PersTier,
    st: &mut AState,
    former_tys: &Vec<EIdx>,
    base: u64,
    t: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if t >= former_tys.len() {
        Ok(out)
    } else {
        match intern_e_fvar(pers, st, base + (t as u64), former_tys[t].dup2()) {
            Err(e) => Err(e),
            Ok(v) => {
                let mut o: Vec<EIdx> = out;
                o.push(v);
                target_holes(pers, st, former_tys, base, t + 1, o)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The major
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean TargetMajor` — **a
/// recursor's major, resolved**: `ind.{lvls} ds ı⃗`, its parameter and index
/// counts at the instantiation, its constructors, the member it is (`none`:
/// an outside inductive), the table's entries for its constructors and the
/// recursor prefix's openers it is compared in.
pub struct TargetMajor {
    pub ind: NIdx,
    pub lvls: LsIdx,
    pub ds: Vec<EIdx>,
    pub n_pc: u64,
    pub n_idx: u64,
    pub ctors: Vec<(IConstantVal, u64)>,
    pub member: Option<u64>,
    pub nfs: Vec<NestCtorNf>,
    pub pfvs: Vec<EIdx>,
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
/// The record copy.
pub fn target_major_dup(m: &TargetMajor) -> TargetMajor {
    TargetMajor {
        ind: m.ind.dup2(),
        lvls: m.lvls.dup2(),
        ds: env::eidx_vec_dup(&m.ds),
        n_pc: m.n_pc,
        n_idx: m.n_idx,
        ctors: block_parts::ctors_dup(&m.ctors, 0, Vec::new()),
        member: match m.member {
            Some(t) => Some(t),
            None => None,
        },
        nfs: positivity::nest_ctor_nfs_dup(&m.nfs, 0, Vec::new()),
        pfvs: env::eidx_vec_dup(&m.pfvs),
    }
}

/// con-leche: none — a `List TargetMajor` copy; Lean shares the list
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean TargetMajor`.
pub fn target_majors_dup(ms: &Vec<TargetMajor>, i: usize, out: Vec<TargetMajor>) -> Vec<TargetMajor> {
    if i >= ms.len() {
        out
    } else {
        let mut o: Vec<TargetMajor> = out;
        o.push(target_major_dup(&ms[i]));
        target_majors_dup(ms, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
/// Lean twin: the cited `deriving Inhabited` default, `Ms.getD c default`'s
/// fallback: the anonymous inductive at no level and no parameter.  Only an
/// out-of-range class index reads it, which the stage never forms.
pub fn target_major_default(pers: &PersTier, st: &mut AState) -> Result<TargetMajor, CheckError> {
    match intern_n_node(pers, st, NNodeView::Anonymous) {
        Err(e) => Err(e),
        Ok(anon) => match crate::arena::pins::pin_empty_levels(st) {
            Err(e) => Err(e),
            Ok(ls) => Ok(TargetMajor {
                ind: anon,
                lvls: ls,
                ds: Vec::new(),
                n_pc: 0,
                n_idx: 0,
                ctors: Vec::new(),
                member: None,
                nfs: Vec::new(),
                pfvs: Vec::new(),
            }),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:255-275 TargetMajor
/// Lean twin: `Ms.getD c default`.
pub fn target_major_at(pers: &PersTier, st: &mut AState, ms: &Vec<TargetMajor>, c: u64) -> Result<TargetMajor, CheckError> {
    if c < ms.len() as u64 {
        Ok(target_major_dup(&ms[c as usize]))
    } else {
        target_major_default(pers, st)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:277-281 Expr.eraseFVarTys
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean eraseFVarTys` — a term
/// with every free variable's ANNOTATION erased (the variable kept at `Sort
/// 0`).
pub fn erase_fvar_tys(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<EIdx, CheckError> {
    let f: FvMap = FvMap::Erase;
    replace_fvars(pers, st, &f, e)
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:305-308 targetCanonParams
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetCanonParams` — a
/// term over the walk's canonical parameter variables, moved to the class's
/// openers `pfvs` (variables `0 … |pfvs|-1`, the rest kept).
pub fn target_canon_params(pers: &PersTier, st: &mut AState, pfvs: &Vec<EIdx>, e: &EIdx) -> Result<EIdx, CheckError> {
    let f: FvMap = FvMap::Canon(env::eidx_vec_dup(pfvs));
    replace_fvars(pers, st, &f, e)
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:310-329 targetParamsDefEq
/// Lean twin: `a.bvarB == 0 && b.bvarB == 0 && a.fvarB ≤ n && b.fvarB ≤ n` —
/// the two sides are closed over the openers, the four reads in order.
pub fn pair_closed(pers: &PersTier, st: &mut AState, a: &EIdx, b: &EIdx, n: u64) -> Result<bool, CheckError> {
    match expr_ops::bvar_b(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(ba) => {
            if ba != 0 {
                Ok(false)
            } else {
                match expr_ops::bvar_b(pers, st, CORE_WALK_FUEL, b) {
                    Err(e) => Err(e),
                    Ok(bb) => {
                        if bb != 0 {
                            Ok(false)
                        } else {
                            match expr_ops::fvar_b(pers, st, CORE_WALK_FUEL, a) {
                                Err(e) => Err(e),
                                Ok(fa) => {
                                    if fa > n {
                                        Ok(false)
                                    } else {
                                        match expr_ops::fvar_b(pers, st, CORE_WALK_FUEL, b) {
                                            Err(e) => Err(e),
                                            Ok(fb) => Ok(fb <= n),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:310-329 targetParamsDefEq
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetParamsDefEq` —
/// **per-component parameter defeq** at depth `d`, each side moved to the
/// openers and member-abstracted (`absM` is `targetAbs names lvls holes`, its
/// one instantiation): syntactically equal, or inferred and defeq.
#[allow(clippy::too_many_arguments)]
pub fn target_params_def_eq(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    d: u64,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    holes: &Vec<EIdx>,
    pfvs: &Vec<EIdx>,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= xs.len() && i >= ys.len() {
        Ok(true)
    } else if i >= xs.len() || i >= ys.len() {
        Ok(false)
    } else {
        let a: EIdx = xs[i].dup2();
        let b: EIdx = ys[i].dup2();
        match pair_closed(pers, st, &a, &b, pfvs.len() as u64) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match target_canon_params(pers, st, pfvs, &a) {
                Err(e) => Err(e),
                Ok(ac) => match target_abs(pers, st, names, lvls, holes, &ac) {
                    Err(e) => Err(e),
                    Ok(a2) => match target_canon_params(pers, st, pfvs, &b) {
                        Err(e) => Err(e),
                        Ok(bc) => match target_abs(pers, st, names, lvls, holes, &bc) {
                            Err(e) => Err(e),
                            Ok(b2) => {
                                if a2.eq2(&b2) {
                                    target_params_def_eq(pers, st, mode, vis, fe, d, names, lvls, holes, pfvs, xs, ys, i + 1)
                                } else {
                                    target_params_def_eq_infer(
                                        pers, st, mode, vis, fe, d, names, lvls, holes, pfvs, xs, ys, i, &a2, &b2,
                                    )
                                }
                            }
                        },
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:310-329 targetParamsDefEq
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetParamsDefEq` —
/// the two sides not syntactically equal: both inferred at `d`, then compared
/// by the kernel's defeq.
#[allow(clippy::too_many_arguments)]
pub fn target_params_def_eq_infer(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    d: u64,
    names: &Vec<NIdx>,
    lvls: &LsIdx,
    holes: &Vec<EIdx>,
    pfvs: &Vec<EIdx>,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
    i: usize,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, d, a2) {
        Err(e) => Err(e),
        Ok(_) => match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, d, b2) {
            Err(e) => Err(e),
            Ok(_) => match core::is_def_eq_core(pers, vis, st, mode, fe, core::CHECK_FUEL, d, a2, b2) {
                Err(e) => Err(e),
                Ok(true) => target_params_def_eq(pers, st, mode, vis, fe, d, names, lvls, holes, pfvs, xs, ys, i + 1),
                Ok(false) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:331-340 targetClassMatch
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetClassMatch` — **a
/// class matches a recorded instantiation `(lvls, eds)`**: levels up to
/// `Level.isEquivList` (an exhausted comparison is no match), parameters
/// pairwise defeq with the members abstracted, over the class's recursor
/// prefix `pfvs` with the holes on top.
#[allow(clippy::too_many_arguments)]
pub fn target_class_match(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    pfvs: &Vec<EIdx>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    lvls: &LsIdx,
    eds: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match core::lvls_eq(pers, st, us, lvls) {
        Err(e) => Err(e),
        Ok(Some(true)) => {
            let names: Vec<NIdx> = shape_member_names(p);
            match struct_parts::param_levels(pers, st, &shape_lps(p)) {
                Err(e) => Err(e),
                Ok(blvls) => match target_holes(pers, st, former_tys, pfvs.len() as u64, 0, Vec::new()) {
                    Err(e) => Err(e),
                    Ok(holes) => target_params_def_eq(
                        pers,
                        st,
                        mode,
                        vis,
                        fe,
                        (pfvs.len() + former_tys.len()) as u64,
                        &names,
                        &blvls,
                        &holes,
                        pfvs,
                        ds,
                        eds,
                        0,
                    ),
                },
            }
        }
        Ok(_) => Ok(false),
    }
}

/// con-leche: none — `ctors.any (·.1.name == c)`
/// Lean twin: the class's constructors name `c`.
pub fn ctors_name(cs: &Vec<(IConstantVal, u64)>, c: &NIdx, i: usize) -> bool {
    if i >= cs.len() {
        false
    } else if cs[i].0.name.eq2(c) {
        true
    } else {
        ctors_name(cs, c, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:342-354 targetMajorNfs
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorNfs` — **the
/// walk's recorded constructor normal forms of a class**: the entries of
/// the class's constructors whose instantiation the class matches.  The
/// cited recursion computes the tail FIRST, so the entries are examined
/// from the LAST to the first; the walk counts `i` down over the table,
/// collecting in reverse, and the result is reversed back.
#[allow(clippy::too_many_arguments)]
pub fn target_major_nfs_rev(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    pfvs: &Vec<EIdx>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    ctors: &Vec<(IConstantVal, u64)>,
    tbl: &Vec<NestCtorNf>,
    i: usize,
    acc: Vec<NestCtorNf>,
) -> Result<Vec<NestCtorNf>, CheckError> {
    if i == 0 {
        Ok(acc)
    } else {
        let e: NestCtorNf = positivity::nest_ctor_nf_dup(&tbl[i - 1]);
        if ctors_name(ctors, &e.ctor, 0) {
            match target_class_match(pers, st, mode, vis, fe, p, former_tys, pfvs, us, ds, &e.lvls, &e.ds) {
                Err(er) => Err(er),
                Ok(true) => {
                    let mut a: Vec<NestCtorNf> = acc;
                    a.push(e);
                    target_major_nfs_rev(pers, st, mode, vis, fe, p, former_tys, pfvs, us, ds, ctors, tbl, i - 1, a)
                }
                Ok(false) => {
                    target_major_nfs_rev(pers, st, mode, vis, fe, p, former_tys, pfvs, us, ds, ctors, tbl, i - 1, acc)
                }
            }
        } else {
            target_major_nfs_rev(pers, st, mode, vis, fe, p, former_tys, pfvs, us, ds, ctors, tbl, i - 1, acc)
        }
    }
}

/// con-leche: none — `List.reverse` on a normal-form list
/// Lean twin: the entries in table order.
pub fn nfs_reverse(xs: &Vec<NestCtorNf>, i: usize, out: Vec<NestCtorNf>) -> Vec<NestCtorNf> {
    if i == 0 {
        out
    } else {
        let mut o: Vec<NestCtorNf> = out;
        o.push(positivity::nest_ctor_nf_dup(&xs[i - 1]));
        nfs_reverse(xs, i - 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:342-354 targetMajorNfs
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorNfs` — the
/// entry: the table from its end, the result in table order.
#[allow(clippy::too_many_arguments)]
pub fn target_major_nfs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    pfvs: &Vec<EIdx>,
    us: &LsIdx,
    ds: &Vec<EIdx>,
    ctors: &Vec<(IConstantVal, u64)>,
    tbl: &Vec<NestCtorNf>,
) -> Result<Vec<NestCtorNf>, CheckError> {
    match target_major_nfs_rev(pers, st, mode, vis, fe, p, former_tys, pfvs, us, ds, ctors, tbl, tbl.len(), Vec::new()) {
        Err(e) => Err(e),
        Ok(rev) => Ok(nfs_reverse(&rev, rev.len(), Vec::new())),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:356-360 targetCtorsOf
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetCtorsOf` — the
/// constructors of a stored inductive `I` and its parameter count
/// (`nestContainer`'s reading, which reads nothing of its context but the
/// lookup).
pub fn target_ctors_of(
    pers: &PersTier,
    st: &AState,
    vis: u64,
    fe: &IFEnv,
    i_name: &NIdx,
) -> Result<Option<(u64, Vec<(IConstantVal, u64)>)>, CheckError> {
    nest_container(pers, st, vis, fe, i_name)
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:362-376 targetOutsideInst
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetOutsideInst` —
/// the instantiated type former of an OUTSIDE major `I.{us} ds`: its index
/// count and its result sort.
pub fn target_outside_inst(
    pers: &PersTier,
    st: &mut AState,
    vis: u64,
    fe: &IFEnv,
    i_name: &NIdx,
    us: &LsIdx,
    ds: &Vec<EIdx>,
) -> Result<(u64, crate::arena::handle::LIdx), CheckError> {
    match positivity::ind_cv_of(vis, fe, i_name) {
        None => fail(core_types::invalid(code_points(&M_NOT_STORED))),
        Some(cv_i) => match expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv_i.level_params, us, &cv_i.ty) {
            Err(e) => Err(e),
            Ok(tl) => match inst_pis_with(pers, st, ds, 0, &tl) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::invalid(code_points(&M_NO_PARAMS))),
                Ok(Some(ty)) => match pi_binders(pers, st, CORE_WALK_FUEL, &ty, Vec::new()) {
                    Err(e) => Err(e),
                    Ok((ibs, s)) => match view(pers, st, &s) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Sort(l)) => Ok((ibs.len() as u64, l)),
                        Ok(_) => fail(core_types::invalid(code_points(&M_NOT_SORT))),
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// A recursor's class, resolved
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorOf` — **a
/// recursor's major, resolved** from its opened type `mty`: a MEMBER of the
/// block at the block's levels and parameters, or — a nested block's
/// container — any other stored inductive at one of the block's auxiliary
/// types.
#[allow(clippy::too_many_arguments)]
pub fn target_major_of(
    pers: &PersTier,
    st: &mut AState,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    ctors_as: &Vec<Vec<(IConstantVal, u64)>>,
    pfvs: &Vec<EIdx>,
    fvs: &Vec<EIdx>,
    mty: &EIdx,
) -> Result<TargetMajor, CheckError> {
    match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, mty) {
        Err(e) => Err(e),
        Ok(args) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, mty) {
            Err(e) => Err(e),
            Ok(hd) => {
                if hd.tag() == ETAG_CONST {
                    match view_const(pers, st, &hd) {
                        None => fail_dangling_e(),
                        Some((i_name, us)) => {
                            let names: Vec<NIdx> = shape_member_names(p);
                            match names_find_idx(&names, &i_name, 0) {
                                Some(t) => target_major_member(pers, st, p, ctors_as, pfvs, fvs, &args, i_name, us, t),
                                None => target_major_outside(pers, st, vis, fe, p, pfvs, &args, i_name, us),
                            }
                        }
                    }
                } else {
                    fail(core_types::invalid(code_points(&M_NOT_APP)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorOf` — a
/// MEMBER `t`: at the block's levels and parameters.
#[allow(clippy::too_many_arguments)]
pub fn target_major_member(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    ctors_as: &Vec<Vec<(IConstantVal, u64)>>,
    pfvs: &Vec<EIdx>,
    fvs: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i_name: NIdx,
    us: LsIdx,
    t: u64,
) -> Result<TargetMajor, CheckError> {
    if t >= p.members.len() as u64 {
        fail(core_types::internal(code_points(&M_MEMBER)))
    } else if t >= ctors_as.len() as u64 {
        fail(core_types::internal(code_points(&M_MEMBER_CTORS)))
    } else {
        let n_idx: u64 = p.members[t as usize].n_idx;
        let ctors_a: Vec<(IConstantVal, u64)> = block_parts::ctors_dup(&ctors_as[t as usize], 0, Vec::new());
        match struct_parts::param_levels(pers, st, &shape_lps(p)) {
            Err(e) => Err(e),
            Ok(blvls) => {
                let pa: Vec<EIdx> = expr_ops::take_eidx_n(args, p.n_p);
                let pf: Vec<EIdx> = expr_ops::take_eidx_n(fvs, p.n_p);
                if us.eq2(&blvls) && crate::arena::canon::eidx_vec_beq(&pa, &pf, 0) {
                    Ok(TargetMajor {
                        ind: i_name,
                        lvls: us,
                        ds: pf,
                        n_pc: p.n_p,
                        n_idx,
                        ctors: ctors_a,
                        member: Some(t),
                        nfs: Vec::new(),
                        pfvs: env::eidx_vec_dup(pfvs),
                    })
                } else {
                    fail(core_types::invalid(code_points(&M_MEMBER_AT)))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorOf` — an
/// OUTSIDE inductive: not `Quot`, stored, its parameters closed over the
/// recursor's, an auxiliary type of the block (some parameter names a
/// member), in the block's universe (Q1).
#[allow(clippy::too_many_arguments)]
pub fn target_major_outside(
    pers: &PersTier,
    st: &mut AState,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    pfvs: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i_name: NIdx,
    us: LsIdx,
) -> Result<TargetMajor, CheckError> {
    match pin_quot(st) {
        Err(e) => Err(e),
        Ok(q) => {
            if i_name.eq2(&q) {
                fail(core_types::invalid(code_points(&M_QUOT)))
            } else {
                match target_ctors_of(pers, st, vis, fe, &i_name) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::invalid(code_points(&M_NOT_STORED))),
                    Ok(Some((n_pc, ctors))) => {
                        let ds: Vec<EIdx> = expr_ops::take_eidx_n(args, n_pc);
                        if ds.len() as u64 != n_pc {
                            fail(core_types::invalid(code_points(&M_MAJOR_PARAMS)))
                        } else {
                            match params_closed(pers, st, &ds, p.n_p, 0) {
                                Err(e) => Err(e),
                                Ok(false) => fail(core_types::invalid(code_points(&M_MAJOR_PARAMS))),
                                Ok(true) => target_major_outside_aux(pers, st, vis, fe, p, pfvs, i_name, us, ds, n_pc, ctors),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:380-439 targetMajorOf
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorOf` — the
/// auxiliary-type test (`nestOcc` at an empty hole range, no whnf, no
/// annotation entered) and Q1.
#[allow(clippy::too_many_arguments)]
pub fn target_major_outside_aux(
    pers: &PersTier,
    st: &mut AState,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    pfvs: &Vec<EIdx>,
    i_name: NIdx,
    us: LsIdx,
    ds: Vec<EIdx>,
    n_pc: u64,
    ctors: Vec<(IConstantVal, u64)>,
) -> Result<TargetMajor, CheckError> {
    let names: Vec<NIdx> = shape_member_names(p);
    match nest_occ_any(pers, st, &names, 0, 0, &ds, 0) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_NO_AUX))),
        Ok(true) => match target_outside_inst(pers, st, vis, fe, &i_name, &us, &ds) {
            Err(e) => Err(e),
            Ok((n_idx, s_i)) => match core::lvl_eq(pers, st, &s_i, &p.res_sort) {
                Err(e) => Err(e),
                Ok(o) => match core::lift_fueled(o) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_Q1))),
                    Ok(true) => Ok(TargetMajor {
                        ind: i_name,
                        lvls: us,
                        ds,
                        n_pc,
                        n_idx,
                        ctors,
                        member: None,
                        nfs: Vec::new(),
                        pfvs: env::eidx_vec_dup(pfvs),
                    }),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:441-458 targetPinTys
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetPinTys` — **an
/// outside major's parameters, typed at the rule prefix** (depth `d`), in
/// order.
#[allow(clippy::too_many_arguments)]
pub fn target_pin_tys(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    d: u64,
    xs: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() {
        Ok(())
    } else {
        let x: EIdx = xs[i].dup2();
        match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, d, &x) {
            Err(e) => Err(e),
            Ok(_) => target_pin_tys(pers, st, mode, vis, fe, d, xs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:460-476 targetMajorPins
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetMajorPins` — the
/// check at a resolved major: an outside major's parameters typed at the rule
/// prefix, and the instantiation `I.{us} D⃗` itself typed there.  Nothing at
/// a member.
pub fn target_major_pins(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    r_p: u64,
    m: &TargetMajor,
) -> Result<(), CheckError> {
    match m.member {
        Some(_) => Ok(()),
        None => match target_pin_tys(pers, st, mode, vis, fe, r_p, &m.ds, 0) {
            Err(e) => Err(e),
            Ok(()) => match intern_e_const(pers, st, m.ind.dup2(), m.lvls.dup2()) {
                Err(e) => Err(e),
                Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, &m.ds) {
                    Err(e) => Err(e),
                    Ok(app) => match core::infer_type_core(pers, vis, st, mode, fe, core::CHECK_FUEL, r_p, &app) {
                        Err(e) => Err(e),
                        Ok(_) => Ok(()),
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The recursor records' pins
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
/// Lean twin: `p.recs.filter fun rc => rc.tgt < p.k` (`own = true`) or its
/// negation — the member recursors, resp. the auxiliary ones, in order.
pub fn recs_by_target(rs: &Vec<RecShape>, k: u64, own: bool, i: usize, out: Vec<RecShape>) -> Vec<RecShape> {
    if i >= rs.len() {
        out
    } else if (rs[i].tgt < k) == own {
        let mut o: Vec<RecShape> = out;
        o.push(block_parts::rec_shape_dup(&rs[i]));
        recs_by_target(rs, k, own, i + 1, o)
    } else {
        recs_by_target(rs, k, own, i + 1, out)
    }
}

/// con-leche: none — the auxiliary recursor-name prefix `rec_`, as code points
/// Lean twin: `s!"rec_{i + 1}"`'s literal part.
pub const REC_AUX_PREFIX: [u32; 4] = [114, 101, 99, 95];

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
/// Lean twin: `(List.range n).map fun i => n0.str s!"rec_{i + 1}"` — official's
/// auxiliary recursor names `T_0.rec_1 … T_0.rec_n`, interned.
pub fn want_aux_names(
    pers: &PersTier,
    st: &mut AState,
    n0: &NIdx,
    n: u64,
    i: u64,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if i >= n {
        Ok(out)
    } else {
        let mut s: Vec<u32> = code_points(&REC_AUX_PREFIX);
        let digits: Vec<u32> = crate::kernel::core_k::nat_to_dec(i + 1);
        s = cps_append(s, &digits, 0);
        match intern_n_node(pers, st, NNodeView::Str(n0.dup2(), s)) {
            Err(e) => Err(e),
            Ok(nm) => {
                let mut o: Vec<NIdx> = out;
                o.push(nm);
                want_aux_names(pers, st, n0, n, i + 1, o)
            }
        }
    }
}

/// con-leche: none — `s ++ t` on code-point strings
/// Lean twin: string append.
pub fn cps_append(s: Vec<u32>, t: &Vec<u32>, i: usize) -> Vec<u32> {
    if i >= t.len() {
        s
    } else {
        let mut o: Vec<u32> = s;
        o.push(t[i]);
        cps_append(o, t, i + 1)
    }
}

/// con-leche: none — `xs.map (·.1.name)` over the constructors
/// Lean twin: the constructors' names, in order.
pub fn ctor_names(cs: &Vec<(IConstantVal, u64)>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(cs[i].0.name.dup2());
        ctor_names(cs, i + 1, o)
    }
}

/// con-leche: none — `cs.map (·.1.name)` over the split's constructor triples
/// Lean twin: the stream's constructors' names, in order.
pub fn ctor3_names(cs: &Vec<(IConstantVal, u64, u64)>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= cs.len() {
        out
    } else {
        let mut o: Vec<NIdx> = out;
        o.push(cs[i].0.name.dup2());
        ctor3_names(cs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetRecPins` — **the
/// recursor records' pins**: the level parameters, the reserved names, the
/// member recursors' names as the set `{T_m.rec}`, the auxiliary ones as
/// `T_0.rec_1 … T_0.rec_n`, all names distinct, and the constructor grouping
/// against the stream's own order.
pub fn target_rec_pins(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    block: &Vec<IConstantInfo>,
) -> Result<(), CheckError> {
    if !block_parts::block_rec_lps_ok(p) {
        fail(core_types::invalid(code_points(&M_REC_LPS)))
    } else {
        match block_parts::block_rec_names_unreserved(st, &p.recs, 0) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_REC_RESERVED))),
            Ok(true) => {
                let k: u64 = shape_k(p);
                let own: Vec<RecShape> = recs_by_target(&p.recs, k, true, 0, Vec::new());
                match block_parts::block_rec_name_set_ok(pers, st, &p.members, &own) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_REC_NAMES))),
                    Ok(true) => target_rec_pins_aux(pers, st, p, block),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetRecPins` — the
/// auxiliary names, distinctness and the grouping.
pub fn target_rec_pins_aux(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    block: &Vec<IConstantInfo>,
) -> Result<(), CheckError> {
    if p.members.len() == 0 {
        match intern_n_node(pers, st, NNodeView::Anonymous) {
            Err(e) => Err(e),
            Ok(n0) => target_rec_pins_names(pers, st, p, block, &n0),
        }
    } else {
        let n0: NIdx = p.members[0].cv_t.name.dup2();
        target_rec_pins_names(pers, st, p, block, &n0)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:480-518 targetRecPins
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetRecPins` — the
/// auxiliary names at member 0's name `n0` (`.anonymous` at no member).
pub fn target_rec_pins_names(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    block: &Vec<IConstantInfo>,
    n0: &NIdx,
) -> Result<(), CheckError> {
    let k: u64 = shape_k(p);
    let aux: Vec<RecShape> = recs_by_target(&p.recs, k, false, 0, Vec::new());
    match want_aux_names(pers, st, n0, aux.len() as u64, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(want) => {
                let got: Vec<NIdx> = block_parts::rec_names(&aux, 0, Vec::new());
                if !(got.len() == want.len()
                    && block_parts::names_all_in(&want, &got, 0)
                    && block_parts::names_all_in(&got, &want, 0))
                {
                    fail(core_types::invalid(code_points(&M_AUX_NAMES)))
                } else if !checker_base::name_nodup(&block_parts::rec_names(&p.recs, 0, Vec::new())) {
                    fail(core_types::invalid(code_points(&M_REC_DUP)))
                } else {
                    match block_parts::block_split(block, 0, Vec::new()) {
                        None => fail(core_types::invalid(code_points(&M_NO_SPLIT))),
                        Some((cv_ts, cs, rs)) => {
                            let mine: Vec<NIdx> =
                                ctor_names(&block_parts::all_ctors(&p.members, 0, Vec::new()), 0, Vec::new());
                            let theirs: Vec<NIdx> = ctor3_names(&cs, 0, Vec::new());
                            if cv_ts.len() as u64 == k
                                && rs.len() == p.recs.len()
                                && core::nidx_vec_beq(&mine, &theirs)
                            {
                                Ok(())
                            } else {
                                fail(core_types::invalid(code_points(&M_GROUPING)))
                            }
                        }
                    }
                }
            }
    }
}

// ---------------------------------------------------------------------------
// A class's constructors, and node agreement (K.53′)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:522-528 targetCtorAt
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetCtorAt` — a
/// constructor's type at the major's LEVELS: a member's as stored, an outside
/// inductive's instantiated at the major's.
pub fn target_ctor_at(pers: &PersTier, st: &mut AState, m: &TargetMajor, c: &IConstantVal) -> Result<EIdx, CheckError> {
    match m.member {
        Some(_) => Ok(c.ty.dup2()),
        None => expr_ops::inst_lp_fast(pers, st, CORE_WALK_FUEL, &c.level_params, &m.lvls, &c.ty),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `teleW.map (fun b => (b.1.eraseFVarTys, b.2))` — a telescope's
/// domains erased, in order.
pub fn erase_binders(
    pers: &PersTier,
    st: &mut AState,
    bs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<Vec<(EIdx, BinderMeta)>, CheckError> {
    if i >= bs.len() {
        Ok(out)
    } else {
        let x: EIdx = bs[i].0.dup2();
        match erase_fvar_tys(pers, st, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((y, expr::binder_meta_dup(&bs[i].1)));
                erase_binders(pers, st, bs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `xs.map Expr.eraseFVarTys`, in order.
pub fn erase_list(
    pers: &PersTier,
    st: &mut AState,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match erase_fvar_tys(pers, st, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                erase_list(pers, st, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: none — `==` on a binder list: the domain handles and the binder data
/// Lean twin: the cited `List (Expr × BinderMeta)` equality.
pub fn binders_beq(a: &Vec<(EIdx, BinderMeta)>, b: &Vec<(EIdx, BinderMeta)>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if a[i].0.eq2(&b[i].0) && expr::binder_meta_beq(&a[i].1, &b[i].1) {
        binders_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetK53` — **K.53′ at
/// one recorded field** `f`: its telescope is the call's `tele` and its leaf
/// the callee's major `maj_dom`, up to the free variables' annotations, and
/// the leaf's CLASS matches the callee's class `mc` per component.
#[allow(clippy::too_many_arguments)]
pub fn target_k53(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    tele: &Vec<(EIdx, BinderMeta)>,
    maj_dom: &EIdx,
    f: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(pers, st, tele.len() as u64, f) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some((tele_w, leaf_w))) => match erase_binders(pers, st, &tele_w, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(ew) => match erase_binders(pers, st, tele, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(et) => {
                    if !binders_beq(&ew, &et, 0) {
                        Ok(false)
                    } else {
                        target_k53_leaf(pers, st, mode, vis, fe, p, former_tys, mc, maj_dom, &leaf_w)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetK53` — the
/// leaf's head constant and arity against the major's, its indices up to
/// annotations, its class naming a member, then the per-component match.
#[allow(clippy::too_many_arguments)]
pub fn target_k53_leaf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    maj_dom: &EIdx,
    leaf_w: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, leaf_w) {
        Err(e) => Err(e),
        Ok(lh) => match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, maj_dom) {
            Err(e) => Err(e),
            Ok(mh) => {
                if lh.tag() == ETAG_CONST && mh.tag() == ETAG_CONST {
                    match view_const(pers, st, &lh) {
                        None => fail_dangling_e(),
                        Some((i2, us2)) => match view_const(pers, st, &mh) {
                            None => fail_dangling_e(),
                            Some((i1, _)) => {
                                target_k53_args(pers, st, mode, vis, fe, p, former_tys, mc, maj_dom, leaf_w, &i2, &us2, &i1)
                            }
                        },
                    }
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetK53` — the
/// cited `&&` chain, left to right: the heads, the arities, the erased
/// indices, the class naming a member; then `targetClassMatch`.
#[allow(clippy::too_many_arguments)]
pub fn target_k53_args(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    maj_dom: &EIdx,
    leaf_w: &EIdx,
    i2: &NIdx,
    us2: &LsIdx,
    i1: &NIdx,
) -> Result<bool, CheckError> {
    match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, leaf_w) {
        Err(e) => Err(e),
        Ok(la) => match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, maj_dom) {
            Err(e) => Err(e),
            Ok(ma) => {
                if !(i2.eq2(i1) && la.len() == ma.len()) {
                    Ok(false)
                } else {
                    let ld: Vec<EIdx> = core::drop_eidx_n(&la, mc.n_pc);
                    let md: Vec<EIdx> = core::drop_eidx_n(&ma, mc.n_pc);
                    match erase_list(pers, st, &ld, 0, Vec::new()) {
                        Err(e) => Err(e),
                        Ok(le) => match erase_list(pers, st, &md, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(me) => {
                                if !crate::arena::canon::eidx_vec_beq(&le, &me, 0) {
                                    Ok(false)
                                } else {
                                    let lp: Vec<EIdx> = expr_ops::take_eidx_n(&la, mc.n_pc);
                                    target_k53_class(pers, st, mode, vis, fe, p, former_tys, mc, i2, us2, &lp)
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:530-556 targetK53
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetK53` — the leaf's
/// class `I'.{us'} lp` names a member (official's `is_nested`), and matches
/// the callee's class per component.
#[allow(clippy::too_many_arguments)]
pub fn target_k53_class(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    vis: u64,
    fe: &IFEnv,
    p: &BlockShape,
    former_tys: &Vec<EIdx>,
    mc: &TargetMajor,
    i2: &NIdx,
    us2: &LsIdx,
    lp: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match intern_e_const(pers, st, i2.dup2(), us2.dup2()) {
        Err(e) => Err(e),
        Ok(hd) => match expr_ops::mk_app_n(pers, st, &hd, lp) {
            Err(e) => Err(e),
            Ok(app) => {
                let names: Vec<NIdx> = shape_member_names(p);
                match nest_occ(pers, st, &names, 0, 0, &app) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => target_class_match(pers, st, mode, vis, fe, p, former_tys, &mc.pfvs, &mc.lvls, &mc.ds, us2, lp),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:558-563 targetPiDomsWith
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean targetPiDomsWith` — the
/// domains of the first `|xs|` `∀` binders, each instantiated at the earlier
/// `xs`.
pub fn target_pi_doms_with(
    pers: &PersTier,
    st: &mut AState,
    xs: &Vec<EIdx>,
    i: usize,
    e: &EIdx,
    out: Vec<EIdx>,
) -> Result<Option<Vec<EIdx>>, CheckError> {
    if i >= xs.len() {
        Ok(Some(out))
    } else if e.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, e) {
            None => fail_dangling_e(),
            Some((d, b, _)) => {
                let x: EIdx = xs[i].dup2();
                match expr_ops::instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &x, 0) {
                    Err(er) => Err(er),
                    Ok(b2) => {
                        let mut o: Vec<EIdx> = out;
                        o.push(d);
                        target_pi_doms_with(pers, st, xs, i + 1, &b2, o)
                    }
                }
            }
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// The stored family
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:574-585 auxRuleFireR
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean auxRuleFireR` — **the
/// firing mode of a rule at an OUTSIDE major**: `.nested` at the syntactic
/// reading of the recursor type's major domain, `.inert` when it fails.
/// `resolves` is the constructors' environment at `vis`.
#[allow(clippy::too_many_arguments)]
pub fn aux_rule_fire_r(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    m_i: u64,
    r_p: u64,
    n_pc: u64,
) -> Result<IRecRuleFire, CheckError> {
    match expr_ops::nested_rule_syn(pers, vis, st, fe, &cv.level_params, &cv.ty, m_i, r_p, n_pc) {
        Err(e) => Err(e),
        Ok(Some((lvls, pins))) => Ok(IRecRuleFire::Nested(lvls, pins)),
        Ok(None) => Ok(IRecRuleFire::Inert),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:587-597 tgtStoredRules
/// Lean twin: `rules.map fun rl => { rl with fire := f }` — every rule refired
/// at the one reading.
pub fn refire(rules: Vec<IRecRule>, f: &IRecRuleFire, i: usize, out: Vec<IRecRule>) -> Vec<IRecRule> {
    if i >= rules.len() {
        out
    } else {
        let mut rl: IRecRule = env::i_rec_rule_dup(&rules[i]);
        rl.fire = env::i_rec_rule_fire_dup(f);
        let mut o: Vec<IRecRule> = out;
        o.push(rl);
        refire(rules, f, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:587-597 tgtStoredRules
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean tgtStoredRules` — **one
/// checked recursor's stored rules, at its major**: `sumRules` at the major's
/// parameter count and constructors, every rule `.nested` at an OUTSIDE
/// major (the reading computed once, the module note).
#[allow(clippy::too_many_arguments)]
pub fn tgt_stored_rules(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    m_i: u64,
    r_p: u64,
    m: &TargetMajor,
    rhss: &Vec<EIdx>,
) -> Result<Vec<IRecRule>, CheckError> {
    match sum_install::sum_rules(pers, vis, st, fe, &cv.name, m.n_pc, m_i, r_p, &cv.ty, &m.ctors, rhss, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(rules) => match m.member {
            Some(_) => Ok(rules),
            None => match aux_rule_fire_r(pers, vis, st, fe, cv, m_i, r_p, m.n_pc) {
                Err(e) => Err(e),
                Ok(f) => Ok(refire(rules, &f, 0, Vec::new())),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:599-605 blockNestedBit
/// Lean twin: `p.recs.any (fun rc => !(rc.tgt < p.k))`.
pub fn some_aux_rec(rs: &Vec<RecShape>, k: u64, i: usize) -> bool {
    if i >= rs.len() {
        false
    } else if rs[i].tgt < k {
        some_aux_rec(rs, k, i + 1)
    } else {
        true
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:599-605 blockNestedBit
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean blockNestedBit` — **the
/// block's container bit**: some field kind is not flat or some recursor's
/// major is not a member.
pub fn block_nested_bit(p: &BlockShape, kinds: &Vec<Vec<Vec<NestFieldKind>>>) -> bool {
    if nest_kinds_flat(kinds, 0) {
        some_aux_rec(&p.recs, shape_k(p), 0)
    } else {
        true
    }
}

/// con-leche: ConLeche/Kernel/Inductives/RecCheck.lean:607-617 consBlockRecsTF
/// con-leche: ConLeche/Kernel/Inductives/BlockTail.lean:93-106 consBlockRecsT
/// Lean twin: `proof/ConRon/Arena/Inductives/RecCheck.lean consBlockRecsTF` — **the
/// checked family consed through the index, at its majors**: each recursor
/// with its rules at ITS major, the rules' lookups (`find?`, `resolves`) at the
/// constructors' environment, i.e. at its visibility bound `vis2` while the
/// recursors are pushed above it.
pub fn cons_block_recs_t(
    pers: &PersTier,
    vis2: u64,
    st: &mut AState,
    p: &BlockShape,
    m: u64,
    out: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    if m >= out.len() as u64 {
        Ok(fe)
    } else {
        let cv: IConstantVal = env::i_constant_val_dup(&out[m as usize].0);
        let mj: TargetMajor = target_major_dup(&out[m as usize].1);
        let rhss: Vec<EIdx> = env::eidx_vec_dup(&out[m as usize].2);
        let m_i: u64 = block_parts::major_idx_at(p, m);
        let r_p: u64 = block_parts::rule_prefix_at(p, m);
        match tgt_stored_rules(pers, vis2, st, &fe, &cv, m_i, r_p, &mj, &rhss) {
            Err(e) => Err(e),
            Ok(rules) => {
                let fe2: IFEnv = env::ifenv_push(fe, IConstantInfo::RecInfo(cv, m_i, r_p, rules));
                cons_block_recs_t(pers, vis2, st, p, m + 1, out, fe2)
            }
        }
    }
}
