//! `arena::inductives::stored_recs` — the stored recursors, against the
//! generated ones.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/StoredRecs.lean`, which is
//! `ConLeche/Kernel/Inductives/StoredRecs.lean` over handles.  The installer
//! GENERATES every recursor of a block (`gen_rec::gen_rec_check`) and installs
//! the STORED one — the record's type and its rules' right-hand sides — once
//! the two agree up to definitional equality.  Everything else of the
//! installed recursor (its major index and rule prefix, each rule's
//! constructor, field count, constructor parameter count, firing mode and
//! rescue bits) is the generator's.
//!
//! ## The twin's deviations
//!
//! * **The operations are not a record**: `ops` and `w` are `core`'s entry
//!   points and `checker_base::consts_resolve_f_fast` at the `IFEnv` in hand,
//!   whose visibility bound holds the generated recursors
//!   (`block_tail::check_block_tail_stored`).
//! * **The messages are constants** (§3.1 drops the interpolation), so the
//!   `rec`/`ctor` arguments that only name the slot are gone.
//! * **Upstream's `==` on terms and names is handle equality**, as everywhere
//!   in the arena.
//! * **Terms read from the store take the state**: `storedNestedOk` and
//!   `storedFireOf` intern, so they are monadic.
//! * **`stored_closed`** is the closedness test `recTyCheck` and `ruleAgree`
//!   both open with, one function.

use super::block_parts;
use super::block_parts::RecShape;
use super::rec_check;
use super::rec_check::TargetMajor;
use crate::arena::canon;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantVal, IFEnv, IRecRule, IRecRuleFire};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, NIdx, ETAG_CONST, ETAG_FORALL_E};
use crate::arena::monad::{fail, fail_dangling_e, intern_e_bvar, view_bind, view_const, view_ls, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr_ops::sub_nat;
use crate::ron::hashmap::{Dup, Eq2};

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `stored recursor: domain index`, as code points.
pub const M_DOM_INDEX: [u32; 29] = [
    115, 116, 111, 114, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 58, 32, 100, 111, 109,
    97, 105, 110, 32, 105, 110, 100, 101, 120,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: the domain of binder  differs`, as code points.
pub const M_TY_DOM: [u32; 81] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 116, 104, 101, 32, 100, 111, 109, 97,
    105, 110, 32, 111, 102, 32, 98, 105, 110, 100, 101, 114, 32, 32, 100, 105, 102, 102, 101, 114,
    115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: its body after the major differs`, as code points.
pub const M_TY_BODY: [u32; 84] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 105, 116, 115, 32, 98, 111, 100, 121,
    32, 97, 102, 116, 101, 114, 32, 116, 104, 101, 32, 109, 97, 106, 111, 114, 32, 100, 105, 102,
    102, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not the generated one: it has fewer than  binders`, as code points.
pub const M_TY_SHORT: [u32; 78] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 58, 32, 105, 116, 32, 104, 97, 115, 32, 102,
    101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 32, 98, 105, 110, 100, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the generated type of the recursor  has fewer than  binders`, as code points.
pub const M_GEN_SHORT: [u32; 59] = [
    116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 116, 121, 112, 101, 32, 111,
    102, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 104, 97, 115, 32,
    102, 101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 32, 98, 105, 110, 100, 101, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the type of the recursor  is not closed`, as code points.
pub const M_TY_OPEN: [u32; 39] = [
    116, 104, 101, 32, 116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117,
    114, 115, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 99, 108, 111, 115, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `undeclared universe parameter in the type of the recursor `, as code points.
pub const M_TY_ULP: [u32; 58] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 104, 101, 32, 116, 121, 112,
    101, 32, 111, 102, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side that is not closed`, as code points.
pub const M_RULE_OPEN: [u32; 66] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 116, 104, 97, 116, 32, 105, 115, 32, 110, 111, 116, 32,
    99, 108, 111, 115, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has an undeclared universe parameter`, as code points.
pub const M_RULE_ULP: [u32; 62] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 110, 32, 117, 110, 100, 101, 99, 108, 97,
    114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116,
    101, 114,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side whose type is not the generated one's`, as code points.
pub const M_RULE_TY: [u32; 85] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 119, 104, 111, 115, 101, 32, 116, 121, 112, 101, 32, 105,
    115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32,
    111, 110, 101, 39, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  has a right-hand side that is not definitionally equal to the generated one`, as code points.
pub const M_RULE_DEFEQ: [u32; 101] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 104, 97, 115, 32, 97, 32, 114, 105, 103, 104, 116, 45, 104, 97,
    110, 100, 32, 115, 105, 100, 101, 32, 116, 104, 97, 116, 32, 105, 115, 32, 110, 111, 116, 32,
    100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 97, 108, 108, 121, 32, 101, 113, 117, 97, 108,
    32, 116, 111, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110,
    101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's rule for  is not the generated one's (constructor ,  fields)`, as code points.
pub const M_RULE_SHAPE: [u32; 76] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 114, 117, 108, 101,
    32, 102, 111, 114, 32, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 39, 115, 32, 40, 99, 111, 110, 115, 116, 114,
    117, 99, 116, 111, 114, 32, 44, 32, 32, 102, 105, 101, 108, 100, 115, 41,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor  carries  more or fewer rules than the generated one ( unmatched)`, as code points.
pub const M_RULE_COUNT: [u32; 78] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 32, 99, 97, 114, 114, 105, 101,
    115, 32, 32, 109, 111, 114, 101, 32, 111, 114, 32, 102, 101, 119, 101, 114, 32, 114, 117, 108,
    101, 115, 32, 116, 104, 97, 110, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101,
    100, 32, 111, 110, 101, 32, 40, 32, 117, 110, 109, 97, 116, 99, 104, 101, 100, 41,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor : the generated rules are not one per stored rule`, as code points.
pub const M_RULES_GEN: [u32; 62] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 58, 32, 116, 104, 101, 32, 103,
    101, 110, 101, 114, 97, 116, 101, 100, 32, 114, 117, 108, 101, 115, 32, 97, 114, 101, 32, 110,
    111, 116, 32, 111, 110, 101, 32, 112, 101, 114, 32, 115, 116, 111, 114, 101, 100, 32, 114, 117,
    108, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `the recursor 's stored type does not apply its major's container at the generated firing data`, as code points.
pub const M_NESTED: [u32; 93] = [
    116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 39, 115, 32, 115, 116, 111, 114,
    101, 100, 32, 116, 121, 112, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 97, 112, 112,
    108, 121, 32, 105, 116, 115, 32, 109, 97, 106, 111, 114, 39, 115, 32, 99, 111, 110, 116, 97,
    105, 110, 101, 114, 32, 97, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97, 116, 101,
    100, 32, 102, 105, 114, 105, 110, 103, 32, 100, 97, 116, 97,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `stored recursors: the generated family is not the records'`, as code points.
pub const M_FAMILY: [u32; 58] = [
    115, 116, 111, 114, 101, 100, 32, 114, 101, 99, 117, 114, 115, 111, 114, 115, 58, 32, 116, 104,
    101, 32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 102, 97, 109, 105, 108, 121, 32, 105,
    115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 114, 101, 99, 111, 114, 100, 115, 39,
];

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:45-59 recDomsAt
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:33-48 recDomsAt` — **the
/// stored type's domains against the generated one's**, binder by binder from
/// binder `j` on (`k` of them): each stored domain `isDefEq` to the generated
/// one at its depth, both telescopes opened at their own locals.
#[allow(clippy::too_many_arguments)]
pub fn rec_doms_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    sfvs: &Vec<EIdx>,
    gfvs: &Vec<EIdx>,
    j: u64,
    k: u64,
) -> Result<(), CheckError> {
    if k == 0 {
        Ok(())
    } else if j >= sfvs.len() as u64 || j >= gfvs.len() as u64 {
        fail(core_types::internal(code_points(&M_DOM_INDEX)))
    } else {
        match expr_ops::fvar_type_d(pers, st, &sfvs[j as usize]) {
            Err(e) => Err(e),
            Ok(a) => match expr_ops::fvar_type_d(pers, st, &gfvs[j as usize]) {
                Err(e) => Err(e),
                Ok(b) => match core::is_def_eq_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, j, &a, &b) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_TY_DOM))),
                    Ok(true) => rec_doms_at(pers, st, mode, fe, sfvs, gfvs, j + 1, k - 1),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:61-74 recTyOpened
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:50-60 recTyOpened` — the
/// stored and the generated type, opened `n` binders deep: the domains, then
/// the residues.
pub fn rec_ty_opened(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n: u64,
    s: &Option<(Vec<EIdx>, EIdx)>,
    g: &Option<(Vec<EIdx>, EIdx)>,
) -> Result<(), CheckError> {
    match s {
        None => fail(core_types::invalid(code_points(&M_TY_SHORT))),
        Some((sfvs, srest)) => match g {
            None => fail(core_types::internal(code_points(&M_GEN_SHORT))),
            Some((gfvs, grest)) => match rec_doms_at(pers, st, mode, fe, sfvs, gfvs, 0, n) {
                Err(e) => Err(e),
                Ok(()) => match core::is_def_eq_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, n, srest, grest) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_TY_BODY))),
                    Ok(true) => Ok(()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:76-90 recTyCheck
/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:92-113 ruleAgree
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:62-71 storedClosed` — the
/// test both open with: `s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar`.
pub fn stored_closed(pers: &PersTier, st: &mut AState, s: &EIdx, g: &EIdx) -> Result<bool, CheckError> {
    match expr_ops::loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, s) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, s) {
            Err(e) => Err(e),
            Ok(true) => Ok(false),
            Ok(false) => match expr_ops::has_fvar_fast(pers, st, CORE_WALK_FUEL, g) {
                Err(e) => Err(e),
                Ok(h) => Ok(!h),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:76-90 recTyCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:73-89 recTyCheck` — **the
/// stored type's check**: closed, at the record's level parameters `lps`,
/// resolving, a type (inferred, a sort), and the generated one binder by binder
/// up to the major (`n` binders): the domains, then the residues.
#[allow(clippy::too_many_arguments)]
pub fn rec_ty_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    n: u64,
    s: &EIdx,
    g: &EIdx,
) -> Result<(), CheckError> {
    match stored_closed(pers, st, s, g) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_TY_OPEN))),
        Ok(true) => match checker_base::all_level_params_defined(pers, st, lps, s) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_TY_ULP))),
            Ok(true) => match checker_base::consts_resolve_f_fast(pers, fe.visible_below, st, fe, s) {
                Err(e) => Err(e),
                Ok(false) => match checker_base::unresolved_consts_error(pers, st, s) {
                    Err(e) => Err(e),
                    Ok(er) => fail(er),
                },
                Ok(true) => match core::infer_type_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, s) {
                    Err(e) => Err(e),
                    Ok(st_ty) => match core::ensure_sort_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, &st_ty) {
                        Err(e) => Err(e),
                        Ok(_) => match checker_base::open_pis_at_fvars(pers, st, n, s, 0) {
                            Err(e) => Err(e),
                            Ok(so) => match checker_base::open_pis_at_fvars(pers, st, n, g, 0) {
                                Err(e) => Err(e),
                                Ok(go) => rec_ty_opened(pers, st, mode, fe, n, &so, &go),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:92-113 ruleAgree
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:91-107 ruleAgree` — **one
/// stored rule's check**: the stored right-hand side `s` is closed, at the
/// record's level parameters `lps`, resolving; it and the generated `g` are
/// inferred, their types are definitionally equal, and so are they.
pub fn rule_agree(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    s: &EIdx,
    g: &EIdx,
) -> Result<(), CheckError> {
    match stored_closed(pers, st, s, g) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_RULE_OPEN))),
        Ok(true) => match checker_base::all_level_params_defined(pers, st, lps, s) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::invalid(code_points(&M_RULE_ULP))),
            Ok(true) => match checker_base::consts_resolve_f_fast(pers, fe.visible_below, st, fe, s) {
                Err(e) => Err(e),
                Ok(false) => match checker_base::unresolved_consts_error(pers, st, s) {
                    Err(e) => Err(e),
                    Ok(er) => fail(er),
                },
                Ok(true) => match core::infer_type_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, s) {
                    Err(e) => Err(e),
                    Ok(ts) => match core::infer_type_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, g) {
                        Err(e) => Err(e),
                        Ok(tg) => match core::is_def_eq_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, &ts, &tg) {
                            Err(e) => Err(e),
                            Ok(false) => fail(core_types::invalid(code_points(&M_RULE_TY))),
                            Ok(true) => match core::is_def_eq_core(pers, fe.visible_below, st, mode, fe, core::CHECK_FUEL, 0, s, g) {
                                Err(e) => Err(e),
                                Ok(false) => fail(core_types::invalid(code_points(&M_RULE_DEFEQ))),
                                Ok(true) => Ok(()),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
/// Lean twin: `pins.map (Expr.liftLooseBVars amount 0)` — the firing pins lifted
/// past the index binders, from `i` on, pushed onto `out`.
pub fn stored_nested_pins(
    pers: &PersTier,
    st: &mut AState,
    amount: u64,
    pins: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= pins.len() {
        Ok(out)
    } else {
        match expr_ops::lift_loose_bvars_fast(pers, st, CORE_WALK_FUEL, amount, 0, &pins[i]) {
            Err(e) => Err(e),
            Ok(p) => {
                let mut o: Vec<EIdx> = out;
                o.push(p);
                stored_nested_pins(pers, st, amount, pins, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
/// Lean twin: `(List.range n).map (fun i => Expr.bvar (n - 1 - i))` — the index
/// variables, `k` of them still to come, pushed onto `out`.
pub fn stored_nested_bvars(pers: &PersTier, st: &mut AState, k: u64, out: Vec<EIdx>) -> Result<Vec<EIdx>, CheckError> {
    if k == 0 {
        Ok(out)
    } else {
        match intern_e_bvar(pers, st, k - 1) {
            Err(e) => Err(e),
            Ok(b) => {
                let mut o: Vec<EIdx> = out;
                o.push(b);
                stored_nested_bvars(pers, st, k - 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:109-127 storedNestedDom` — the
/// major's domain against the firing data: its head a constant at the firing
/// levels, its arguments the pins lifted past the index binders and the index
/// variables.
pub fn stored_nested_dom(
    pers: &PersTier,
    st: &mut AState,
    dom: &EIdx,
    n: u64,
    lvls: &Vec<LIdx>,
    pins: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(pers, st, CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(hd) => {
            if hd.tag() == ETAG_CONST {
                match view_const(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some((_, us)) => match view_ls(pers, st, &us) {
                        Err(e) => Err(e),
                        Ok(usv) => {
                            if canon::lidx_vec_beq(&usv, lvls, 0) {
                                match expr_ops::get_app_args(pers, st, CORE_WALK_FUEL, dom) {
                                    Err(e) => Err(e),
                                    Ok(args) => match stored_nested_pins(pers, st, n, pins, 0, Vec::new()) {
                                        Err(e) => Err(e),
                                        Ok(ps) => match stored_nested_bvars(pers, st, n, ps) {
                                            Err(e) => Err(e),
                                            Ok(want) => Ok(canon::eidx_vec_beq(&args, &want, 0)),
                                        },
                                    },
                                }
                            } else {
                                Ok(false)
                            }
                        }
                    },
                }
            } else {
                Ok(false)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:115-131 storedNestedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:129-144 storedNestedOk` — **an
/// auxiliary recursor's stored type fires where the generated one does**: its
/// major's domain (binder `m_i`) is the container at the firing data's levels,
/// applied to the pins lifted past the index binders and the index variables.
/// `true` at a member major (its rules fire `.plain`).
pub fn stored_nested_ok(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    m_i: u64,
    r_p: u64,
    fire: &IRecRuleFire,
) -> Result<bool, CheckError> {
    match fire {
        IRecRuleFire::Plain => Ok(true),
        IRecRuleFire::Nested(lvls, pins) => match expr_ops::strip_pis(pers, st, m_i, ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some((_, rest))) => {
                if rest.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &rest) {
                        None => fail_dangling_e(),
                        Some((dom, _)) => stored_nested_dom(pers, st, &dom, sub_nat(m_i, r_p), lvls, pins),
                    }
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:133-138 storedFireOf
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:146-152 storedFireOf` — the
/// firing mode the generated recursor's rules carry at its major: `.nested` at
/// an outside major, `.plain` at a member.
pub fn stored_fire_of(pers: &PersTier, st: &mut AState, m: &TargetMajor, r_p: u64) -> Result<IRecRuleFire, CheckError> {
    match m.member {
        None => rec_check::aux_rule_fire(pers, st, m, r_p),
        Some(_) => Ok(IRecRuleFire::Plain),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:140-152 storedRulesShape
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:154-163 storedRulesShape` — the
/// stored rules' shape against the generated recursor's class, from `i` on: one
/// rule per constructor of the class, in order, each with its field count.
pub fn stored_rules_shape(rs: &Vec<IRecRule>, cs: &Vec<(IConstantVal, u64)>, i: usize) -> Result<(), CheckError> {
    if i >= rs.len() && i >= cs.len() {
        Ok(())
    } else if i >= rs.len() || i >= cs.len() {
        fail(core_types::invalid(code_points(&M_RULE_COUNT)))
    } else if rs[i].ctor.eq2(&cs[i].0.name) && rs[i].nfields == cs[i].1 {
        stored_rules_shape(rs, cs, i + 1)
    } else {
        fail(core_types::invalid(code_points(&M_RULE_SHAPE)))
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:154-163 storedRulesCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:165-175 storedRulesCheck` — the
/// stored rules' checks from `i` on, each against the generated right-hand side
/// at its position (a rule equal to the generated one needs none).
#[allow(clippy::too_many_arguments)]
pub fn stored_rules_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    lps: &Vec<NIdx>,
    rs: &Vec<IRecRule>,
    gs: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rs.len() && i >= gs.len() {
        Ok(())
    } else if i >= rs.len() || i >= gs.len() {
        fail(core_types::internal(code_points(&M_RULES_GEN)))
    } else if rs[i].rhs.eq2(&gs[i]) {
        stored_rules_check(pers, st, mode, fe, lps, rs, gs, i + 1)
    } else {
        match rule_agree(pers, st, mode, fe, lps, &rs[i].rhs, &gs[i]) {
            Err(e) => Err(e),
            Ok(()) => stored_rules_check(pers, st, mode, fe, lps, rs, gs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:165-172 storedRecCompare
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:177-184 storedRecCompare` — **the
/// comparison of one recursor**: its stored type unless it is the generated
/// one, and its stored rules.
pub fn stored_rec_compare(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rc: &RecShape,
    g: &(IConstantVal, TargetMajor, Vec<EIdx>),
) -> Result<(), CheckError> {
    if rc.cv_r.ty.eq2(&g.0.ty) {
        stored_rules_check(pers, st, mode, fe, &g.0.level_params, &rc.rules, &g.2, 0)
    } else {
        match rec_ty_check(pers, st, mode, fe, &g.0.level_params, rc.m_i + 1, &rc.cv_r.ty, &g.0.ty) {
            Err(e) => Err(e),
            Ok(()) => stored_rules_check(pers, st, mode, fe, &g.0.level_params, &rc.rules, &g.2, 0),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:174-183 storedRecCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:186-195 storedRecCheck` — **one
/// recursor, stored against generated**: the rules' shape and the stored major's
/// container, decided before anything is compared, then the comparison.
pub fn stored_rec_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rc: &RecShape,
    g: &(IConstantVal, TargetMajor, Vec<EIdx>),
) -> Result<(), CheckError> {
    match stored_rules_shape(&rc.rules, &g.1.ctors, 0) {
        Err(e) => Err(e),
        Ok(()) => match stored_fire_of(pers, st, &g.1, rc.r_p) {
            Err(e) => Err(e),
            Ok(fire) => match stored_nested_ok(pers, st, &rc.cv_r.ty, rc.m_i, rc.r_p, &fire) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::internal(code_points(&M_NESTED))),
                Ok(true) => stored_rec_compare(pers, st, mode, fe, rc, g),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:185-193 storedRecsCheck
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:197-206 storedRecsCheck` — **the
/// block's stored recursors against the generated ones**, record by record from
/// `i` on (the generated family is in the records' order).
pub fn stored_recs_check(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    rcs: &Vec<RecShape>,
    gs: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rcs.len() && i >= gs.len() {
        Ok(())
    } else if i >= rcs.len() || i >= gs.len() {
        fail(core_types::internal(code_points(&M_FAMILY)))
    } else {
        match stored_rec_check(pers, st, mode, fe, &rcs[i], &gs[i]) {
            Err(e) => Err(e),
            Ok(()) => stored_recs_check(pers, st, mode, fe, rcs, gs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/StoredRecs.lean:195-202 storedOut
/// Lean twin: `proof/ConRon/Arena/Inductives/StoredRecs.lean:208-215 storedOut` — **what is
/// installed**, from `i` on: each generated recursor with the stored type and
/// the stored right-hand sides, at the generated recursor's name, level
/// parameters and major (the shorter of the two lists decides, as the cited
/// `zipWith` does).
pub fn stored_out(
    rcs: &Vec<RecShape>,
    gs: &Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
    i: usize,
    acc: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)>,
) -> Vec<(IConstantVal, TargetMajor, Vec<EIdx>)> {
    if i >= rcs.len() || i >= gs.len() {
        acc
    } else {
        let cv: IConstantVal = IConstantVal {
            name: gs[i].0.name.dup2(),
            level_params: env::nidx_vec_dup(&gs[i].0.level_params),
            ty: rcs[i].cv_r.ty.dup2(),
        };
        let mut o: Vec<(IConstantVal, TargetMajor, Vec<EIdx>)> = acc;
        o.push((cv, rec_check::target_major_dup(&gs[i].1), block_parts::rule_rhss(&rcs[i].rules, 0, Vec::new())));
        stored_out(rcs, gs, i + 1, o)
    }
}
