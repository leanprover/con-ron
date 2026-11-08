//! `arena::decl_check` — the declaration-level checks, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/DeclCheck.lean`, which is con-leche's
//! `Kernel/DeclCheck.lean` and the declaration-level halves of
//! `Kernel/Checker.lean`, `StdAxioms.lean` and `TrustAxioms.lean`.
//!
//! ## One twin per PAIR
//!
//! con-leche carries each of these functions twice — once reading the linear
//! environment and once the index (`DeclCheck.lean`'s `…F` mirrors, which is
//! what both binaries run).  The arena has ONE environment type, so each pair
//! collapses into one twin carrying a `con-leche:` line per collapsed
//! declaration, and the twin keeps the UNSUFFIXED name.
//!
//! ## No closures
//!
//! * `divModCertStmts`' eleven local lambdas are named functions here, and its
//!   twenty opening `let`s are one record (`CertCtx`) — the treatment task
//!   #97-P4c gives `natOpEquations`' eight (`NatEqCtx`), so the seven branches
//!   read as the twin's;
//! * `divModCertsGuard`'s `(… .zip …).all` is an index recursion, bounded by
//!   the shorter list, which is what a `zip` means.
//!
//! ## What is `arena::inductives`'
//!
//! The modeled and native inductive installs are the other half of this phase
//! (task #97-P4d part 2).  Eight of `DeclCheck.lean`'s declarations are
//! theirs, because they call into those modules and nothing here does.

use crate::arena::basis::{
    basis_kind_at_block, basis_kind_decls, nat_a, pin_list_ok, quot_at, quot_pin_hit, quot_preds_ok,
};
use crate::arena::canon::i_constant_info_beq;
use crate::arena::checker_base::{
    all_level_params_defined, consts_resolve_f_fast, unresolved_consts_fail,
};
use crate::arena::core::{
    bool_false_name, bool_name, bool_true_name, const_e, ensure_sort_core,
    infer_type_core, is_def_eq_core, lift_fueled, lvl_eq, nat_add_name, nat_ap1, nat_ap2,
    nat_ble_name, nat_div_name, nat_gcd_name, nat_land_name, nat_lor_name, nat_mod_name,
    nat_mul_name, nat_op_deps, nat_op_guard, nat_op_stored_ok, nat_shift_left_name,
    nat_shift_right_name, nat_sub_name, nat_xor_name, subst_const0, subst_const_all,
    zero_level, CHECK_FUEL, CORE_WALK_FUEL,
};
use crate::arena::env::{
    i_constant_info_dup, i_constant_info_to_constant_val, ifenv_find, ifenv_pop_temp, ifenv_push,
    ifenv_push_temp, IConstantInfo, IConstantVal, IFEnv,
};
use crate::arena::expr_ops::{has_fvar_fast, loose_bvars_bounded_fast};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::monad::{
    AState, fail, intern_e_app, intern_e_const, intern_e_fvar, intern_e_sort, intern_l_node,
    intern_ls_node,
};
use crate::arena::nat_op_pin_set::INatOpPinSet;
use crate::arena::std_axioms::{
    choice_name, choice_a, i_constant_val_matches_pin, iff_intro_name,
    iff_intro_a, iff_name, iff_a, iff_rec_name, iff_rec_a, nonempty_intro_name,
    nonempty_intro_a, nonempty_name, nonempty_a, nonempty_rec_name, nonempty_rec_a,
    propext_name, propext_a,
};
use crate::arena::store::LNodeView;
use crate::arena::trust_axioms::{
    bool_cv_a, of_reduce_op, of_reduce_pin_a, reduce_cert_var, reduce_decl_pin,
    reduce_nat_name, reduce_op_cv_a, true_cv_a, true_intro_cv_a, true_intro_name, true_name,
    trust_compiler_a,
};
use crate::arena::pins::{pin_eq, pin_nat, pin_nat_succ, pin_nat_zero};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{BasisKind, CheckMode, QuotKind, ReducibilityHint};
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported Nat.div/mod spelling: no pin variant matched"`, as code points.
pub const M_DIVMOD_NO_VARIANT: [u32; 56] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105,
    118, 47, 109, 111, 100, 32, 115, 112, 101, 108, 108, 105, 110, 103, 58, 32, 110, 111,
    32, 112, 105, 110, 32, 118, 97, 114, 105, 97, 110, 116, 32, 109, 97, 116, 99, 104,
    101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported Nat.div/mod environment"`, as code points.
pub const M_DIVMOD_ENV: [u32; 35] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105,
    118, 47, 109, 111, 100, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"Nat.div/mod operation not stored"`, as code points.
pub const M_DIVMOD_NOT_STORED: [u32; 32] = [
    78, 97, 116, 46, 100, 105, 118, 47, 109, 111, 100, 32, 111, 112, 101, 114, 97, 116,
    105, 111, 110, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque declaration"`, as code points.
pub const M_REDUCE_DECL: [u32; 45] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 100, 101,
    99, 108, 97, 114, 97, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque spelling: pin ground constants absent"`, as code points.
pub const M_REDUCE_PIN_ABSENT: [u32; 71] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112,
    101, 108, 108, 105, 110, 103, 58, 32, 112, 105, 110, 32, 103, 114, 111, 117, 110, 100,
    32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 97, 98, 115, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unsupported compiler-trust opaque spelling"`, as code points.
pub const M_REDUCE_SPELLING: [u32; 42] = [
    117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108,
    101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112,
    101, 108, 108, 105, 110, 103
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"pinned compiler-trust opaque is not the identity"`, as code points.
pub const M_REDUCE_NOT_ID: [u32; 48] = [
    112, 105, 110, 110, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114,
    117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 105, 115, 32, 110, 111, 116, 32,
    116, 104, 101, 32, 105, 100, 101, 110, 116, 105, 116, 121
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate declaration"`, as code points (`arena::checker_base`'s, spelled
/// again here because `install_basis_decl` is this module's).
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116,
    105, 111, 110
];

// ---------------------------------------------------------------------------
// The standard axioms' environment shape (`DeclCheck.lean:44-90` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// con-leche: ConLeche/Kernel/TrustAxioms.lean:174-184 ofReduceAxOk
/// con-leche: ConLeche/Kernel/Checker.lean:295-308 divModEnvGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:42-50 eqStored` — the
/// `(fe.find? eqName).isSome` the three guards share: the environment holds
/// `Eq` only ever as a copy of its pin (at the stream's level-parameter names),
/// so presence is the whole test.
pub fn eq_stored(pers: &PersTier, st: &AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match pin_eq(st) {
        Err(e) => Err(e),
        Ok(en) => Ok(ifenv_find(pers, fe, &en).is_some()),
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Iff` type former against the pin.  Factored out of the twin's `&&` cascade
/// so each lookup's `match` ends before the next one begins (task #14's borrow
/// rule, `con_ron_core::kernel::std_axioms::iff_pinned`'s arrangement).
pub fn iff_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match iff_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::IndInfo(cv_i, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_i);
                match iff_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:57-91 ConstantVal.matchesPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the
/// twin's `cvI.matchesPin (← (← iffA).toConstantVal)`: the pin's common data,
/// then the comparison.  One function, because six call sites spell it.
pub fn matches_pin_of_ci(cv: &IConstantVal, pin_ci: &IConstantInfo) -> bool {
    let pcv: IConstantVal = i_constant_info_to_constant_val(pin_ci);
    i_constant_val_matches_pin(cv, &pcv)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Iff.intro` against the pin, at the pinned arity `2 2`.
pub fn iff_intro_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match iff_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ii, n_p, n_f)) => {
                if *n_p == 2 && *n_f == 2 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ii);
                    match iff_intro_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Iff.rec` against the pin, at the pinned arity `4 4`.  Only its *type* is
/// used, never its reduction rules.
pub fn iff_rec_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match iff_rec_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::RecInfo(cv_ir, m_i, r_p, _, _)) => {
                if *m_i == 4 && *r_p == 4 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ir);
                    match iff_rec_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Nonempty` type former against the pin.
pub fn nonempty_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match nonempty_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::IndInfo(cv_n, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_n);
                match nonempty_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Nonempty.intro` against the pin, at the pinned arity `1 1`.
pub fn nonempty_intro_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match nonempty_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ni, n_p, n_f)) => {
                if *n_p == 1 && *n_f == 1 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ni);
                    match nonempty_intro_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the stored
/// `Nonempty.rec` against the pin, at the pinned arity `3 3`.
pub fn nonempty_rec_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match nonempty_rec_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::RecInfo(cv_nr, m_i, r_p, _, _)) => {
                if *m_i == 3 && *r_p == 3 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_nr);
                    match nonempty_rec_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(matches_pin_of_ci(&cv, &p)),
                }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-263 stdAxiomOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — is this
/// checked axiom one of the two recognized standard axioms, over
/// standardly-shaped stored `Iff` / `Nonempty` families (and the pinned `Eq`
/// basis)?  All three of each family's constants are pinned, not just the
/// type, because the verification has to REALIZE the axiom and nothing turns
/// an inhabitant of an opaque family into its fields except that family's own
/// recursor.
pub fn std_axiom_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match propext_name(st) {
        Err(e) => Err(e),
        Ok(pn) => {
            if cv.name.eq2(&pn) {
                std_axiom_ok_propext(pers, st, fe, cv)
            } else {
                match choice_name(st) {
                    Err(e) => Err(e),
                    Ok(cn) => {
                        if cv.name.eq2(&cn) {
                            std_axiom_ok_choice(pers, st, fe, cv)
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the
/// `propext` branch: the pinned `Eq` basis and the three `Iff` constants, then
/// the axiom's own type.
pub fn std_axiom_ok_propext(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match eq_stored(pers, st, fe) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match iff_pinned(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(b1) => {
                        if !b1 {
                            Ok(false)
                        } else {
                            std_axiom_ok_propext_rest(pers, st, fe, cv)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the two
/// remaining `Iff` constants and `propext`'s own type.
pub fn std_axiom_ok_propext_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match iff_intro_pinned(pers, st, fe) {
        Err(e) => Err(e),
        Ok(b2) => {
            if !b2 {
                Ok(false)
            } else {
                match iff_rec_pinned(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(b3) => {
                        if !b3 {
                            Ok(false)
                        } else {
                            match propext_a(pers, st) {
                                Err(e) => Err(e),
                                Ok(p) => Ok(i_constant_val_matches_pin(cv, &p)),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the
/// `Classical.choice` branch: the three `Nonempty` constants, then the axiom's
/// own type.
pub fn std_axiom_ok_choice(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match nonempty_pinned(pers, st, fe) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match nonempty_intro_pinned(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            std_axiom_ok_choice_rest(pers, st, fe, cv)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:168-214 stdAxiomOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:52-97 stdAxiomOk` — the
/// recursor and `Classical.choice`'s own type.
pub fn std_axiom_ok_choice_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match nonempty_rec_pinned(pers, st, fe) {
        Err(e) => Err(e),
        Ok(b3) => {
            if !b3 {
                Ok(false)
            } else {
                match choice_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(c) => Ok(i_constant_val_matches_pin(cv, &c)),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The compiler-trust family's environment shape (`DeclCheck.lean:92-152`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:141-152 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:265-273 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:101-114 trustCompilerOk` — the
/// stored `True` against its pin.
pub fn true_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match true_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::IndInfo(cv_t, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_t);
                match true_cv_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(i_constant_val_matches_pin(&cv, &p)),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:141-152 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:265-273 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:101-114 trustCompilerOk` — the
/// stored `True.intro` against its pin, at the pinned arity `0 0`.
pub fn true_intro_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match true_intro_name(st) {
        Err(e) => Err(e),
        Ok(n) => match ifenv_find(pers, fe, &n) {
            Some(IConstantInfo::CtorInfo(cv_ti, n_p, n_f)) => {
                if *n_p == 0 && *n_f == 0 {
                    let cv = crate::arena::env::i_constant_val_dup(cv_ti);
                    match true_intro_cv_a(pers, st) {
                        Err(e) => Err(e),
                        Ok(p) => Ok(i_constant_val_matches_pin(&cv, &p)),
                    }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:141-152 trustCompilerOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:265-273 trustCompilerOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:101-114 trustCompilerOk` — is
/// `Lean.trustCompiler` installable here?  The `True` family must be stored
/// with the pinned shapes, and the checked axiom's type must match the pin.
pub fn trust_compiler_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match true_pinned(pers, st, fe) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match true_intro_pinned(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            match trust_compiler_a(pers, st) {
                                Err(e) => Err(e),
                                Ok(p) => Ok(i_constant_val_matches_pin(cv, &p)),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:154-160 reduceStoredOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:275-279 reduceStoredOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:116-123 reduceStoredOk` — is
/// the reduce operation `c` stored as a checked opaque (`axiomInfo`, the
/// storage kind of every checked `opaque`) of the pinned type?
pub fn reduce_stored_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match ifenv_find(pers, fe, c) {
        Some(IConstantInfo::AxiomInfo(cv_r)) => {
            let cv = crate::arena::env::i_constant_val_dup(cv_r);
            match reduce_op_cv_a(pers, st, c) {
                Err(e) => Err(e),
                Ok(p) => Ok(i_constant_val_matches_pin(&cv, &p)),
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:162-172 reduceElemOk
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::reduce_elem_ok_refines, then delete this line
/// con-leche: ConLeche/Kernel/DeclCheck.lean:281-290 reduceElemOkF
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::reduce_elem_ok_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:125-137 reduceElemOk` — the
/// element-inductive shape an `ofReduce*` axiom needs: the pinned `Nat` basis
/// resp. a standardly-shaped stored `Bool`.
pub fn reduce_elem_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_nat_name(st) {
        Err(e) => Err(e),
        Ok(rn) => {
            if c.eq2(&rn) {
                match pin_nat(st) {
                    Err(e) => Err(e),
                    Ok(nn) => match nat_a(pers, st) {
                        Err(e) => Err(e),
                        Ok(na) => match ifenv_find(pers, fe, &nn) {
                            Some(ci) => Ok(i_constant_info_beq(ci, &na)),
                            None => Ok(false),
                        },
                    },
                }
            } else {
                reduce_elem_ok_bool(pers, st, fe)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:162-172 reduceElemOk
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::reduce_elem_ok_bool_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:125-137 reduceElemOk` — the
/// `Bool` branch: a standardly-shaped stored `Bool` inductive.
pub fn reduce_elem_ok_bool(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match bool_name(st) {
        Err(e) => Err(e),
        Ok(bn) => match ifenv_find(pers, fe, &bn) {
            Some(IConstantInfo::IndInfo(cv_b, _)) => {
                let cv = crate::arena::env::i_constant_val_dup(cv_b);
                match bool_cv_a(pers, st) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(i_constant_val_matches_pin(&cv, &p)),
                }
            }
            _ => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:174-184 ofReduceAxOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:292-298 ofReduceAxOkF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:139-148 ofReduceAxOk` — is
/// this checked axiom a pinned `ofReduce*` over a standardly-shaped
/// environment?
pub fn of_reduce_ax_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match of_reduce_op(st, &cv.name) {
        Err(e) => Err(e),
        Ok(c) => match eq_stored(pers, st, fe) {
            Err(e) => Err(e),
            Ok(b) => {
                if !b {
                    Ok(false)
                } else {
                    of_reduce_ax_ok_rest(pers, st, fe, cv, &c)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:174-184 ofReduceAxOk
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:139-148 ofReduceAxOk` — the
/// element and storage guards, then the axiom's own type.
pub fn of_reduce_ax_ok_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_elem_ok(pers, st, fe, c) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match reduce_stored_ok(pers, st, fe, c) {
                    Err(e) => Err(e),
                    Ok(b2) => {
                        if !b2 {
                            Ok(false)
                        } else {
                            match of_reduce_pin_a(pers, st, &cv.name) {
                                Err(e) => Err(e),
                                Ok(p) => Ok(i_constant_val_matches_pin(cv, &p)),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:195-199 reducePinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:300-304 reducePinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:150-158 reducePinGuard` —
/// syntactic guards on the generated reduce pin (checked once).
pub fn reduce_pin_guard(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match reduce_decl_pin(pers, st, c) {
        Err(e) => Err(e),
        Ok(p) => ground_guards(pers, st, fe, &p),
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:195-199 reducePinGuard
/// con-leche: ConLeche/Kernel/Checker.lean:310-320 divModPinGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:150-158 reducePinGuard` (and
/// `groundGuards`, the same four on a different pin) — closed,
/// free-variable-free, level-monomorphic and resolving.  The twin writes the
/// four out twice; one function here.
pub fn ground_guards(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    p: &EIdx,
) -> Result<bool, CheckError> {
    match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, p) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match has_fvar_fast(pers, st, CORE_WALK_FUEL, p) {
                    Err(e) => Err(e),
                    Ok(f) => {
                        if f {
                            Ok(false)
                        } else {
                            ground_guards_rest(pers, st, fe, p)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:195-199 reducePinGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:150-158 reducePinGuard` — the
/// two semantic guards, past the two syntactic ones.
pub fn ground_guards_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    p: &EIdx,
) -> Result<bool, CheckError> {
    let empty: Vec<NIdx> = Vec::new();
    match all_level_params_defined(pers, st, &empty, p) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                Ok(false)
            } else {
                consts_resolve_f_fast(pers, st, fe, p)
            }
        }
    }
}

/// con-leche: none — `(natOpDeps c).all (natOpStoredOk fe)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:160-168 natOpStoredOkAll` —
/// an explicit list recursion (DESIGN.md §3.4 forbids the closure `List.all`
/// takes).  con-leche's `natOpGuard` has the WEAKER dependency test; this is
/// the stronger one `divModEnvGuard` asks for, which pins the type too.
pub fn nat_op_stored_ok_all(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(true)
    } else {
        match nat_op_stored_ok(pers, st, fe, &ns[i]) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    nat_op_stored_ok_all(pers, st, fe, ns, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The `Nat.div`/`Nat.mod` pin variants (`DeclCheck.lean:170-199` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:113-125 divModDeclPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:181-192 divModDeclPin` — the
/// pinned defining expression of a pin-certified WF-recursive op in one pin
/// variant.  con-leche's `c = natDivName` chain is a handle comparison here.
pub fn div_mod_decl_pin(
    st: &mut AState,
    ps: &INatOpPinSet,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    match div_mod_slot(st, c) {
        Err(e) => Err(e),
        Ok(0) => Ok(ps.div_pin.dup2()),
        Ok(1) => Ok(ps.gcd_pin.dup2()),
        Ok(2) => Ok(ps.land_pin.dup2()),
        Ok(3) => Ok(ps.lor_pin.dup2()),
        Ok(4) => Ok(ps.xor_pin.dup2()),
        Ok(5) => Ok(ps.shift_left_pin.dup2()),
        Ok(6) => Ok(ps.shift_right_pin.dup2()),
        Ok(_) => Ok(ps.mod_pin.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:113-125 divModDeclPin
/// con-leche: ConLeche/Kernel/Checker.lean:127-137 divModCertProofs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:181-192 divModDeclPin` — the
/// twin's seven-way `if c == …` chain, once: both `divModDeclPin` and
/// `divModCertProofs` walk it, and over handles each test interns a name.
/// `7` is the `else` arm, `Nat.mod`.
pub fn div_mod_slot(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_div_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(0)
            } else {
                div_mod_slot_1(st, c)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:113-125 divModDeclPin
/// The chain's second test onward (`gcd`, `land`, `lor`).
pub fn div_mod_slot_1(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_gcd_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(1)
            } else {
                match nat_land_name(st) {
                    Err(e) => Err(e),
                    Ok(n2) => {
                        if c.eq2(&n2) {
                            Ok(2)
                        } else {
                            match nat_lor_name(st) {
                                Err(e) => Err(e),
                                Ok(n3) => {
                                    if c.eq2(&n3) {
                                        Ok(3)
                                    } else {
                                        div_mod_slot_2(st, c)
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

/// con-leche: ConLeche/Kernel/Checker.lean:113-125 divModDeclPin
/// The chain's last three tests (`xor`, `shiftLeft`, `shiftRight`) and the
/// `else` arm.
pub fn div_mod_slot_2(st: &mut AState, c: &NIdx) -> Result<u64, CheckError> {
    match nat_xor_name(st) {
        Err(e) => Err(e),
        Ok(n) => {
            if c.eq2(&n) {
                Ok(4)
            } else {
                match nat_shift_left_name(st) {
                    Err(e) => Err(e),
                    Ok(n2) => {
                        if c.eq2(&n2) {
                            Ok(5)
                        } else {
                            match nat_shift_right_name(st) {
                                Err(e) => Err(e),
                                Ok(n3) => {
                                    if c.eq2(&n3) {
                                        Ok(6)
                                    } else {
                                        Ok(7)
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

/// con-leche: ConLeche/Kernel/Checker.lean:127-137 divModCertProofs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:194-205 divModCertProofs` —
/// the certificate proof terms of a pin-certified WF-recursive op in one pin
/// variant, one per statement of `divModCertStmts`.
pub fn div_mod_cert_proofs(
    st: &mut AState,
    ps: &INatOpPinSet,
    c: &NIdx,
) -> Result<Vec<EIdx>, CheckError> {
    match div_mod_slot(st, c) {
        Err(e) => Err(e),
        Ok(0) => Ok(crate::arena::env::eidx_vec_dup(&ps.div_proofs)),
        Ok(1) => Ok(crate::arena::env::eidx_vec_dup(&ps.gcd_proofs)),
        Ok(2) => Ok(crate::arena::env::eidx_vec_dup(&ps.land_proofs)),
        Ok(3) => Ok(crate::arena::env::eidx_vec_dup(&ps.lor_proofs)),
        Ok(4) => Ok(crate::arena::env::eidx_vec_dup(&ps.xor_proofs)),
        Ok(5) => Ok(crate::arena::env::eidx_vec_dup(&ps.shift_left_proofs)),
        Ok(6) => Ok(crate::arena::env::eidx_vec_dup(&ps.shift_right_proofs)),
        Ok(_) => Ok(crate::arena::env::eidx_vec_dup(&ps.mod_proofs)),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:139-151 divModTypePins
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:207-219 divModTypePins` — the type
/// pins of a pin-certified WF-recursive op in one pin variant: the constants
/// its certificates use whose types differ between supported toolchains, each
/// with its type in this variant's toolchain.  Borrowed from the variant, not
/// copied: the gate only reads them.
pub fn div_mod_type_pins<'a>(
    st: &mut AState,
    ps: &'a INatOpPinSet,
    c: &NIdx,
) -> Result<&'a Vec<(NIdx, EIdx)>, CheckError> {
    match div_mod_slot(st, c) {
        Err(e) => Err(e),
        Ok(0) => Ok(&ps.div_type_pins),
        Ok(1) => Ok(&ps.gcd_type_pins),
        Ok(2) => Ok(&ps.land_type_pins),
        Ok(3) => Ok(&ps.lor_type_pins),
        Ok(4) => Ok(&ps.xor_type_pins),
        Ok(5) => Ok(&ps.shift_left_type_pins),
        Ok(6) => Ok(&ps.shift_right_type_pins),
        Ok(_) => Ok(&ps.mod_type_pins),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:153-160 typePinStored
/// con-leche: ConLeche/Kernel/DeclCheck.lean:328-332 typePinStoredF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:221-230 typePinStored` — the stored
/// type a type pin is compared against: the constant's type in the
/// environment.  An absent constant gives `Sort 0`, which nothing is compared
/// against: the guard (`div_mod_pin_guard`) requires every type-pinned
/// constant present.
pub fn type_pin_stored(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<EIdx, CheckError> {
    match ifenv_find(pers, fe, n) {
        Some(ci) => Ok(i_constant_info_to_constant_val(ci).ty),
        None => match zero_level(st) {
            Err(e) => Err(e),
            Ok(z) => intern_e_sort(pers, st, z),
        },
    }
}

// ---------------------------------------------------------------------------
// The pinned characterization statements (`DeclCheck.lean:201-332`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-249 eqAt1` — the
/// statements' `Eq.{1} τ a b` former.
pub fn eq_at1(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match intern_l_node(pers, st, LNodeView::Succ(z)) {
            Err(e) => Err(e),
            Ok(one) => {
                let mut us: Vec<crate::arena::handle::LIdx> = Vec::with_capacity(1);
                us.push(one);
                match intern_ls_node(pers, st, us) {
                    Err(e) => Err(e),
                    Ok(hus) => eq_at1_app(pers, st, hus, ty, a, b),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:239-249 eqAt1` — the three
/// applications, past the universe argument.
pub fn eq_at1_app(
    pers: &PersTier,
    st: &mut AState,
    hus: crate::arena::handle::LsIdx,
    ty: &EIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match pin_eq(st) {
        Err(e) => Err(e),
        Ok(en) => match intern_e_const(pers, st, en, hus) {
            Err(e) => Err(e),
            Ok(e0) => match intern_e_app(pers, st, e0, ty.dup2()) {
                Err(e) => Err(e),
                Ok(e1) => match intern_e_app(pers, st, e1, a.dup2()) {
                    Err(e) => Err(e),
                    Ok(e2) => intern_e_app(pers, st, e2, b.dup2()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:251-256 natOne` — the numeral
/// `1` as `Nat.succ Nat.zero`.
pub fn nat_one(pers: &PersTier, st: &mut AState) -> Result<EIdx, CheckError> {
    match pin_nat_succ(st) {
        Err(e) => Err(e),
        Ok(s) => match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(z) => match const_e(pers, st, &z) {
                Err(e) => Err(e),
                Ok(ze) => nat_ap1(pers, st, &s, &ze),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:258-262 natVar` — the open
/// statements' variables `x := fvar 0`, `y := fvar 1` at `Nat`.
pub fn nat_var(pers: &PersTier, st: &mut AState, i: u64) -> Result<EIdx, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match const_e(pers, st, &nt) {
            Err(e) => Err(e),
            Ok(ty) => intern_e_fvar(pers, st, i, ty),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// the twenty `let`s the twin's `do` block opens with, as one record.  Over
/// handles each of them interns, and the seven branches below read exactly as
/// the twin's; this is task #97-P4c's `NatEqCtx` treatment of
/// `natOpEquations`' eight.
pub struct CertCtx {
    pub nat_ty: EIdx,
    pub x: EIdx,
    pub y: EIdx,
    pub one: EIdx,
    pub ble_n: NIdx,
    pub bool_ty: EIdx,
    pub b_t: EIdx,
    pub b_f: EIdx,
    pub z: EIdx,
    pub two: EIdx,
    pub mod_n: NIdx,
    pub div_n: NIdx,
    pub add_n: NIdx,
    pub mul_n: NIdx,
    pub sub_n: NIdx,
    pub gcd_n: NIdx,
    pub sl_n: NIdx,
    pub sr_n: NIdx,
    pub land_n: NIdx,
    pub lor_n: NIdx,
    pub xor_n: NIdx,
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// first half of the twin's opening `let`s: the types, the variables and the
/// two `Bool` constructors.
pub fn cert_ctx(pers: &PersTier, st: &mut AState) -> Result<CertCtx, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match const_e(pers, st, &nt) {
            Err(e) => Err(e),
            Ok(nat_ty) => match nat_var(pers, st, 0) {
                Err(e) => Err(e),
                Ok(x) => match nat_var(pers, st, 1) {
                    Err(e) => Err(e),
                    Ok(y) => match nat_one(pers, st) {
                        Err(e) => Err(e),
                        Ok(one) => cert_ctx_bool(pers, st, nat_ty, x, y, one),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// `Bool` constants and the numerals `0` and `2`.
pub fn cert_ctx_bool(
    pers: &PersTier,
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
) -> Result<CertCtx, CheckError> {
    match nat_ble_name(st) {
        Err(e) => Err(e),
        Ok(ble_n) => match bool_name(st) {
            Err(e) => Err(e),
            Ok(bn) => match const_e(pers, st, &bn) {
                Err(e) => Err(e),
                Ok(bool_ty) => match bool_true_name(st) {
                    Err(e) => Err(e),
                    Ok(btn) => match const_e(pers, st, &btn) {
                        Err(e) => Err(e),
                        Ok(b_t) => match bool_false_name(st) {
                            Err(e) => Err(e),
                            Ok(bfn) => match const_e(pers, st, &bfn) {
                                Err(e) => Err(e),
                                Ok(b_f) => cert_ctx_nums(
                                    pers,
                                    st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f,
                                ),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// numerals and the eleven operation names.
pub fn cert_ctx_nums(
    pers: &PersTier,
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
) -> Result<CertCtx, CheckError> {
    match pin_nat_zero(st) {
        Err(e) => Err(e),
        Ok(zn) => match const_e(pers, st, &zn) {
            Err(e) => Err(e),
            Ok(z) => match pin_nat_succ(st) {
                Err(e) => Err(e),
                Ok(sn) => match nat_ap1(pers, st, &sn, &one) {
                    Err(e) => Err(e),
                    Ok(two) => cert_ctx_names(
                        st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f, z, two,
                    ),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// eleven operation names, in the twin's order.
pub fn cert_ctx_names(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
    z: EIdx,
    two: EIdx,
) -> Result<CertCtx, CheckError> {
    match nat_mod_name(st) {
        Err(e) => Err(e),
        Ok(mod_n) => match nat_div_name(st) {
            Err(e) => Err(e),
            Ok(div_n) => match nat_add_name(st) {
                Err(e) => Err(e),
                Ok(add_n) => match nat_mul_name(st) {
                    Err(e) => Err(e),
                    Ok(mul_n) => match nat_sub_name(st) {
                        Err(e) => Err(e),
                        Ok(sub_n) => match nat_gcd_name(st) {
                            Err(e) => Err(e),
                            Ok(gcd_n) => cert_ctx_names_rest(
                                st, nat_ty, x, y, one, ble_n, bool_ty, b_t, b_f, z, two,
                                mod_n, div_n, add_n, mul_n, sub_n, gcd_n,
                            ),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// last five names, and the record.
#[allow(clippy::too_many_arguments)]
pub fn cert_ctx_names_rest(
    st: &mut AState,
    nat_ty: EIdx,
    x: EIdx,
    y: EIdx,
    one: EIdx,
    ble_n: NIdx,
    bool_ty: EIdx,
    b_t: EIdx,
    b_f: EIdx,
    z: EIdx,
    two: EIdx,
    mod_n: NIdx,
    div_n: NIdx,
    add_n: NIdx,
    mul_n: NIdx,
    sub_n: NIdx,
    gcd_n: NIdx,
) -> Result<CertCtx, CheckError> {
    match nat_shift_left_name(st) {
        Err(e) => Err(e),
        Ok(sl_n) => match nat_shift_right_name(st) {
            Err(e) => Err(e),
            Ok(sr_n) => match nat_land_name(st) {
                Err(e) => Err(e),
                Ok(land_n) => match nat_lor_name(st) {
                    Err(e) => Err(e),
                    Ok(lor_n) => match nat_xor_name(st) {
                        Err(e) => Err(e),
                        Ok(xor_n) => Ok(CertCtx {
                            nat_ty,
                            x,
                            y,
                            one,
                            ble_n,
                            bool_ty,
                            b_t,
                            b_f,
                            z,
                            two,
                            mod_n,
                            div_n,
                            add_n,
                            mul_n,
                            sub_n,
                            gcd_n,
                            sl_n,
                            sr_n,
                            land_n,
                            lor_n,
                            xor_n,
                        }),
                    },
                },
            },
        },
    }
}

/// con-leche: none — the one-element hypothesis list `[h]` of `divModCertStmts`
/// A `Vec` literal needs a push (§3.4 has no `vec!`).
pub fn cert_hyp1(h: EIdx) -> Vec<EIdx> {
    let mut hs: Vec<EIdx> = Vec::with_capacity(1);
    hs.push(h);
    hs
}

/// con-leche: none — the two-element hypothesis list `[h1, h2]` of `divModCertStmts`
/// As `cert_hyp1`.
pub fn cert_hyp2(h1: EIdx, h2: EIdx) -> Vec<EIdx> {
    let mut hs: Vec<EIdx> = Vec::with_capacity(2);
    hs.push(h1);
    hs.push(h2);
    hs
}

/// con-leche: none — the certificate list of `divModCertStmts`
/// One cons onto the statement list, as a function (§3.4 has no `vec!`).
pub fn cert_push(
    out: Vec<(Vec<EIdx>, EIdx)>,
    hyps: Vec<EIdx>,
    eq: EIdx,
) -> Vec<(Vec<EIdx>, EIdx)> {
    let mut out2 = out;
    out2.push((hyps, eq));
    out2
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// twin's `eqAt1 boolTy (← natAp2 bleN a b) r`, the guard shape all seven
/// branches are written with.
pub fn cert_guard(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    a: &EIdx,
    b: &EIdx,
    r: &EIdx,
) -> Result<EIdx, CheckError> {
    match nat_ap2(pers, st, &cx.ble_n, a, b) {
        Err(e) => Err(e),
        Ok(g) => {
            let bt = cx.bool_ty.dup2();
            eq_at1(pers, st, &bt, &g, r)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// twin's `eqAt1 natTy (← natAp2 c x y) rhs`, the characteristic equation all
/// seven branches are written with.
pub fn cert_eq(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    rhs: &EIdx,
) -> Result<EIdx, CheckError> {
    let x = cx.x.dup2();
    let y = cx.y.dup2();
    match nat_ap2(pers, st, c, &x, &y) {
        Err(e) => Err(e),
        Ok(lhs) => {
            let nt = cx.nat_ty.dup2();
            eq_at1(pers, st, &nt, &lhs, rhs)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// bitwise branches' `op2 (div2 x two) (div2 y two)`, written three times in
/// the twin.
pub fn cert_halves(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError>  {
    let (x, y, two, dn) = (cx.x.dup2(), cx.y.dup2(), cx.two.dup2(), cx.div_n.dup2());
    match nat_ap2(pers, st, &dn, &x, &two) {
        Err(e) => Err(e),
        Ok(hx) => match nat_ap2(pers, st, &dn, &y, &two) {
            Err(e) => Err(e),
            Ok(hy) => nat_ap2(pers, st, c, &hx, &hy),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// **the pinned characterization statements** of a pin-certified WF-recursive
/// op, in *open* form over `x := fvar 0`, `y := fvar 1` (the hypotheses become
/// `fvar 2, fvar 3`): per certificate, the list of hypothesis types and the
/// characteristic equation `Eq Nat lhs rhs`.  The guards are spelled with the
/// already-certified `Nat.ble` and the numeral `1` as `Nat.succ Nat.zero`.
pub fn div_mod_cert_stmts(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_ctx(pers, st) {
        Err(e) => Err(e),
        Ok(cx) => div_mod_cert_stmts_at(pers, st, &cx, c),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// seven-way branch, in the twin's order.
pub fn div_mod_cert_stmts_at(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    if c.eq2(&cx.gcd_n) {
        cert_gcd(pers, st, cx, c)
    } else if c.eq2(&cx.sl_n) {
        cert_shift_left(pers, st, cx, c)
    } else if c.eq2(&cx.sr_n) {
        cert_shift_right(pers, st, cx, c)
    } else if c.eq2(&cx.land_n) {
        cert_land(pers, st, cx, c)
    } else if c.eq2(&cx.lor_n) {
        cert_lor(pers, st, cx, c)
    } else if c.eq2(&cx.xor_n) {
        cert_xor(pers, st, cx, c)
    } else {
        cert_div_mod(pers, st, cx, c)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`.
pub fn cert_gcd(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, mn) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.mod_n.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(pers, st, &mn, &y, &x) {
                Err(e) => Err(e),
                Ok(yx) => match nat_ap2(pers, st, c, &yx, &x) {
                    Err(e) => Err(e),
                    Ok(r1) => match cert_eq(pers, st, cx, c, &r1) {
                        Err(e) => Err(e),
                        Ok(e1) => match cert_eq(pers, st, cx, c, &y) {
                            Err(e) => Err(e),
                            Ok(e2) => Ok(cert_push(
                                cert_push(Vec::new(), cert_hyp1(h1), e1),
                                cert_hyp1(h2),
                                e2,
                            )),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`.
pub fn cert_shift_left(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, mul, sub, two) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.mul_n.dup2(),
        cx.sub_n.dup2(),
        cx.two.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &y, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &y, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(pers, st, &mul, &two, &x) {
                Err(e) => Err(e),
                Ok(tx) => match nat_ap2(pers, st, &sub, &y, &one) {
                    Err(e) => Err(e),
                    Ok(y1) => match nat_ap2(pers, st, c, &tx, &y1) {
                        Err(e) => Err(e),
                        Ok(r1) => cert_two_eqs(pers, st, cx, c, h1, h2, r1, x),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// `pure [([h1], e1), ([h2], e2)]` the six non-`div`/`mod` branches end with.
pub fn cert_two_eqs(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    h1: EIdx,
    h2: EIdx,
    r1: EIdx,
    r2: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_eq(pers, st, cx, c, &r1) {
        Err(e) => Err(e),
        Ok(e1) => match cert_eq(pers, st, cx, c, &r2) {
            Err(e) => Err(e),
            Ok(e2) => Ok(cert_push(
                cert_push(Vec::new(), cert_hyp1(h1), e1),
                cert_hyp1(h2),
                e2,
            )),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`.
pub fn cert_shift_right(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, div, sub, two) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.div_n.dup2(),
        cx.sub_n.dup2(),
        cx.two.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &y, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &y, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match nat_ap2(pers, st, &sub, &y, &one) {
                Err(e) => Err(e),
                Ok(y1) => match nat_ap2(pers, st, c, &x, &y1) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap2(pers, st, &div, &inner, &two) {
                        Err(e) => Err(e),
                        Ok(r1) => cert_two_eqs(pers, st, cx, c, h1, h2, r1, x),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`, `x = 0 → … = 0`.
pub fn cert_land(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf, add, mul, mn, two, z) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
        cx.z.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_halves(pers, st, cx, c) {
                Err(e) => Err(e),
                Ok(rec1) => match nat_ap2(pers, st, &mul, &two, &rec1) {
                    Err(e) => Err(e),
                    Ok(t2) => match nat_ap2(pers, st, &mn, &x, &two) {
                        Err(e) => Err(e),
                        Ok(mx) => match nat_ap2(pers, st, &mn, &y, &two) {
                            Err(e) => Err(e),
                            Ok(my) => match nat_ap2(pers, st, &mul, &mx, &my) {
                                Err(e) => Err(e),
                                Ok(p) => match nat_ap2(pers, st, &add, &t2, &p) {
                                    Err(e) => Err(e),
                                    Ok(r1) => cert_two_eqs(pers, st, cx, c, h1, h2, r1, z),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
/// `x = 0 → x ||| y = y`.
pub fn cert_lor(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_lor_rhs(pers, st, cx, c) {
                Err(e) => Err(e),
                Ok(r1) => cert_two_eqs(pers, st, cx, c, h1, h2, r1, y),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// `lor` branch's right-hand side.
pub fn cert_lor_rhs(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    let (x, y, add, mul, sub, mn, two) = (
        cx.x.dup2(),
        cx.y.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.sub_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
    );
    match cert_halves(pers, st, cx, c) {
        Err(e) => Err(e),
        Ok(rec1) => match nat_ap2(pers, st, &mul, &two, &rec1) {
            Err(e) => Err(e),
            Ok(t2) => match nat_ap2(pers, st, &mn, &x, &two) {
                Err(e) => Err(e),
                Ok(mx) => match nat_ap2(pers, st, &mn, &y, &two) {
                    Err(e) => Err(e),
                    Ok(my) => match nat_ap2(pers, st, &add, &mx, &my) {
                        Err(e) => Err(e),
                        Ok(s) => match nat_ap2(pers, st, &mul, &mx, &my) {
                            Err(e) => Err(e),
                            Ok(p) => match nat_ap2(pers, st, &sub, &s, &p) {
                                Err(e) => Err(e),
                                Ok(d) => nat_ap2(pers, st, &add, &t2, &d),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` —
/// `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
/// `x = 0 → x ^^^ y = y`.
pub fn cert_xor(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(pers, st, cx, &one, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &x, &bf) {
            Err(e) => Err(e),
            Ok(h2) => match cert_xor_rhs(pers, st, cx, c) {
                Err(e) => Err(e),
                Ok(r1) => cert_two_eqs(pers, st, cx, c, h1, h2, r1, y),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// `xor` branch's right-hand side.
pub fn cert_xor_rhs(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    let (x, y, add, mul, mn, two) = (
        cx.x.dup2(),
        cx.y.dup2(),
        cx.add_n.dup2(),
        cx.mul_n.dup2(),
        cx.mod_n.dup2(),
        cx.two.dup2(),
    );
    match cert_halves(pers, st, cx, c) {
        Err(e) => Err(e),
        Ok(rec1) => match nat_ap2(pers, st, &mul, &two, &rec1) {
            Err(e) => Err(e),
            Ok(t2) => match nat_ap2(pers, st, &mn, &x, &two) {
                Err(e) => Err(e),
                Ok(mx) => match nat_ap2(pers, st, &mn, &y, &two) {
                    Err(e) => Err(e),
                    Ok(my) => match nat_ap2(pers, st, &add, &mx, &my) {
                        Err(e) => Err(e),
                        Ok(s) => match nat_ap2(pers, st, &mn, &s, &two) {
                            Err(e) => Err(e),
                            Ok(m) => nat_ap2(pers, st, &add, &t2, &m),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// twin's `else` branch, `Nat.div` and `Nat.mod`: three certificates, with
/// `recRhs`/`baseRhs` as the twin's two locals.
pub fn cert_div_mod(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_rec_rhs(pers, st, cx, c) {
        Err(e) => Err(e),
        Ok(rec_rhs) => {
            let base_rhs: EIdx = if c.eq2(&cx.div_n) {
                cx.z.dup2()
            } else {
                cx.x.dup2()
            };
            cert_div_mod_guards(pers, st, cx, c, rec_rhs, base_rhs)
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// twin's `recRhs`: `Nat.succ (c (x - y) y)` for `Nat.div`, `c (x - y) y` for
/// `Nat.mod`.
pub fn cert_rec_rhs(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
) -> Result<EIdx, CheckError>  {
    let (x, y, sub) = (cx.x.dup2(), cx.y.dup2(), cx.sub_n.dup2());
    match nat_ap2(pers, st, &sub, &x, &y) {
        Err(e) => Err(e),
        Ok(d) => match nat_ap2(pers, st, c, &d, &y) {
            Err(e) => Err(e),
            Ok(step) => {
                if c.eq2(&cx.div_n) {
                    match pin_nat_succ(st) {
                        Err(e) => Err(e),
                        Ok(sn) => nat_ap1(pers, st, &sn, &step),
                    }
                } else {
                    Ok(step)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// `div`/`mod` branch's four guards and three certificates.
pub fn cert_div_mod_guards(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    rec_rhs: EIdx,
    base_rhs: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    let (one, x, y, bt, bf) = (
        cx.one.dup2(),
        cx.x.dup2(),
        cx.y.dup2(),
        cx.b_t.dup2(),
        cx.b_f.dup2(),
    );
    match cert_guard(pers, st, cx, &y, &x, &bt) {
        Err(e) => Err(e),
        Ok(h1) => match cert_guard(pers, st, cx, &one, &y, &bt) {
            Err(e) => Err(e),
            Ok(h2) => match cert_guard(pers, st, cx, &y, &x, &bf) {
                Err(e) => Err(e),
                Ok(h3) => match cert_guard(pers, st, cx, &one, &y, &bf) {
                    Err(e) => Err(e),
                    Ok(h4) => {
                        cert_div_mod_eqs(pers, st, cx, c, h1, h2, h3, h4, rec_rhs, base_rhs)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:162-240 divModCertStmts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:463-475 divModCertStmts` — the
/// twin's `pure [([h1, h2], e1), ([h3], e2), ([h4], e2)]`.
#[allow(clippy::too_many_arguments)]
pub fn cert_div_mod_eqs(
    pers: &PersTier,
    st: &mut AState,
    cx: &CertCtx,
    c: &NIdx,
    h1: EIdx,
    h2: EIdx,
    h3: EIdx,
    h4: EIdx,
    rec_rhs: EIdx,
    base_rhs: EIdx,
) -> Result<Vec<(Vec<EIdx>, EIdx)>, CheckError> {
    match cert_eq(pers, st, cx, c, &rec_rhs) {
        Err(e) => Err(e),
        Ok(e1) => match cert_eq(pers, st, cx, c, &base_rhs) {
            Err(e) => Err(e),
            Ok(e2) => {
                let out = cert_push(Vec::new(), cert_hyp2(h1, h2), e1);
                let out = cert_push(out, cert_hyp1(h3), e2.dup2());
                Ok(cert_push(out, cert_hyp1(h4), e2))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The certificate checks (`DeclCheck.lean:334-537` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:242-255 divModCertApplied
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:477-495 divModCertApplied` —
/// the vendored proof applied to the statement's free variables (`x`, `y`,
/// then one `fvar` per hypothesis, carrying the hypothesis *type* as its
/// annotation — the checker's implicit local context).
pub fn div_mod_cert_applied(
    pers: &PersTier,
    st: &mut AState,
    proof_s: &EIdx,
    hyps: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    match nat_var(pers, st, 0) {
        Err(e) => Err(e),
        Ok(x) => match nat_var(pers, st, 1) {
            Err(e) => Err(e),
            Ok(y) => match intern_e_app(pers, st, proof_s.dup2(), x) {
                Err(e) => Err(e),
                Ok(b1) => match intern_e_app(pers, st, b1, y) {
                    Err(e) => Err(e),
                    Ok(base) => div_mod_cert_applied_hyps(pers, st, base, hyps),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:242-255 divModCertApplied
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:477-495 divModCertApplied` —
/// the twin's three-way `match hyps with | [h1] | [h1, h2] | _`.
pub fn div_mod_cert_applied_hyps(
    pers: &PersTier,
    st: &mut AState,
    base: EIdx,
    hyps: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    if hyps.len() == 1 {
        match intern_e_fvar(pers, st, 2, hyps[0].dup2()) {
            Err(e) => Err(e),
            Ok(f2) => intern_e_app(pers, st, base, f2),
        }
    } else if hyps.len() == 2 {
        match intern_e_fvar(pers, st, 2, hyps[0].dup2()) {
            Err(e) => Err(e),
            Ok(f2) => match intern_e_app(pers, st, base, f2) {
                Err(e) => Err(e),
                Ok(a1) => match intern_e_fvar(pers, st, 3, hyps[1].dup2()) {
                    Err(e) => Err(e),
                    Ok(f3) => intern_e_app(pers, st, a1, f3),
                },
            },
        }
    } else {
        Ok(base)
    }
}

/// con-leche: none — `hyps.map (Expr.substConst0 c annVal)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:497-504 substConst0List` — an
/// explicit list recursion (§3.4 forbids the closure).
pub fn subst_const0_list(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    hs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match subst_const0(pers, st, n, r, CORE_WALK_FUEL, &hs[i]) {
            Err(e) => Err(e),
            Ok(h) => {
                let mut out2 = out;
                out2.push(h);
                subst_const0_list(pers, st, n, r, hs, i + 1, out2)
            }
        }
    }
}

/// con-leche: none — `(hyps.map …).all (fun h => h.constsResolveF fe)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:506-511 constsResolveAll` — an
/// explicit list recursion.
pub fn consts_resolve_all(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    hs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= hs.len() {
        Ok(true)
    } else {
        match consts_resolve_f_fast(pers, st, fe, &hs[i]) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    consts_resolve_all(pers, st, fe, hs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:257-268 divModCertGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:317-326 divModCertGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:513-527 divModCertGuard` — the
/// syntactic guards of one certificate check: the substituted proof is closed,
/// level-monomorphic and resolving, and the substituted statement components
/// resolve.
pub fn div_mod_cert_guard(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    hyps: &Vec<EIdx>,
    eq_e: &EIdx,
    proof: &EIdx,
) -> Result<bool, CheckError> {
    match subst_const_all(pers, st, c, ann_val, CORE_WALK_FUEL, proof) {
        Err(e) => Err(e),
        Ok(p) => match ground_guards(pers, st, fe, &p) {
            Err(e) => Err(e),
            Ok(g) => {
                if !g {
                    Ok(false)
                } else {
                    div_mod_cert_guard_rest(pers, st, fe, c, ann_val, hyps, eq_e)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:257-268 divModCertGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:513-527 divModCertGuard` — the
/// two statement-component guards, past the proof's four.
pub fn div_mod_cert_guard_rest(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    hyps: &Vec<EIdx>,
    eq_e: &EIdx,
) -> Result<bool, CheckError> {
    match subst_const0_list(pers, st, c, ann_val, hyps, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(hs) => match consts_resolve_all(pers, st, fe, &hs, 0) {
            Err(e) => Err(e),
            Ok(r) => {
                if !r {
                    Ok(false)
                } else {
                    match subst_const0(pers, st, c, ann_val, CORE_WALK_FUEL, eq_e) {
                        Err(e) => Err(e),
                        Ok(q) => consts_resolve_f_fast(pers, st, fe, &q),
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:295-308 divModEnvGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:306-315 divModEnvGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:544-555 divModEnvGuard` —
/// environment prerequisites of a certified `Nat.div`/`Nat.mod`: dependency
/// guard, pinned dependencies, the pinned `Eq` basis, and the `Bool`
/// constructors stored at the type `Bool` itself.
pub fn div_mod_env_guard(
    pers: &PersTier,
    st: &mut AState,
    fe2: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match nat_op_guard(pers, st, fe2, c) {
        Err(e) => Err(e),
        Ok(g) => {
            if !g {
                Ok(false)
            } else {
                match nat_op_deps(st, c) {
                    Err(e) => Err(e),
                    Ok(deps) => match nat_op_stored_ok_all(pers, st, fe2, &deps, 0) {
                        Err(e) => Err(e),
                        Ok(d) => {
                            if !d {
                                Ok(false)
                            } else {
                                div_mod_env_guard_rest(pers, st, fe2)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:295-308 divModEnvGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:544-555 divModEnvGuard` — the
/// pinned `Eq` basis and the two `Bool` constructors.
pub fn div_mod_env_guard_rest(
    pers: &PersTier,
    st: &mut AState,
    fe2: &IFEnv,
) -> Result<bool, CheckError>  {
    match eq_stored(pers, st, fe2) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                Ok(false)
            } else {
                match bool_true_name(st) {
                    Err(e) => Err(e),
                    Ok(btn) => match bool_ctor_typed(pers, st, fe2, &btn) {
                        Err(e) => Err(e),
                        Ok(t) => {
                            if !t {
                                Ok(false)
                            } else {
                                match bool_false_name(st) {
                                    Err(e) => Err(e),
                                    Ok(bfn) => bool_ctor_typed(pers, st, fe2, &bfn),
                                }
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:295-308 divModEnvGuard
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:544-555 divModEnvGuard` — the
/// twin's `(← ci.toConstantVal).type != boolTy`, which it spells twice: the
/// guards' `true`/`false` must inhabit the `Bool` value semantically.
pub fn bool_ctor_typed(
    pers: &PersTier,
    st: &mut AState,
    fe2: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError> {
    match ifenv_find(pers, fe2, n) {
        Some(ci) => {
            let c = i_constant_info_dup(ci);
            {
                let cv: IConstantVal = i_constant_info_to_constant_val(&c);
                match bool_name(st) {
                    Err(e) => Err(e),
                    Ok(bn) => match const_e(pers, st, &bn) {
                        Err(e) => Err(e),
                        Ok(bool_ty) => Ok(cv.ty.eq2(&bool_ty)),
                    },
                }
            }
        }
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:310-320 divModPinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:334-341 divModPinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:590-599 divModPinGuard` — syntactic
/// guards on one variant's pin (generated; checked once rather
/// than proven about the blob), and on its type pins: each type-pinned
/// constant stored with a closed type, each pinned type closed over constants
/// the stream declares.
pub fn div_mod_pin_guard(
    pers: &PersTier,
    st: &mut AState,
    ps: &INatOpPinSet,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError> {
    match div_mod_decl_pin(st, ps, c) {
        Err(e) => Err(e),
        Ok(p) => match ground_guards(pers, st, fe, &p) {
            Err(e) => Err(e),
            Ok(g) => {
                if g {
                    match div_mod_type_pins(st, ps, c) {
                        Err(e) => Err(e),
                        Ok(tps) => type_pins_guard(pers, st, fe, tps, 0),
                    }
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:310-320 divModPinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:334-341 divModPinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:580-588 typePinsGuard` — the cited
/// `(divModTypePins ps c).all fun p => …` as a cursor recursion (DESIGN.md
/// §3.4 forbids the closure `List.all` takes).
pub fn type_pins_guard(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    tps: &Vec<(NIdx, EIdx)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= tps.len() {
        Ok(true)
    } else {
        match type_pin_guard(pers, st, fe, &tps[i].0, &tps[i].1) {
            Err(e) => Err(e),
            Ok(g) => {
                if g {
                    type_pins_guard(pers, st, fe, tps, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:310-320 divModPinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:334-341 divModPinGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:567-578 typePinGuard` — one type
/// pin's guard, the `List.all` closure's body: the constant stored, its
/// stored type free of free variables, the pinned type closed, free of free
/// variables and resolving.
pub fn type_pin_guard(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
    ty: &EIdx,
) -> Result<bool, CheckError> {
    if ifenv_find(pers, fe, n).is_some() {
        match type_pin_stored(pers, st, fe, n) {
            Err(e) => Err(e),
            Ok(stored) => match has_fvar_fast(pers, st, CORE_WALK_FUEL, &stored) {
                Err(e) => Err(e),
                Ok(f) => {
                    if f {
                        Ok(false)
                    } else {
                        match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, ty) {
                            Err(e) => Err(e),
                            Ok(b) => {
                                if !b {
                                    Ok(false)
                                } else {
                                    match has_fvar_fast(pers, st, CORE_WALK_FUEL, ty) {
                                        Err(e) => Err(e),
                                        Ok(f2) => {
                                            if f2 {
                                                Ok(false)
                                            } else {
                                                consts_resolve_f_fast(pers, st, fe, ty)
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:322-329 divModCertsGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:343-347 divModCertsGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:601-613 divModCertsGuardGo` —
/// all of one variant's certificates' syntactic guards at once, `zip`ped with
/// the statements.  A `zip` stops at the shorter list, which is why the bound
/// is the minimum (the twin's two `[]` clauses are both `true`).
pub fn div_mod_certs_guard_go(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= stmts.len() || i >= proofs.len() {
        Ok(true)
    } else {
        match div_mod_cert_guard(
            pers,
            st,
            fe,
            c,
            ann_val,
            &stmts[i].0,
            &stmts[i].1,
            &proofs[i],
        ) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    div_mod_certs_guard_go(pers, st, fe, c, ann_val, stmts, proofs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:322-329 divModCertsGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:343-347 divModCertsGuardF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:615-621 divModCertsGuard` —
/// the statements and the variant's proofs, zipped.
pub fn div_mod_certs_guard(
    pers: &PersTier,
    st: &mut AState,
    ps: &INatOpPinSet,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
) -> Result<bool, CheckError> {
    match div_mod_cert_stmts(pers, st, c) {
        Err(e) => Err(e),
        Ok(stmts) => match div_mod_cert_proofs(st, ps, c) {
            Err(e) => Err(e),
            Ok(proofs) => div_mod_certs_guard_go(pers, st, fe, c, ann_val, &stmts, &proofs, 0),
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:270-293 checkDivModCerts
/// con-leche: ConLeche/Kernel/DeclCheck.lean:392-406 checkDivModCertsF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:623-644 checkDivModCerts` —
/// check the pinned certificates of op `c`: per certificate, the vendored
/// proof (with the op's self-references replaced by the stored value
/// — the checks run in the *pre-insertion* environment) is applied to free
/// variables typed by the pinned open statement, its type inferred, and
/// compared against the pinned characteristic equation.  The twin's
/// two-`List` recursion is one index recursion; its `_, _ => pure false` is
/// the length mismatch.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_certs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= stmts.len() && i >= proofs.len() {
        Ok(true)
    } else if i >= stmts.len() || i >= proofs.len() {
        Ok(false)
    } else {
        match div_mod_cert_guard(pers, st, fe, c, ann_val, &stmts[i].0, &stmts[i].1, &proofs[i]) {
            Err(e) => Err(e),
            Ok(g) => {
                if !g {
                    Ok(false)
                } else {
                    check_div_mod_cert_at(pers, st, mode, fe, c, ann_val, stmts, proofs, i)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:270-293 checkDivModCerts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:623-644 checkDivModCerts` —
/// one certificate, past its guard: the substituted proof applied, then
/// inferred and compared.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_cert_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    match subst_const_all(pers, st, c, ann_val, CORE_WALK_FUEL, &proofs[i]) {
        Err(e) => Err(e),
        Ok(p) => match subst_const0_list(pers, st, c, ann_val, &stmts[i].0, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(hs) => match div_mod_cert_applied(pers, st, &p, &hs) {
                Err(e) => Err(e),
                Ok(applied) => {
                    check_div_mod_cert_tail(pers, st, mode, fe, c, ann_val, stmts, proofs, i, applied)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:270-293 checkDivModCerts
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:623-644 checkDivModCerts` —
/// the inference and the comparison, then the next certificate.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_cert_tail(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    ann_val: &EIdx,
    stmts: &Vec<(Vec<EIdx>, EIdx)>,
    proofs: &Vec<EIdx>,
    i: usize,
    applied_a: EIdx,
) -> Result<bool, CheckError> {
    match infer_type_core(pers, st, mode, fe, CHECK_FUEL, 4, &applied_a) {
        Err(e) => Err(e),
        Ok(tp) => match subst_const0(pers, st, c, ann_val, CORE_WALK_FUEL, &stmts[i].1) {
            Err(e) => Err(e),
            Ok(rhs) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 4, &tp, &rhs) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        check_div_mod_certs(pers, st, mode, fe, c, ann_val, stmts, proofs, i + 1)
                    } else {
                        Ok(false)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:331-339 checkTypePins
/// con-leche: ConLeche/Kernel/DeclCheck.lean:408-415 checkTypePinsF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:646-655 checkTypePins` — the type
/// pins: each type-pinned constant's stored type against the variant's pinned
/// one, by definitional equality; the cited list recursion as a cursor.
#[allow(clippy::too_many_arguments)]
pub fn check_type_pins(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    tps: &Vec<(NIdx, EIdx)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= tps.len() {
        Ok(true)
    } else {
        match type_pin_stored(pers, st, fe, &tps[i].0) {
            Err(e) => Err(e),
            Ok(stored) => {
                match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, &stored, &tps[i].1) {
                    Err(e) => Err(e),
                    Ok(ok) => {
                        if ok {
                            check_type_pins(pers, st, mode, fe, tps, i + 1)
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:341-368 checkDivModPinAt
/// con-leche: ConLeche/Kernel/DeclCheck.lean:417-427 checkDivModPinAtF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:670-681 checkDivModPinAt` — **one pin
/// variant's attempt**: the variant's type pins (`check_type_pins`), then the
/// stored value against the variant's pin by definitional equality, and on a
/// match the variant's certificates.  `true` = matched; `false` = a type pin
/// or the pin is not definitionally equal, or a certificate did not check.
/// Every outcome is a boolean; an error is the run's.
pub fn check_div_mod_pin_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    ps: &INatOpPinSet,
) -> Result<bool, CheckError> {
    match div_mod_type_pins(st, ps, c) {
        Err(e) => Err(e),
        Ok(tps) => match check_type_pins(pers, st, mode, fe, tps, 0) {
            Err(e) => Err(e),
            Ok(ok_types) => {
                if ok_types {
                    check_div_mod_pin_value(pers, st, mode, fe, c, value2, ps)
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:341-368 checkDivModPinAt
/// con-leche: ConLeche/Kernel/DeclCheck.lean:417-427 checkDivModPinAtF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:657-668 checkDivModPinValue` — the
/// attempt past its type pins: the value pin, and on a match the
/// certificates.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_value(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    ps: &INatOpPinSet,
) -> Result<bool, CheckError> {
    match div_mod_decl_pin(st, ps, c) {
        Err(e) => Err(e),
        Ok(pin_a) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, value2, &pin_a) {
            Err(e) => Err(e),
            Ok(ok_pin) => {
                if ok_pin {
                    check_div_mod_pin_certs(pers, st, mode, fe, c, value2, ps)
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:341-368 checkDivModPinAt
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:657-668 checkDivModPinValue`'s tail —
/// the certificates, past the pin comparison.
pub fn check_div_mod_pin_certs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    ps: &INatOpPinSet,
) -> Result<bool, CheckError> {
    match div_mod_cert_stmts(pers, st, c) {
        Err(e) => Err(e),
        Ok(stmts) => match div_mod_cert_proofs(st, ps, c) {
            Err(e) => Err(e),
            Ok(proofs) => {
                check_div_mod_certs(pers, st, mode, fe, c, value2, &stmts, &proofs, 0)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:376-396 checkDivModPinLoop
/// con-leche: ConLeche/Kernel/DeclCheck.lean:429-444 checkDivModPinLoopF
/// con-leche: ConLeche/Kernel/Checker.lean:370-374 divModAttemptReason
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:689-717 checkDivModPinLoop` — **the
/// variant loop**: the first variant whose guards pass and whose attempt
/// succeeds enables the fast path; every other outcome moves on to the next
/// variant, and when none is left the stream DECLINES.  Every step is a
/// boolean decision — the guards, then the attempt's `true`/`false`
/// (`check_div_mod_pin_at`, in `check_div_mod_pin_try`) — and an error from
/// either is the run's.  The two guards short-circuit as the cited `&&` of
/// two pure `Bool`s does: a variant whose pin guard fails never walks its
/// certificates.
///
/// Deviation: the cited loop accumulates one reason per variant
/// (`divModAttemptReason`, the ground-constants text) for the decline
/// message; the port declines with one fixed message, `M_DIVMOD_NO_VARIANT`
/// (§3.1: a message need not match, and the theorem relates an error by its
/// kind).
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_loop(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    variants: &Vec<INatOpPinSet>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= variants.len() {
        fail(CheckError::NotImplemented(code_points(&M_DIVMOD_NO_VARIANT)))
    } else {
        match div_mod_pin_guard(pers, st, &variants[i], fe, c) {
            Err(e) => Err(e),
            Ok(g1) => {
                if g1 {
                    match div_mod_certs_guard(pers, st, &variants[i], fe, c, value2) {
                        Err(e) => Err(e),
                        Ok(g2) => {
                            if g2 {
                                check_div_mod_pin_try(pers, st, mode, fe, c, value2, variants, i)
                            } else {
                                check_div_mod_pin_loop(
                                    pers, st, mode, fe, c, value2, variants, i + 1,
                                )
                            }
                        }
                    }
                } else {
                    check_div_mod_pin_loop(pers, st, mode, fe, c, value2, variants, i + 1)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:376-396 checkDivModPinLoop
/// con-leche: ConLeche/Kernel/DeclCheck.lean:429-444 checkDivModPinLoopF
/// Lean twin: the inner `if` of `proof/ConRon/Arena/DeclCheck.lean:689-717
/// checkDivModPinLoop` — the loop's step at a variant whose guards passed:
/// the attempt, then the loop's tail call on `false`.
#[allow(clippy::too_many_arguments)]
pub fn check_div_mod_pin_try(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value2: &EIdx,
    variants: &Vec<INatOpPinSet>,
    i: usize,
) -> Result<(), CheckError> {
    match check_div_mod_pin_at(pers, st, mode, fe, c, value2, &variants[i]) {
        Err(e) => Err(e),
        Ok(ok) => {
            if ok {
                Ok(())
            } else {
                check_div_mod_pin_loop(pers, st, mode, fe, c, value2, variants, i + 1)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:398-424 checkDivModPin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:446-456 checkDivModPinF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:731-748 checkDivModPin` — the
/// pin-certified operations' gate: the environment guards and the stored value
/// at `fe2`, the environment with the definition, then the variant loop at
/// `fe`, the one without it.  The variant list is its parameter (con-leche's
/// task #304).
///
/// Deviation: the cited `fe2` is `fe.overlay [ci]` (`checkDeclC`'s argument),
/// passed as `ci`: the port pushes it in place for the two reads at `fe2` and
/// pops it before the loop (`ifenv_push_temp`/`ifenv_pop_temp`, the port's
/// overlay), since `IFEnv` has no cheap copy.
pub fn check_div_mod_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    pins: &Vec<INatOpPinSet>,
    fe: &mut IFEnv,
    ci: &IConstantInfo,
    c: &NIdx,
) -> Result<(), CheckError> {
    let prev: Option<u64> = ifenv_push_temp(fe, i_constant_info_dup(ci));
    let at_fe2: Result<EIdx, CheckError> = check_div_mod_pin_at_fe2(pers, st, fe, c);
    ifenv_pop_temp(fe, c, prev);
    match at_fe2 {
        Err(e) => Err(e),
        Ok(value2) => check_div_mod_pin_loop(pers, st, mode, fe, c, &value2, pins, 0),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:398-424 checkDivModPin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:446-456 checkDivModPinF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:731-748 checkDivModPin` — the two reads
/// at `fe2`: `divModEnvGuardF fe2 c`, then the stored definition's value.
pub fn check_div_mod_pin_at_fe2(
    pers: &PersTier,
    st: &mut AState,
    fe2: &IFEnv,
    c: &NIdx,
) -> Result<EIdx, CheckError> {
    match div_mod_env_guard(pers, st, fe2, c) {
        Err(e) => Err(e),
        Ok(g) => {
            if !g {
                fail(CheckError::NotImplemented(code_points(&M_DIVMOD_ENV)))
            } else {
                match defn_value(pers, fe2, c) {
                    None => fail(CheckError::Internal(code_points(&M_DIVMOD_NOT_STORED))),
                    Some(value2) => Ok(value2),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:398-424 checkDivModPin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:731-748 checkDivModPin` — the
/// twin's `match fe2.find? c with | some (.defnInfo _ value' _)`: the stored
/// definition's value, COPIED before the state is taken mutably (task #14's
/// rule).
pub fn defn_value(pers: &PersTier, fe: &IFEnv, c: &NIdx) -> Option<EIdx> {
    match ifenv_find(pers, fe, c) {
        Some(IConstantInfo::DefnInfo(_, v, _)) => Some(v.dup2()),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:426-461 checkReducePin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:458-477 checkReducePinF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:776-795 checkReducePin` — the
/// `Lean.reduceNat`/`Lean.reduceBool` gate, after the ordinary opaque check:
/// the stored constant carries the pinned type (at `fe2`, the environment with
/// it), the witness value is definitionally equal to the build-time pin, and
/// the *identity certificate* `value x ≡ x` over an opened `fvar` at the element
/// type holds (at `fe`).
///
/// Deviation: as `check_div_mod_pin`, `fe2` is `fe.overlay [ci]`, pushed in
/// place for its one read and popped.
pub fn check_reduce_pin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &mut IFEnv,
    ci: &IConstantInfo,
    c: &NIdx,
    value: &EIdx,
) -> Result<(), CheckError> {
    let prev: Option<u64> = ifenv_push_temp(fe, i_constant_info_dup(ci));
    let stored: Result<bool, CheckError> = reduce_stored_ok(pers, st, fe, c);
    ifenv_pop_temp(fe, c, prev);
    match stored {
        Err(e) => Err(e),
        Ok(s) => {
            if !s {
                fail(CheckError::NotImplemented(code_points(&M_REDUCE_DECL)))
            } else {
                check_reduce_pin_pre(pers, st, mode, fe, c, value)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:426-461 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:776-795 checkReducePin` — the
/// body at `fe`, the environment without the opaque: the element guard, the pin's own syntactic
/// guards, the definitional comparison of the witness against the pin, and the
/// identity certificate.
pub fn check_reduce_pin_pre(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value: &EIdx,
) -> Result<(), CheckError> {
    match reduce_elem_ok(pers, st, fe, c) {
        Err(e) => Err(e),
        Ok(el) => {
            if !el {
                fail(CheckError::NotImplemented(code_points(&M_REDUCE_DECL)))
            } else {
                match reduce_pin_guard(pers, st, fe, c) {
                    Err(e) => Err(e),
                    Ok(g) => {
                        if !g {
                            fail(CheckError::NotImplemented(code_points(
                                &M_REDUCE_PIN_ABSENT,
                            )))
                        } else {
                            check_reduce_pin_value(pers, st, mode, fe, c, value)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:426-461 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:776-795 checkReducePin` — the
/// witness and the pin, compared.
pub fn check_reduce_pin_value(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    value: &EIdx,
) -> Result<(), CheckError> {
    match reduce_decl_pin(pers, st, c) {
        Err(e) => Err(e),
        Ok(pin_a) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, value, &pin_a) {
            Err(e) => Err(e),
            Ok(ok_pin) => {
                if ok_pin {
                    check_reduce_identity(pers, st, mode, fe, c, value)
                } else {
                    fail(CheckError::NotImplemented(code_points(&M_REDUCE_SPELLING)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:426-461 checkReducePin
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:776-795 checkReducePin` — the
/// identity certificate: `valA x ≡ x` at depth 1 over `reduceCertVar`.
pub fn check_reduce_identity(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    c: &NIdx,
    val_a: &EIdx,
) -> Result<(), CheckError> {
    match reduce_cert_var(pers, st, c) {
        Err(e) => Err(e),
        Ok(x) => match intern_e_app(pers, st, val_a.dup2(), x.dup2()) {
            Err(e) => Err(e),
            Ok(ax) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 1, &ax, &x) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(())
                    } else {
                        fail(CheckError::Internal(code_points(&M_REDUCE_NOT_ID)))
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The structural-`Nat` recurrence certification (`DeclCheck.lean:566-587`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:103-111 certifyNatEqs
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:799-808 certifyNatEqs` —
/// certify a list of recurrence equations by definitional equality (at depth 2:
/// the equations' variables are `fvar 0`/`fvar 1`).
pub fn certify_nat_eqs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    eqs: &Vec<(EIdx, EIdx)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= eqs.len() {
        Ok(true)
    } else {
        match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 2, &eqs[i].0, &eqs[i].1) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    certify_nat_eqs(pers, st, mode, fe, eqs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: none — `(natOpEquations 0 c).map fun eq => (substConst0 …, substConst0 …)`
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:810-818 substConst0Pairs` — an
/// explicit list recursion.
pub fn subst_const0_pairs(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    eqs: &Vec<(EIdx, EIdx)>,
    i: usize,
    out: Vec<(EIdx, EIdx)>,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    if i >= eqs.len() {
        Ok(out)
    } else {
        match subst_const0(pers, st, n, r, CORE_WALK_FUEL, &eqs[i].0) {
            Err(e) => Err(e),
            Ok(a) => match subst_const0(pers, st, n, r, CORE_WALK_FUEL, &eqs[i].1) {
                Err(e) => Err(e),
                Ok(b) => {
                    let mut out2 = out;
                    out2.push((a, b));
                    subst_const0_pairs(pers, st, n, r, eqs, i + 1, out2)
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The three value kinds' full checks
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"loose bound variable in value"`, as code points.
pub const M_LOOSE_VALUE: [u32; 29] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unexpected free variable in value"`, as code points.
pub const M_FVAR_VALUE: [u32; 33] = [
    117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"undeclared universe parameter in value"`, as code points.
pub const M_UNDECL_VALUE: [u32; 38] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type of theorem is not a proposition"`, as code points.
pub const M_THM_NOT_PROP: [u32; 36] = [
    116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in definition"`, as code points.
pub const M_TYPE_MISMATCH_DEFN: [u32; 27] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in theorem"`, as code points.
pub const M_TYPE_MISMATCH_THM: [u32; 24] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 104, 101, 111, 114, 101, 109,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"type mismatch in opaque"`, as code points.
pub const M_TYPE_MISMATCH_OPAQUE: [u32; 23] = [
    116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 111, 112, 97, 113, 117, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"reserved basis name: the block is not the pinned one"`, as code points.
pub const M_BASIS_NOT_PIN: [u32; 52] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101, 58, 32, 116, 104, 101, 32, 98, 108, 111, 99, 107, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32, 111, 110, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient soundness axiom mismatch"`, as code points.
pub const M_QUOT_SOUND_MISMATCH: [u32; 33] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 115, 111, 117, 110, 100, 110, 101, 115, 115, 32, 97, 120, 105, 111, 109, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient declaration mismatch"`, as code points.
pub const M_QUOT_DECL_MISMATCH: [u32; 29] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"quotient declaration before what it needs"`, as code points.
pub const M_QUOT_PREDS: [u32; 41] = [
    113, 117, 111, 116, 105, 101, 110, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 98, 101, 102, 111, 114, 101, 32, 119, 104, 97, 116, 32, 105, 116, 32, 110, 101, 101, 100, 115,
];

/// con-leche: ConLeche/Kernel/Checker.lean:30-47 checkDefnVal
/// con-leche: ConLeche/Kernel/Checker.lean:49-78 checkThmVal
/// con-leche: ConLeche/Kernel/Checker.lean:80-102 checkOpaqueVal
/// con-leche: ConLeche/Cached/ParsedC.lean:66-83 checkDefnValCI
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:822-838 valueGuards` — the value's
/// syntactic guards the three value checks spell alike (no loose bound
/// variable, no free variable, declared universe parameters, resolving
/// constants), spelled once here.
pub fn value_guards(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(), CheckError> {
    match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, value) {
        Err(e) => Err(e),
        Ok(b) => {
            if !b {
                fail(CheckError::Invalid(code_points(&M_LOOSE_VALUE)))
            } else {
                match has_fvar_fast(pers, st, CORE_WALK_FUEL, value) {
                    Err(e) => Err(e),
                    Ok(f) => {
                        if f {
                            fail(CheckError::Invalid(code_points(&M_FVAR_VALUE)))
                        } else {
                            value_guards_tail(pers, st, fe, cv, value)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:30-47 checkDefnVal
/// con-leche: ConLeche/Kernel/Checker.lean:49-78 checkThmVal
/// con-leche: ConLeche/Kernel/Checker.lean:80-102 checkOpaqueVal
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:822-838 valueGuards` — the two guards
/// past the scope tests: the level-parameter and the resolution guard (else
/// `unresolvedConstsErrorL`'s verdict).
pub fn value_guards_tail(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<(), CheckError> {
    match all_level_params_defined(pers, st, &cv.level_params, value) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                fail(CheckError::Invalid(code_points(&M_UNDECL_VALUE)))
            } else {
                match consts_resolve_f_fast(pers, st, fe, value) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if !r {
                            unresolved_consts_fail(pers, st, fe, value)
                        } else {
                            Ok(())
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:30-47 checkDefnVal
/// con-leche: ConLeche/Cached/ParsedC.lean:66-83 checkDefnValCI
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:840-853 checkDefnVal` — check a `def`
/// declaration's value against its checked constant, returning the record to
/// install, unpushed (the cached twin's shape: the caller certifies the pinned
/// operations against the environment with and without it, then pushes).  The
/// reducibility hint is stored untouched: it steers only the lazy delta
/// unfolding order, never a verdict.
pub fn check_defn_val(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
    hint: &ReducibilityHint,
) -> Result<IConstantInfo, CheckError> {
    match value_guards(pers, st, fe, cv, value) {
        Err(e) => Err(e),
        Ok(()) => match infer_type_core(pers, st, mode, fe, CHECK_FUEL, 0, value) {
            Err(e) => Err(e),
            Ok(vtype) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(IConstantInfo::DefnInfo(
                            crate::arena::env::i_constant_val_dup(cv),
                            value.dup2(),
                            crate::kernel::env::reducibility_hint_dup(hint),
                        ))
                    } else {
                        fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_DEFN)))
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:49-78 checkThmVal
/// con-leche: ConLeche/Cached/ParsedC.lean:85-105 checkThmValCI
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:855-873 checkThmVal` — check a
/// `theorem` declaration's value against its checked constant (whose type must
/// additionally be a proposition), returning the record to install, unpushed.
/// **A theorem is stored by its statement only** (`thmInfo` carries no value):
/// the checked value is a realizability witness, checked and then discarded.
pub fn check_thm_val(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IConstantInfo, CheckError> {
    match infer_type_core(pers, st, mode, fe, CHECK_FUEL, 0, &cv.ty) {
        Err(e) => Err(e),
        Ok(stype) => match ensure_sort_core(pers, st, mode, fe, CHECK_FUEL, 0, &stype) {
            Err(e) => Err(e),
            Ok(u) => match zero_level(st) {
                Err(e) => Err(e),
                Ok(z) => match lvl_eq(pers, st, &u, &z) {
                    Err(e) => Err(e),
                    Ok(o) => match lift_fueled(o) {
                        Err(e) => Err(e),
                        Ok(is_prop) => {
                            if is_prop {
                                check_thm_val_witness(pers, st, mode, fe, cv, value)
                            } else {
                                fail(CheckError::Invalid(code_points(&M_THM_NOT_PROP)))
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:49-78 checkThmVal
/// con-leche: ConLeche/Cached/ParsedC.lean:85-105 checkThmValCI
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:855-873 checkThmVal` — the witness
/// half: the value's guards, its inferred type against the statement, and the
/// record `.thmInfo cv` — the statement only.
pub fn check_thm_val_witness(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IConstantInfo, CheckError> {
    match value_guards(pers, st, fe, cv, value) {
        Err(e) => Err(e),
        Ok(()) => match infer_type_core(pers, st, mode, fe, CHECK_FUEL, 0, value) {
            Err(e) => Err(e),
            Ok(vtype) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(IConstantInfo::ThmInfo(crate::arena::env::i_constant_val_dup(cv)))
                    } else {
                        fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_THM)))
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:80-102 checkOpaqueVal
/// con-leche: ConLeche/Cached/ParsedC.lean:107-123 checkOpaqueValCI
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:875-887 checkOpaqueVal` — check an
/// `opaque` declaration's value against its checked constant: exactly the
/// theorem check without the is-a-proposition requirement, returning the record
/// to install, unpushed.  It is an `axiomInfo` — the checked value is a
/// realizability witness, consumed by the model extension and then discarded.
pub fn check_opaque_val(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    value: &EIdx,
) -> Result<IConstantInfo, CheckError> {
    match value_guards(pers, st, fe, cv, value) {
        Err(e) => Err(e),
        Ok(()) => match infer_type_core(pers, st, mode, fe, CHECK_FUEL, 0, value) {
            Err(e) => Err(e),
            Ok(vtype) => match is_def_eq_core(pers, st, mode, fe, CHECK_FUEL, 0, &vtype, &cv.ty) {
                Err(e) => Err(e),
                Ok(ok) => {
                    if ok {
                        Ok(IConstantInfo::AxiomInfo(crate::arena::env::i_constant_val_dup(cv)))
                    } else {
                        fail(CheckError::Invalid(code_points(&M_TYPE_MISMATCH_OPAQUE)))
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The pinned blocks and the quotient records
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:24-28 installBasisDecl
/// con-leche: ConLeche/Kernel/DeclCheck.lean:386-390 installBasisDeclF
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:891-898 installBasisDecl` — install one
/// pinned basis declaration (duplicate-checked), returning the pushed index.
pub fn install_basis_decl(
    pers: &PersTier,
    fe: IFEnv,
    ci: IConstantInfo,
) -> Result<IFEnv, CheckError> {
    if ifenv_find(pers, &fe, &crate::arena::env::i_constant_info_name(&ci)).is_some() {
        fail(CheckError::Invalid(code_points(&M_DUP_DECL)))
    } else {
        Ok(ifenv_push(fe, ci))
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:463-470 checkBasisBlock
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::install_basis_decls_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:900-905 installBasisDecls` — the cited
/// `(kind.atBlock block).foldlM installBasisDecl env`, as an explicit list
/// recursion (§3.4), threading the index by value.
pub fn install_basis_decls(
    pers: &PersTier,
    fe: IFEnv,
    decls: &Vec<IConstantInfo>,
    i: usize,
) -> Result<IFEnv, CheckError> {
    if i >= decls.len() {
        Ok(fe)
    } else {
        match install_basis_decl(pers, fe, i_constant_info_dup(&decls[i])) {
            Err(e) => Err(e),
            Ok(fe2) => install_basis_decls(pers, fe2, decls, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:463-470 checkBasisBlock
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::check_basis_block_refines, then delete this line
/// con-leche: ConLeche/Cached/ParsedC.lean:137-142 checkBasisBlockC
/// con-leche: CHANGED since 210a580e — re-port, re-test, re-prove decl_check::check_basis_block_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:907-918 checkBasisBlock` — **a pinned
/// block's check and install**: the records compared with the pin, and each pin
/// installed at the names its record declares.  A block with a pinned block's
/// names that is not the pin is invalid input (a basis redefinition).
pub fn check_basis_block(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    kind: &BasisKind,
    block: &Vec<IConstantInfo>,
) -> Result<IFEnv, CheckError> {
    match basis_kind_decls(pers, st, kind) {
        Err(e) => Err(e),
        Ok(pins) => match pin_list_ok(pers, st, block, &pins) {
            Err(e) => Err(e),
            Ok(false) => fail(CheckError::Invalid(code_points(&M_BASIS_NOT_PIN))),
            Ok(true) => match basis_kind_at_block(pers, st, kind, block) {
                Err(e) => Err(e),
                Ok(cs) => install_basis_decls(pers, fe, &cs, 0),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:463-474 checkQuotRecord
/// con-leche: ConLeche/Cached/ParsedC.lean:125-133 checkQuotRecordC
/// Lean twin: `proof/ConRon/Arena/DeclCheck.lean:920-932 checkQuotRecord` — **a quotient
/// record's check and install**: compared with its slot's pin, the slots it
/// needs stored, and installed at its own names.  A record that does not match
/// is a quotient this checker positively does not support.
pub fn check_quot_record(
    pers: &PersTier,
    st: &mut AState,
    fe: IFEnv,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<IFEnv, CheckError> {
    match quot_pin_hit(pers, st, k, cv) {
        Err(e) => Err(e),
        Ok(false) => match k {
            QuotKind::Sound => fail(CheckError::NotImplemented(code_points(&M_QUOT_SOUND_MISMATCH))),
            _ => fail(CheckError::NotImplemented(code_points(&M_QUOT_DECL_MISMATCH))),
        },
        Ok(true) => match quot_preds_ok(pers, st, &fe, k) {
            Err(e) => Err(e),
            Ok(false) => fail(CheckError::NotImplemented(code_points(&M_QUOT_PREDS))),
            Ok(true) => match quot_at(pers, st, k, cv) {
                Err(e) => Err(e),
                Ok(ci) => install_basis_decl(pers, fe, ci),
            },
        },
    }
}
