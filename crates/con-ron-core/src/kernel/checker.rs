//! `ConLeche/Kernel/Checker.lean` — **the declaration checker**.  `checkDecl`
//! checks one declaration against the current environment and, on success,
//! returns the extended one; `checkDeclsPure` folds it over a list of
//! declarations from the empty environment.
//!
//! The `CheckerOps` collapse is `kernel::checker_base`'s module note; the
//! indexed twins of `ConLeche/Kernel/DeclCheck.lean` are the same Rust
//! functions with a second citation (task #18's deviation 3).  Two further
//! deviations are specific to this file and are recorded here, once.
//!
//! ## 1. The pre-insertion environment is a *visibility bound*, not a value
//!
//! `checkDecl`'s `defn` and `opaque` arms hold **two** environments at once:
//! `env`, the pre-insertion one every check runs in, and `env2`, the extended
//! one the guards read (`natOpGuard env2`, `env2.find? c`, `divModEnvGuard
//! env2`).  Lean can, because its environments are persistent.  Task #14's
//! `FEnv` ruling is that the port threads the index linearly instead — and
//! con-leche's index was built for exactly this: an entry carries its
//! installation counter and `FEnv.restrictTo k` lowers the visibility bound
//! in `O(1)` (con-leche task #108).  So the two views are **one index at two
//! bounds**: `k` is read off before the push, and a function that needs the
//! pre-insertion view takes the index *by value*, restricts, checks, and
//! restores the bound before handing it back.  That is DESIGN.md §3.5's
//! "phase B needs exactly one view at a time — it lowers the bound for a
//! record and raises it back", made concrete; the functions it changes the
//! shape of are `check_div_mod_pin` and `check_reduce_pin`, which return the
//! index where the Lean returns `Unit`.
//!
//! ## 2. The decline messages drop their accumulated reasons
//!
//! `checkDivModPinLoop` carries a `List String` of per-variant reasons and
//! `String.intercalate`s them into the final decline; `divModAttemptReason`
//! renders one.  DESIGN.md §3.1 says message strings need not match — the
//! theorem never reads them — so the accumulator and its renderer are not
//! ported and the decline is a fixed message.  The one error the port does
//! report verbatim is a *thrown* attempt's, which task #65 makes the pin
//! check's verdict (`cached::checker_c::or_else_step`, and note 3).
//!
//! ## 3. An attempt's error is the verdict (task #65)
//!
//! `checkDivModPinLoop`'s `ops.orElse` recovers from a *thrown* attempt and
//! tries the next variant.  The port does not: `Ok(false)` moves on,
//! `Err e` fails the whole pin check with `e`.  The ruling, why it is only
//! ever an acceptance lost, and what it buys the refinement proof are in
//! `cached::checker_c`'s module note and DESIGN.md §3.
//!
//! ## What is not here
//!
//! * `checkDecl`'s `.indDecl` arm declines: its two install routes
//!   (`nativeParts?`, `checkNative`, `checkModeled`) are
//!   `ConLeche/Kernel/Inductives/*`, a separate family.  The declared
//!   parameter count is still checked first, as con-leche task #228 insists,
//!   so a block with a wrong `nparams` is *rejected* and everything else
//!   *declines* — sound for the accept direction (DESIGN.md §1).
//! * the pinned basis blocks the `.basisDecl` arm installs are
//!   `kernel::basis_tables`, generated from con-leche's own
//!   `BasisKind.declsA` (task #22), and the two pins compared as whole
//!   `ConstantInfo`s are `kernel::basis_pins` over that table (task #27).
//!   The pin variants `checkDivModPinLoop` walks are the `pins` **parameter**
//!   threaded down from `cached::installed::check_decls` (DESIGN.md §3.6,
//!   task #31), where the cited code reads the global `natOpPinSets`; an
//!   empty list is the loop's `[]` arm, i.e. a decline.

use crate::cached::checker_c;
use crate::cached::checker_c::OrElseStep;
use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::basis_pins;
use crate::kernel::basis_tables;
use crate::kernel::checker_base;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{
    BasisKind, CheckMode, ConstantInfo, ConstantVal, Declaration, ReducibilityHint,
};
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::kernel::std_axioms;
use crate::kernel::trust_axioms;
use crate::kernel::type_checker;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The value declarations (`Checker.lean:26-107`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:26-30 installBasisDecl
/// con-leche: ConLeche/Kernel/DeclCheck.lean:855-859 installBasisDeclF
/// Install one pinned basis declaration (duplicate-checked), returning the
/// pushed index.
pub fn install_basis_decl(fe: FEnv, ci: ConstantInfo) -> CheckM<FEnv> {
    if fenv::find(&fe, &env::constant_info_name(&ci)).is_some() {
        Err(core_types::invalid({ const M: [u32; 21] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else {
        Ok(fenv::push(fe, ci))
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:838-853 checkDefnValF
/// Check a `def` declaration's value against its checked constant, returning
/// the pushed index.  The reducibility hint is stored untouched: it steers
/// only the lazy delta unfolding order in `isDefEq`, never a verdict.
pub fn check_defn_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
    hint: &ReducibilityHint,
) -> CheckM<FEnv> {
    if !expr_ops::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(value_a) => check_defn_val_after_annot(mode, st, fe, cv, value_a, hint),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:32-50 checkDefnVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:838-853 checkDefnValF
/// The tail past the annotation: the level-parameter and resolution guards,
/// the value's inferred type against the declared one, and the push.
pub fn check_defn_val_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value_a: Expr,
    hint: &ReducibilityHint,
) -> CheckM<FEnv> {
    if !expr_ops::all_level_params_defined_fast(&cv.level_params, &value_a) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !core_k::consts_resolve(&fe, &value_a) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::infer_type_core(mode, st, &fe, 0, &value_a) {
            Err(err) => Err(err),
            Ok(vtype) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &vtype, &cv.ty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::DefnInfo(
                                env::constant_val_dup(cv),
                                value_a,
                                env::reducibility_hint_dup(hint),
                            ),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 27] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal
/// Check a `theorem` declaration's value against its checked constant, whose
/// type must additionally be a proposition.  **A theorem is stored by its
/// statement**: the constant keeps the record's own (raw) value as an unread
/// datum — a theorem is opaque to reduction — and the annotated value is a
/// *realizability witness*, checked against the statement and then
/// discarded.
pub fn check_thm_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<FEnv> {
    match type_checker::infer_type_core(mode, st, &fe, 0, &cv.ty) {
        Err(err) => Err(err),
        Ok(stype) => match type_checker::ensure_sort_core(mode, st, &fe, 0, &stype) {
            Err(err) => Err(err),
            Ok(u) => match core_k::lift_fueled(level::is_equiv(&u, &level::zero())) {
                Err(err) => Err(err),
                Ok(is_prop) => {
                    if is_prop {
                        check_thm_val_witness(mode, st, fe, cv, value)
                    } else {
                        Err(core_types::invalid({ const M: [u32; 36] = [116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal
/// The witness half of `checkThmVal`: the value's syntactic guards and
/// annotation.  Split off so the is-a-proposition gate is a tail call.
pub fn check_thm_val_witness(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<FEnv> {
    if !expr_ops::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(jv) => check_thm_val_checked(mode, st, fe, cv, value, jv),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:52-82 checkThmVal
/// The tail past the witness annotation: the guards on `jv`, its inferred
/// type against the statement, and the push of `.thmInfo cv value` — the
/// **raw** value, as the cited clause stores it.
pub fn check_thm_val_checked(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
    jv: Expr,
) -> CheckM<FEnv> {
    if !expr_ops::all_level_params_defined_fast(&cv.level_params, &jv) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !core_k::consts_resolve(&fe, &jv) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::infer_type_core(mode, st, &fe, 0, &jv) {
            Err(err) => Err(err),
            Ok(vtype) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &vtype, &cv.ty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::ThmInfo(
                                env::constant_val_dup(cv),
                                expr::dup(value),
                            ),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 24] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 116, 104, 101, 111, 114, 101, 109]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal
/// Check an `opaque` declaration's value against its checked constant:
/// exactly the theorem check without the is-a-proposition requirement.  The
/// result is stored as an `axiomInfo` — the checked value is a realizability
/// witness, consumed by the model extension and then discarded, because the
/// official kernel's `is_delta` never unfolds an opaque.
pub fn check_opaque_val(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<FEnv> {
    if !expr_ops::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, &fe, 0, value) {
            Err(err) => Err(err),
            Ok(value_a) => check_opaque_val_after_annot(mode, st, fe, cv, value_a),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:84-107 checkOpaqueVal
/// The tail past the annotation: the guards, the inferred type against the
/// declared one, and the push of `.axiomInfo cv`.
pub fn check_opaque_val_after_annot(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value_a: Expr,
) -> CheckM<FEnv> {
    if !expr_ops::all_level_params_defined_fast(&cv.level_params, &value_a) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !core_k::consts_resolve(&fe, &value_a) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::infer_type_core(mode, st, &fe, 0, &value_a) {
            Err(err) => Err(err),
            Ok(vtype) => match type_checker::is_def_eq_core(mode, st, &fe, 0, &vtype, &cv.ty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::push(
                            fe,
                            ConstantInfo::AxiomInfo(env::constant_val_dup(cv)),
                        ))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 23] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 111, 112, 97, 113, 117, 101]; core_types::code_points(&M) }))
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// The structural-`Nat` certification (`Checker.lean:108-116`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:108-116 certifyNatEqs
/// Certify a list of recurrence equations by definitional equality (at depth
/// 2: the equations' variables are `fvar 0`/`fvar 1`).
pub fn certify_nat_eqs(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    eqs: &Vec<(Expr, Expr)>,
) -> CheckM<bool> {
    certify_nat_eqs_from(mode, st, fe, eqs, 0)
}

/// con-leche: ConLeche/Kernel/Checker.lean:108-116 certifyNatEqs
/// The cited `List` recursion as an index recursion (task #3's pattern).
pub fn certify_nat_eqs_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    eqs: &Vec<(Expr, Expr)>,
    i: usize,
) -> CheckM<bool> {
    if i >= eqs.len() {
        Ok(true)
    } else {
        match type_checker::is_def_eq_core(mode, st, fe, 2, &eqs[i].0, &eqs[i].1) {
            Err(err) => Err(err),
            Ok(ok) => {
                if ok {
                    certify_nat_eqs_from(mode, st, fe, eqs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The pin-certified WF-recursive `Nat` operations (`Checker.lean:118-380`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:118-130 divModDeclPin
/// The pinned defining expression of a pin-certified WF-recursive op in one
/// **pin variant**.
pub fn div_mod_decl_pin(ps: &NatOpPinSet, c: &Name) -> Expr {
    if name::beq(c, &core_k::nat_div_name()) {
        expr::dup(&ps.div_pin)
    } else if name::beq(c, &core_k::nat_gcd_name()) {
        expr::dup(&ps.gcd_pin)
    } else if name::beq(c, &core_k::nat_land_name()) {
        expr::dup(&ps.land_pin)
    } else if name::beq(c, &core_k::nat_lor_name()) {
        expr::dup(&ps.lor_pin)
    } else if name::beq(c, &core_k::nat_xor_name()) {
        expr::dup(&ps.xor_pin)
    } else if name::beq(c, &core_k::nat_shift_left_name()) {
        expr::dup(&ps.shift_left_pin)
    } else if name::beq(c, &core_k::nat_shift_right_name()) {
        expr::dup(&ps.shift_right_pin)
    } else {
        expr::dup(&ps.mod_pin)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:132-142 divModCertProofs
/// The certificate proof terms of a pin-certified WF-recursive op in one pin
/// variant, one per statement of `divModCertStmts`.
pub fn div_mod_cert_proofs(ps: &NatOpPinSet, c: &Name) -> Vec<Expr> {
    if name::beq(c, &core_k::nat_div_name()) {
        env::exprs_copy(&ps.div_proofs)
    } else if name::beq(c, &core_k::nat_gcd_name()) {
        env::exprs_copy(&ps.gcd_proofs)
    } else if name::beq(c, &core_k::nat_land_name()) {
        env::exprs_copy(&ps.land_proofs)
    } else if name::beq(c, &core_k::nat_lor_name()) {
        env::exprs_copy(&ps.lor_proofs)
    } else if name::beq(c, &core_k::nat_xor_name()) {
        env::exprs_copy(&ps.xor_proofs)
    } else if name::beq(c, &core_k::nat_shift_left_name()) {
        env::exprs_copy(&ps.shift_left_proofs)
    } else if name::beq(c, &core_k::nat_shift_right_name()) {
        env::exprs_copy(&ps.shift_right_proofs)
    } else {
        env::exprs_copy(&ps.mod_proofs)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// `divModCertStmts`' local `natTy` — `Nat` as the pinned constant.  The
/// cited block opens with thirteen `let`-bound builders and constants;
/// DESIGN.md §3.4 forbids closures, so each is a named function (task #18's
/// point 5, `natOpEquations`' four local lambdas).
pub fn cert_nat_ty() -> Expr {
    expr::mk_const(basis_names::nat_name(), Vec::new())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `x : Expr := .fvar 0 natTy`.
pub fn cert_x() -> Expr {
    expr::fvar(0, cert_nat_ty())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `y : Expr := .fvar 1 natTy`.
pub fn cert_y() -> Expr {
    expr::fvar(1, cert_nat_ty())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `one`, spelled `Nat.succ Nat.zero` (the statements never use a
/// literal: the model side consumes them through the existing `NatOpsOk`
/// literal semantics).
pub fn cert_one() -> Expr {
    core_k::nat_eq_s(expr::mk_const(basis_names::nat_zero_name(), Vec::new()))
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `two := Nat.succ one`.
pub fn cert_two() -> Expr {
    core_k::nat_eq_s(cert_one())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `z := Nat.zero`.
pub fn cert_zero() -> Expr {
    expr::mk_const(basis_names::nat_zero_name(), Vec::new())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `bT := Bool.true`.
pub fn cert_b_true() -> Expr {
    expr::mk_const(core_k::bool_true_name(), Vec::new())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `bF := Bool.false`.
pub fn cert_b_false() -> Expr {
    expr::mk_const(core_k::bool_false_name(), Vec::new())
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `ble2 a b := Nat.ble a b` — the guards are spelled with the
/// already-certified `Nat.ble`, never the `Nat.le`/`Nat.lt` `Prop`
/// inductives.
pub fn cert_ble2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_ble_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `eqB a b := Eq.{1} Bool a b`.
pub fn cert_eq_b(a: Expr, b: Expr) -> Expr {
    expr::app(
        expr::app(
            expr::app(
                expr::mk_const(basis_names::eq_name(), std_axioms::one_level()),
                expr::mk_const(core_k::bool_name(), Vec::new()),
            ),
            a,
        ),
        b,
    )
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `eqN a b := Eq.{1} Nat a b`.
pub fn cert_eq_n(a: Expr, b: Expr) -> Expr {
    expr::app(
        expr::app(
            expr::app(
                expr::mk_const(basis_names::eq_name(), std_axioms::one_level()),
                cert_nat_ty(),
            ),
            a,
        ),
        b,
    )
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `op2 a b := c a b` — the op's self-reference is `.const c []`,
/// substituted with the stored annotated value before checking.
pub fn cert_op2(c: &Name, a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(c, a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The pinned characterization statements of a pin-certified WF-recursive op,
/// in *open* form over `x := fvar 0`, `y := fvar 1` (the hypotheses become
/// `fvar 2, fvar 3`): per certificate, the list of hypothesis types and the
/// characteristic equation `Eq Nat lhs rhs`.
pub fn div_mod_cert_stmts(c: &Name) -> Vec<(Vec<Expr>, Expr)> {
    let mut out: Vec<(Vec<Expr>, Expr)> = Vec::new();
    if name::beq(c, &core_k::nat_gcd_name()) {
        // `gcd`: `1 ≤ x → gcd x y = gcd (y % x) x`, `x = 0 → gcd x y = y`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_op2(c, cert_mod2(cert_y(), cert_x()), cert_x()),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_y()),
        ));
    } else if name::beq(c, &core_k::nat_shift_left_name()) {
        // `1 ≤ y → x <<< y = (2*x) <<< (y-1)`, `y = 0 → x <<< y = x`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_op2(
                    c,
                    cert_mul2(cert_two(), cert_x()),
                    cert_sub2(cert_y(), cert_one()),
                ),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_x()),
        ));
    } else if name::beq(c, &core_k::nat_shift_right_name()) {
        // `1 ≤ y → x >>> y = (x >>> (y-1)) / 2`, `y = 0 → x >>> y = x`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_div2(
                    cert_op2(c, cert_x(), cert_sub2(cert_y(), cert_one())),
                    cert_two(),
                ),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_x()),
        ));
    } else if name::beq(c, &core_k::nat_land_name()) {
        // `1 ≤ x → x &&& y = 2*((x/2) &&& (y/2)) + (x%2)*(y%2)`,
        // `x = 0 → x &&& y = 0`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_add2(
                    cert_mul2(cert_two(), cert_halves(c)),
                    cert_mul2(
                        cert_mod2(cert_x(), cert_two()),
                        cert_mod2(cert_y(), cert_two()),
                    ),
                ),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_zero()),
        ));
    } else if name::beq(c, &core_k::nat_lor_name()) {
        // `1 ≤ x → x ||| y = 2*((x/2) ||| (y/2)) + (x%2 + y%2 - (x%2)*(y%2))`,
        // `x = 0 → x ||| y = y`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_add2(
                    cert_mul2(cert_two(), cert_halves(c)),
                    cert_sub2(
                        cert_add2(
                            cert_mod2(cert_x(), cert_two()),
                            cert_mod2(cert_y(), cert_two()),
                        ),
                        cert_mul2(
                            cert_mod2(cert_x(), cert_two()),
                            cert_mod2(cert_y(), cert_two()),
                        ),
                    ),
                ),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_y()),
        ));
    } else if name::beq(c, &core_k::nat_xor_name()) {
        // `1 ≤ x → x ^^^ y = 2*((x/2) ^^^ (y/2)) + (x%2 + y%2) % 2`,
        // `x = 0 → x ^^^ y = y`
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_true())),
            cert_eq_n(
                cert_op2(c, cert_x(), cert_y()),
                cert_add2(
                    cert_mul2(cert_two(), cert_halves(c)),
                    cert_mod2(
                        cert_add2(
                            cert_mod2(cert_x(), cert_two()),
                            cert_mod2(cert_y(), cert_two()),
                        ),
                        cert_two(),
                    ),
                ),
            ),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_x()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_y()),
        ));
    } else {
        // `Nat.div` / `Nat.mod`: the cited `else` branch's three
        // certificates, with `recRhs`/`baseRhs` as the Lean's two locals.
        out.push((
            cert_hyp2(
                cert_eq_b(cert_ble2(cert_y(), cert_x()), cert_b_true()),
                cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_true()),
            ),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_rec_rhs(c)),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_y(), cert_x()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_base_rhs(c)),
        ));
        out.push((
            cert_hyp1(cert_eq_b(cert_ble2(cert_one(), cert_y()), cert_b_false())),
            cert_eq_n(cert_op2(c, cert_x(), cert_y()), cert_base_rhs(c)),
        ));
    }
    out
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `sub2 a b := Nat.sub a b`.
pub fn cert_sub2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_sub_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `mod2 a b := Nat.mod a b`.
pub fn cert_mod2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_mod_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `div2 a b := Nat.div a b`.
pub fn cert_div2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_div_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `add2 a b := Nat.add a b`.
pub fn cert_add2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_add_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `mul2 a b := Nat.mul a b`.
pub fn cert_mul2(a: Expr, b: Expr) -> Expr {
    core_k::nat_eq_ap2(&core_k::nat_mul_name(), a, b)
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// `op2 (div2 x two) (div2 y two)` — the bitwise certificates' recursive
/// call on the halves, written three times in the cited block.
pub fn cert_halves(c: &Name) -> Expr {
    cert_op2(
        c,
        cert_div2(cert_x(), cert_two()),
        cert_div2(cert_y(), cert_two()),
    )
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `recRhs`: `Nat.succ (c (x - y) y)` for `Nat.div`, `c (x - y) y`
/// for `Nat.mod`.
pub fn cert_rec_rhs(c: &Name) -> Expr {
    let step: Expr = cert_op2(c, cert_sub2(cert_x(), cert_y()), cert_y());
    if name::beq(c, &core_k::nat_div_name()) {
        core_k::nat_eq_s(step)
    } else {
        step
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:144-222 divModCertStmts
/// The local `baseRhs`: `Nat.zero` for `Nat.div`, `x` for `Nat.mod`.
pub fn cert_base_rhs(c: &Name) -> Expr {
    if name::beq(c, &core_k::nat_div_name()) {
        cert_zero()
    } else {
        cert_x()
    }
}

/// con-leche: none — the one-element hypothesis list `[h]` of `divModCertStmts`
/// A `Vec` literal needs a push (task #18's point 10).
pub fn cert_hyp1(h: Expr) -> Vec<Expr> {
    let mut hs: Vec<Expr> = Vec::new();
    hs.push(h);
    hs
}

/// con-leche: none — the two-element hypothesis list `[h1, h2]` of `divModCertStmts`
/// As `cert_hyp1`.
pub fn cert_hyp2(h1: Expr, h2: Expr) -> Vec<Expr> {
    let mut hs: Vec<Expr> = Vec::new();
    hs.push(h1);
    hs.push(h2);
    hs
}

/// con-leche: ConLeche/Kernel/Checker.lean:224-237 divModCertApplied
/// The vendored proof applied to the statement's free variables (`x`, `y`,
/// then one `fvar` per hypothesis, carrying the hypothesis *type* as its
/// `fvar` annotation — the checker's implicit local context).
pub fn div_mod_cert_applied(proof_s: &Expr, hyps: &Vec<Expr>) -> Expr {
    let base: Expr = expr::app(
        expr::app(expr::dup(proof_s), cert_x()),
        cert_y(),
    );
    if hyps.len() == 1 {
        expr::app(base, expr::fvar(2, expr::dup(&hyps[0])))
    } else if hyps.len() == 2 {
        expr::app(
            expr::app(base, expr::fvar(2, expr::dup(&hyps[0]))),
            expr::fvar(3, expr::dup(&hyps[1])),
        )
    } else {
        base
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:321-330 divModCertGuardF
/// The syntactic guards of one certificate check: the substituted proof is
/// closed, level-monomorphic and resolving, and the substituted statement
/// components resolve.  Deviation: the Lean recomputes
/// `Expr.substConstAll c annVal proof` four times; the port substitutes once
/// and reads the result (a `@[simp]`-transparent common subexpression).
pub fn div_mod_cert_guard(
    fe: &FEnv,
    c: &Name,
    ann_val: &Expr,
    hyps: &Vec<Expr>,
    eq_e: &Expr,
    proof: &Expr,
) -> bool {
    let p: Expr = core_k::subst_const_all(c, ann_val, proof);
    if !expr_ops::loose_bvars_bounded(0, &p) {
        false
    } else if expr_ops::has_fvar(&p) {
        false
    } else if !expr_ops::all_level_params_defined_fast(&Vec::new(), &p) {
        false
    } else if !core_k::consts_resolve(fe, &p) {
        false
    } else if !hyps_resolve(fe, c, ann_val, hyps, 0) {
        false
    } else {
        core_k::consts_resolve(fe, &core_k::subst_const0(c, ann_val, eq_e))
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:239-250 divModCertGuard
/// The `(hyps.map (Expr.substConst0 c annVal)).all (·.constsResolve env)` of
/// the cited guard, as an index recursion with the substitution fused in.
pub fn hyps_resolve(
    fe: &FEnv,
    c: &Name,
    ann_val: &Expr,
    hyps: &Vec<Expr>,
    i: usize,
) -> bool {
    if i >= hyps.len() {
        true
    } else if core_k::consts_resolve(fe, &core_k::subst_const0(c, ann_val, &hyps[i])) {
        hyps_resolve(fe, c, ann_val, hyps, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `hyps.map (Expr.substConst0 c annVal)` of `checkDivModCerts`
/// `List.map` over a `Vec<Expr>`; DESIGN.md §3.4 forbids the closure.
pub fn hyps_subst(c: &Name, ann_val: &Expr, hyps: &Vec<Expr>) -> Vec<Expr> {
    hyps_subst_from(c, ann_val, hyps, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `hyps_subst`
/// The accumulator is passed by value and returned.
pub fn hyps_subst_from(
    c: &Name,
    ann_val: &Expr,
    hyps: &Vec<Expr>,
    i: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if i >= hyps.len() {
        out
    } else {
        let mut out = out;
        out.push(core_k::subst_const0(c, ann_val, &hyps[i]));
        hyps_subst_from(c, ann_val, hyps, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
/// con-leche: ConLeche/Kernel/DeclCheck.lean:861-875 checkDivModCertsF
/// Check the pinned certificates of op `c`: per certificate, the vendored
/// proof (with the op's self-references replaced by the stored annotated
/// value — the checks run in the *pre-insertion* environment, exactly like
/// the structural-`Nat` certification) is applied to free variables typed by
/// the pinned open statement, its type inferred, and compared against the
/// pinned characteristic equation.  Nothing is installed.
pub fn check_div_mod_certs(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    ann_val: &Expr,
    stmts: &Vec<(Vec<Expr>, Expr)>,
    proofs: &Vec<Expr>,
) -> CheckM<bool> {
    check_div_mod_certs_from(mode, st, fe, c, ann_val, stmts, proofs, 0)
}

/// con-leche: ConLeche/Kernel/Checker.lean:252-275 checkDivModCerts
/// The cited two-list recursion as one index recursion: both exhausted, both
/// in range, or the length-mismatch `false`.
pub fn check_div_mod_certs_from(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    ann_val: &Expr,
    stmts: &Vec<(Vec<Expr>, Expr)>,
    proofs: &Vec<Expr>,
    i: usize,
) -> CheckM<bool> {
    if i >= stmts.len() && i >= proofs.len() {
        Ok(true)
    } else if i >= stmts.len() || i >= proofs.len() {
        Ok(false)
    } else if !div_mod_cert_guard(fe, c, ann_val, &stmts[i].0, &stmts[i].1, &proofs[i]) {
        Ok(false)
    } else {
        let applied: Expr = div_mod_cert_applied(
            &core_k::subst_const_all(c, ann_val, &proofs[i]),
            &hyps_subst(c, ann_val, &stmts[i].0),
        );
        match type_checker::annotate_core(mode, st, fe, 4, &applied) {
            Err(err) => Err(err),
            Ok(applied_a) => match type_checker::infer_type_core(mode, st, fe, 4, &applied_a) {
                Err(err) => Err(err),
                Ok(tp) => {
                    let target: Expr = core_k::subst_const0(c, ann_val, &stmts[i].1);
                    match type_checker::is_def_eq_core(mode, st, fe, 4, &tp, &target) {
                        Err(err) => Err(err),
                        Ok(ok) => {
                            if ok {
                                check_div_mod_certs_from(
                                    mode, st, fe, c, ann_val, stmts, proofs, i + 1,
                                )
                            } else {
                                Ok(false)
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF
/// The cited `(natOpDeps c).all (natOpStoredOkF fe2)`, as an index recursion
/// (task #14's per-element rule; DESIGN.md §3.4 forbids the closure).
///
/// **Not `core_k::deps_all_stored`** (task #58): that is `natOpGuard`'s own
/// `.all`, whose per-dependency test is only `defnLpEmptyF` — level
/// parameters empty.  `divModEnvGuard`/`checkDecl` demand `natOpStoredOk`,
/// which additionally pins the dependency's *type*, and using the weaker one
/// here let the port take the `Nat.div`/`Nat.mod` pin route where con-leche
/// declines (§1's accept direction).
pub fn deps_all_stored_ok(fe2: &FEnv, deps: &Vec<Name>, i: usize) -> bool {
    if i >= deps.len() {
        true
    } else if core_k::nat_op_stored_ok(fe2, &deps[i]) {
        deps_all_stored_ok(fe2, deps, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF
/// Environment prerequisites of a certified `Nat.div`/`Nat.mod`: dependency
/// guard, pinned dependencies, the pinned `Eq` basis (the certificate
/// statements are equations in the pinned equality), and the `Bool`
/// constructors stored at the type `Bool` itself.
pub fn div_mod_env_guard(fe2: &FEnv, c: &Name) -> bool {
    if !core_k::nat_op_guard(fe2, c) {
        false
    } else if !deps_all_stored_ok(fe2, &core_k::nat_op_deps(c), 0) {
        false
    } else if !basis_pins::eq_basis_pinned(fe2) {
        false
    } else if !bool_ctor_typed(fe2, &core_k::bool_true_name()) {
        false
    } else {
        bool_ctor_typed(fe2, &core_k::bool_false_name())
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:277-290 divModEnvGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:310-319 divModEnvGuardF
/// The cited `match env2.find? boolTrueName with | some ci => ci.toConstantVal.type
/// == .const boolName []` — the guards' `true`/`false` must inhabit the
/// `Bool` value semantically.  Factored out because the Lean spells it twice
/// (task #14's borrow rule: the lookup's borrow ends at the call).
pub fn bool_ctor_typed(fe2: &FEnv, n: &Name) -> bool {
    match fenv::find(fe2, n) {
        Some(ci) => expr::beq(
            &env::constant_info_type(ci),
            &expr::mk_const(core_k::bool_name(), Vec::new()),
        ),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:292-297 divModPinGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:332-336 divModPinGuardF
/// Syntactic guards on one variant's pin (generated; checked once at install
/// rather than proven about the blob).
pub fn div_mod_pin_guard(ps: &NatOpPinSet, fe: &FEnv, c: &Name) -> bool {
    let pin: Expr = div_mod_decl_pin(ps, c);
    if !expr_ops::loose_bvars_bounded(0, &pin) {
        false
    } else if expr_ops::has_fvar(&pin) {
        false
    } else if !expr_ops::all_level_params_defined_fast(&Vec::new(), &pin) {
        false
    } else {
        core_k::consts_resolve(fe, &pin)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
/// con-leche: ConLeche/Kernel/DeclCheck.lean:338-342 divModCertsGuardF
/// All of one variant's certificates' syntactic guards at once.  Checked
/// *before* the pin comparison; a failure moves on to the next variant, since
/// a stream may legitimately stop short of the constants a variant's proofs
/// mention.
pub fn div_mod_certs_guard(ps: &NatOpPinSet, fe: &FEnv, c: &Name, ann_val: &Expr) -> bool {
    div_mod_certs_guard_from(
        &div_mod_cert_stmts(c),
        &div_mod_cert_proofs(ps, c),
        fe,
        c,
        ann_val,
        0,
    )
}

/// con-leche: ConLeche/Kernel/Checker.lean:299-306 divModCertsGuard
/// The cited `(stmts.zip proofs).all` as an index recursion: a `zip` stops at
/// the shorter list, so the bound is the minimum.
pub fn div_mod_certs_guard_from(
    stmts: &Vec<(Vec<Expr>, Expr)>,
    proofs: &Vec<Expr>,
    fe: &FEnv,
    c: &Name,
    ann_val: &Expr,
    i: usize,
) -> bool {
    if i >= stmts.len() || i >= proofs.len() {
        true
    } else if div_mod_cert_guard(fe, c, ann_val, &stmts[i].0, &stmts[i].1, &proofs[i]) {
        div_mod_certs_guard_from(stmts, proofs, fe, c, ann_val, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:308-328 checkDivModPinAt
/// con-leche: ConLeche/Kernel/DeclCheck.lean:877-885 checkDivModPinAtF
/// **One pin variant's attempt**: the stored value against the variant's pin
/// by definitional equality, and on a match the variant's certificates.
/// `true` = matched, the fast path is justified; `false` = the pin is not
/// definitionally equal, or a certificate did not check.  The third outcome
/// is an error thrown from inside — a certificate blob generated by another
/// toolchain can be ill-typed against this stream — which the cited code
/// reads as "this variant does not match" and the port (task #65) makes the
/// whole pin check's verdict (`cached::checker_c::or_else_step`).
pub fn check_div_mod_pin_at(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    value2: &Expr,
    ps: &NatOpPinSet,
) -> CheckM<bool> {
    match type_checker::annotate_core(mode, st, fe, 0, &div_mod_decl_pin(ps, c)) {
        Err(err) => Err(err),
        Ok(pin_a) => match type_checker::is_def_eq_core(mode, st, fe, 0, value2, &pin_a) {
            Err(err) => Err(err),
            Ok(ok_pin) => {
                if ok_pin {
                    check_div_mod_certs(
                        mode,
                        st,
                        fe,
                        c,
                        value2,
                        &div_mod_cert_stmts(c),
                        &div_mod_cert_proofs(ps, c),
                    )
                } else {
                    Ok(false)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:338-360 checkDivModPinLoop
/// con-leche: ConLeche/Kernel/DeclCheck.lean:887-901 checkDivModPinLoopF
/// **The variant loop**: the first variant whose guards pass and whose
/// attempt succeeds enables the fast path; every other outcome moves on to
/// the next variant, and when none is left the stream DECLINES.  The cited
/// `List NatOpPinSet` recursion is an index recursion over the pin list
/// `check_decls` was given (task #31; the cited code reads the global
/// `natOpPinSets`), and the `tried : List String` accumulator is dropped
/// (module note 2).
///
/// **This is the port's one variant-fallback point**: the `ops.orElse` call is
/// `cached::checker_c::or_else_step`, and the cited continuation — a closure
/// DESIGN.md §3.4 forbids — is spelled here as the loop's own tail call, in
/// the pattern task #18 used for `whnfStep`'s continuation.
///
/// **Deviation (task #65, `cached::checker_c`'s module note): an attempt's
/// error is the verdict.**  Only `Ok(false)` moves on to the next variant;
/// `Err e` fails the whole pin check with `e` — the decline names what the
/// variant failed on — where the cited code recovers and tries the rest.  An
/// accept-direction deviation that can only lose acceptances (DESIGN.md §3).
pub fn check_div_mod_pin_loop(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    value2: &Expr,
    variants: &Vec<NatOpPinSet>,
    i: usize,
) -> CheckM<()> {
    if i >= variants.len() {
        Err(core_types::not_implemented({ const M: [u32; 56] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105, 118, 47, 109, 111, 100, 32, 115, 112, 101, 108, 108, 105, 110, 103, 58, 32, 110, 111, 32, 112, 105, 110, 32, 118, 97, 114, 105, 97, 110, 116, 32, 109, 97, 116, 99, 104, 101, 100]; core_types::code_points(&M) }))
    } else if div_mod_pin_guard(&variants[i], fe, c)
        && div_mod_certs_guard(&variants[i], fe, c, value2)
    {
        let attempt: CheckM<bool> =
            check_div_mod_pin_at(mode, st, fe, c, value2, &variants[i]);
        match checker_c::or_else_step(attempt) {
            OrElseStep::Matched => Ok(()),
            OrElseStep::Continue => {
                check_div_mod_pin_loop(mode, st, fe, c, value2, variants, i + 1)
            }
            OrElseStep::Failed(e) => Err(e),
        }
    } else {
        check_div_mod_pin_loop(mode, st, fe, c, value2, variants, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:362-380 checkDivModPin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:903-912 checkDivModPinF
/// The pin-certified operations' install gate, run after the ordinary
/// definition check: the dependency and pinned-`Eq` guards at the *extended*
/// environment, then the pin variants in `natOpPinSets` order at the
/// *pre-insertion* one.  No variant matching is a decline, never a silent
/// accept.
///
/// Deviation (module note 1): the two environments are one index at two
/// visibility bounds, so this takes the index by value at the extended bound
/// and hands it back there, where the Lean returns `Unit`.
/// **Deviation (DESIGN.md §3.6, task #31): `pins` is a parameter.**  con-leche
/// bakes `natOpPinSets` (`ConLeche/Kernel/NatOpPins.lean:61`) into
/// `checkDivModPin` as a global constant; the port threads the list from
/// `check_decls` instead, because the ~26 500-node table cannot be generated
/// as Rust (Charon OOMs on it, task #22) and it is a *hint* list — every pin
/// is re-checked by `isDefEq` against the stream's own stored value and every
/// certificate against the hand-pinned `div_mod_cert_stmts`, so a wrong list
/// costs a decline and never an accept.  The upstream change this asks for is
/// `checkDecls mode pins ds`.
pub fn check_div_mod_pin(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe: FEnv,
    k_pre: u64,
    c: &Name,
) -> CheckM<FEnv> {
    if !div_mod_env_guard(&fe, c) {
        Err(core_types::not_implemented({ const M: [u32; 35] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 78, 97, 116, 46, 100, 105, 118, 47, 109, 111, 100, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116]; core_types::code_points(&M) }))
    } else {
        match core_k::defn_probe(&fe, c) {
            None => Err(core_types::internal({ const M: [u32; 32] = [78, 97, 116, 46, 100, 105, 118, 47, 109, 111, 100, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; core_types::code_points(&M) })),
            Some((_, value2, _)) => {
                let k2: u64 = fe.visible_below;
                let fe_pre: FEnv = fenv::restrict_to(fe, k_pre);
                let r: CheckM<()> = check_div_mod_pin_loop(
                    mode,
                    st,
                    &fe_pre,
                    c,
                    &value2,
                    pins,
                    0,
                );
                match r {
                    Err(err) => Err(err),
                    Ok(()) => Ok(fenv::restrict_to(fe_pre, k2)),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:382-417 checkReducePin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:914-933 checkReducePinF
/// The `Lean.reduceNat`/`Lean.reduceBool` install gate, run after the
/// ordinary opaque check: the stored constant must carry the pinned type; the
/// witness value must be definitionally equal to the build-time pin of the
/// toolchain's own defining expression (toolchain drift surfaces as a
/// decline, never silently); and the *identity certificate* `value x ≡ x`
/// over an opened `fvar` at the element type must hold — that is what the
/// model consumes, and a failure after the pin matched is an internal
/// inconsistency, because the pin *is* the identity function.
///
/// Deviation (module note 1): as `check_div_mod_pin`, the index comes in at
/// the extended bound and goes back out there.
pub fn check_reduce_pin(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    k_pre: u64,
    c: &Name,
    value: &Expr,
) -> CheckM<FEnv> {
    if !trust_axioms::reduce_stored_ok(&fe, c) {
        Err(core_types::not_implemented({ const M: [u32; 45] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else {
        let k2: u64 = fe.visible_below;
        let fe_pre: FEnv = fenv::restrict_to(fe, k_pre);
        let r: CheckM<()> = check_reduce_pin_pre(mode, st, &fe_pre, c, value);
        match r {
            Err(err) => Err(err),
            Ok(()) => Ok(fenv::restrict_to(fe_pre, k2)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:382-417 checkReducePin
/// con-leche: ConLeche/Kernel/DeclCheck.lean:914-933 checkReducePinF
/// `checkReducePin`'s body at the pre-insertion view: the element guard, the
/// pin's own syntactic guards, the definitional comparison of the witness
/// against the pin, and the identity certificate.
pub fn check_reduce_pin_pre(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    value: &Expr,
) -> CheckM<()> {
    if !trust_axioms::reduce_elem_ok(fe, c) {
        Err(core_types::not_implemented({ const M: [u32; 45] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if !trust_axioms::reduce_pin_guard(fe, c) {
        Err(core_types::not_implemented({ const M: [u32; 71] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112, 101, 108, 108, 105, 110, 103, 58, 32, 112, 105, 110, 32, 103, 114, 111, 117, 110, 100, 32, 99, 111, 110, 115, 116, 97, 110, 116, 115, 32, 97, 98, 115, 101, 110, 116]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, value) {
            Err(err) => Err(err),
            Ok(val_a) => {
                match type_checker::annotate_core(
                    mode,
                    st,
                    fe,
                    0,
                    &trust_axioms::reduce_decl_pin(c),
                ) {
                    Err(err) => Err(err),
                    Ok(pin_a) => {
                        match type_checker::is_def_eq_core(mode, st, fe, 0, &val_a, &pin_a) {
                            Err(err) => Err(err),
                            Ok(ok_pin) => {
                                if ok_pin {
                                    check_reduce_identity(mode, st, fe, c, &val_a)
                                } else {
                                    Err(core_types::not_implemented({ const M: [u32; 42] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 115, 112, 101, 108, 108, 105, 110, 103]; core_types::code_points(&M) }))
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:382-417 checkReducePin
/// The identity certificate: `valA x ≡ x` at depth 1 over `reduceCertVar`.
pub fn check_reduce_identity(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    c: &Name,
    val_a: &Expr,
) -> CheckM<()> {
    let x: Expr = trust_axioms::reduce_cert_var(c);
    let applied: Expr = expr::app(expr::dup(val_a), expr::dup(&x));
    match type_checker::is_def_eq_core(mode, st, fe, 1, &applied, &x) {
        Err(err) => Err(err),
        Ok(ok) => {
            if ok {
                Ok(())
            } else {
                Err(core_types::internal({ const M: [u32; 48] = [112, 105, 110, 110, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 111, 112, 97, 113, 117, 101, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 105, 100, 101, 110, 116, 105, 116, 121]; core_types::code_points(&M) }))
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `checkDecl` (`Checker.lean:419-562`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// Check a single declaration, extending the environment on success.  The
/// cited `match d with` becomes one dispatch and six arm functions, so every
/// arm stays a tail call.
///
/// Deviation: the environment in and out is the *index* (task #18's deviation
/// 3), taken by value and returned (task #14's `FEnv` ruling).  `pins` is
/// `check_div_mod_pin`'s parameter, threaded (task #31).
pub fn check_decl(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe: FEnv,
    d: &Declaration,
) -> CheckM<FEnv> {
    match d {
        Declaration::DefnDecl(cv, value, hint) => {
            check_defn_decl(mode, pins, st, fe, cv, value, hint)
        }
        Declaration::ThmDecl(cv, value) => check_thm_decl(mode, st, fe, cv, value),
        Declaration::OpaqueDecl(cv, value) => check_opaque_decl(mode, st, fe, cv, value),
        Declaration::AxiomDecl(cv) => check_axiom_decl(mode, st, fe, cv),
        Declaration::BasisDecl(kind) => check_basis_decl(fe, kind),
        Declaration::IndDecl(block, n_p) => check_ind_decl(mode, st, fe, block, *n_p),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.defnDecl` arm: the common constant check, the value check, then the
/// two pinned-`Nat` gates.  `pins` is `check_div_mod_pin`'s parameter,
/// threaded (task #31).
pub fn check_defn_decl(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
    hint: &ReducibilityHint,
) -> CheckM<FEnv> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val_borrowed(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => match check_defn_val(mode, st, fe, &cv_a, value, hint) {
            Err(err) => Err(err),
            Ok(fe2) => check_defn_pins(mode, pins, st, fe2, k_pre, &cv_a.name),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:73-97 checkConstantVal
/// `checkConstantVal` at a borrowed index — the arms call it before the push,
/// where the index is still theirs to lend.
pub fn check_constant_val_borrowed(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckM<ConstantVal> {
    checker_base::check_constant_val(mode, st, fe, cv)
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.defnDecl` arm's two pinned-`Nat` gates.  **Structural-`Nat` pins**:
/// the fast-path ops must be the standard structural recursions, so their
/// recurrence equations are checked by definitional equality here, once, in
/// the *pre-insertion* environment with the operation's self-references
/// replaced by its stored value — certifying after insertion would let the
/// operation's own fast path discharge its all-literal equations vacuously.
/// **WF-recursive `Nat` pins** (`Nat.div`/`Nat.mod`): `check_div_mod_pin`.
///
/// `pins` is `check_div_mod_pin`'s parameter, threaded (task #31).
pub fn check_defn_pins(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe2: FEnv,
    k_pre: u64,
    n: &Name,
) -> CheckM<FEnv> {
    if name::contains(&core_k::nat_op_names(), n) {
        match check_structural_nat_pin(mode, st, fe2, k_pre, n) {
            Err(err) => Err(err),
            Ok(fe3) => check_defn_div_mod_pin(mode, pins, st, fe3, k_pre, n),
        }
    } else {
        check_defn_div_mod_pin(mode, pins, st, fe2, k_pre, n)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `natDivModNames.contains` gate of the `.defnDecl` arm.  `pins` is
/// `check_div_mod_pin`'s parameter, threaded (task #31).
pub fn check_defn_div_mod_pin(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe2: FEnv,
    k_pre: u64,
    n: &Name,
) -> CheckM<FEnv> {
    if name::contains(&core_k::nat_div_mod_names(), n) {
        check_div_mod_pin(mode, pins, st, fe2, k_pre, n)
    } else {
        Ok(fe2)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The structural-`Nat` gate: the environment guards at the extended
/// environment, then `certifyNatEqs` at the pre-insertion one over the
/// equations with the operation's self-references substituted.
pub fn check_structural_nat_pin(
    mode: &CheckMode,
    st: &mut CState,
    fe2: FEnv,
    k_pre: u64,
    n: &Name,
) -> CheckM<FEnv> {
    if !core_k::nat_op_guard(&fe2, n)
        || !deps_all_stored_ok(&fe2, &core_k::nat_op_deps(n), 0)
    {
        Err(core_types::not_implemented({ const M: [u32; 48] = [110, 111, 110, 115, 116, 97, 110, 100, 97, 114, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116]; core_types::code_points(&M) }))
    } else {
        match core_k::defn_probe(&fe2, n) {
            None => Err(core_types::internal({ const M: [u32; 35] = [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110, 32, 110, 111, 116, 32, 115, 116, 111, 114, 101, 100]; core_types::code_points(&M) })),
            Some((_, value2, _)) => {
                let eqs: Vec<(Expr, Expr)> =
                    nat_eqs_subst(n, &value2, &core_k::nat_op_equations(0, n));
                let k2: u64 = fe2.visible_below;
                let fe_pre: FEnv = fenv::restrict_to(fe2, k_pre);
                let r: CheckM<bool> = certify_nat_eqs(mode, st, &fe_pre, &eqs);
                let fe2: FEnv = fenv::restrict_to(fe_pre, k2);
                match r {
                    Err(err) => Err(err),
                    Ok(ok) => {
                        if ok {
                            Ok(fe2)
                        } else {
                            Err(core_types::not_implemented({ const M: [u32; 36] = [110, 111, 110, 115, 116, 97, 110, 100, 97, 114, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 78, 97, 116, 32, 111, 112, 101, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: none — `(natOpEquations 0 c).map (substConst0 c value' ·)` of `checkDecl`
/// `List.map` over the equation pairs; DESIGN.md §3.4 forbids the closure.
pub fn nat_eqs_subst(n: &Name, value2: &Expr, eqs: &Vec<(Expr, Expr)>) -> Vec<(Expr, Expr)> {
    nat_eqs_subst_from(n, value2, eqs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `nat_eqs_subst`
/// The accumulator is passed by value and returned.
pub fn nat_eqs_subst_from(
    n: &Name,
    value2: &Expr,
    eqs: &Vec<(Expr, Expr)>,
    i: usize,
    out: Vec<(Expr, Expr)>,
) -> Vec<(Expr, Expr)> {
    if i >= eqs.len() {
        out
    } else {
        let mut out = out;
        out.push((
            core_k::subst_const0(n, value2, &eqs[i].0),
            core_k::subst_const0(n, value2, &eqs[i].1),
        ));
        nat_eqs_subst_from(n, value2, eqs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.thmDecl` arm.
pub fn check_thm_decl(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<FEnv> {
    match check_constant_val_borrowed(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => check_thm_val(mode, st, fe, &cv_a, value),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.opaqueDecl` arm: the opaque check, then the compiler-trust gate for
/// `Lean.reduceNat`/`Lean.reduceBool`.
pub fn check_opaque_decl(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckM<FEnv> {
    let k_pre: u64 = fe.visible_below;
    match check_constant_val_borrowed(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => match check_opaque_val(mode, st, fe, &cv_a, value) {
            Err(err) => Err(err),
            Ok(fe2) => {
                if name::contains(&trust_axioms::reduce_op_names(), &cv_a.name) {
                    check_reduce_pin(mode, st, fe2, k_pre, &cv_a.name, value)
                } else {
                    Ok(fe2)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.axiomDecl` arm.  Pinned axioms are *installed*: the two standard
/// axioms and the `Init` compiler-trust family, with all types and the shapes
/// of the inductives they quantify over pinned.  The tolerated whitelist
/// (`toleratedAxiomNames` — exactly `sorryAx`) is well-formedness-checked but
/// not stored; the run continues and the frontend positively declines any
/// later declaration that references the skipped axiom.  Any other axiom is a
/// positive decline at its own record; a *pinned name* with a non-pinned
/// shape likewise, because the pin would otherwise shadow.
pub fn check_axiom_decl(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    cv: &ConstantVal,
) -> CheckM<FEnv> {
    match check_constant_val_borrowed(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok(cv_a) => {
            if std_axioms::std_axiom_ok(&fe, &cv_a) {
                Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
            } else if name::beq(&cv_a.name, &trust_axioms::trust_compiler_name()) {
                if trust_axioms::trust_compiler_ok(&fe, &cv_a) {
                    Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 36] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 76, 101, 97, 110, 46, 116, 114, 117, 115, 116, 67, 111, 109, 112, 105, 108, 101, 114, 32, 115, 104, 97, 112, 101]; core_types::code_points(&M) }))
                }
            } else if name::beq(&cv_a.name, &trust_axioms::of_reduce_nat_name())
                || name::beq(&cv_a.name, &trust_axioms::of_reduce_bool_name())
            {
                if trust_axioms::of_reduce_ax_ok(&fe, &cv_a) {
                    Ok(fenv::push(fe, ConstantInfo::AxiomInfo(cv_a)))
                } else {
                    Err(core_types::not_implemented({ const M: [u32; 44] = [117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 99, 111, 109, 112, 105, 108, 101, 114, 45, 116, 114, 117, 115, 116, 32, 97, 120, 105, 111, 109, 32, 101, 110, 118, 105, 114, 111, 110, 109, 101, 110, 116]; core_types::code_points(&M) }))
                }
            } else if name::beq(&cv_a.name, &std_axioms::propext_name())
                || name::beq(&cv_a.name, &std_axioms::choice_name())
            {
                Err(core_types::not_implemented({ const M: [u32; 29] = [115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109, 32, 115, 104, 97, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
            } else if name::contains(&std_axioms::tolerated_axiom_names(), &cv_a.name) {
                Ok(fe)
            } else {
                Err(core_types::not_implemented({ const M: [u32; 18] = [110, 111, 110, 45, 115, 116, 97, 110, 100, 97, 114, 100, 32, 97, 120, 105, 111, 109]; core_types::code_points(&M) }))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.basisDecl` arm: install the pinned (pre-annotated) basis block; the
/// frontend has already matched the incoming record against the pinned
/// shapes.  The quotient block's types mention the pinned equality former, so
/// it requires the pinned `Eq` basis.
///
/// The block itself is `basis_tables::basis_decls_a` — `BasisKind.declsA`,
/// generated from con-leche's own value (task #22), because the annotated
/// pins are produced by the annotation pass at elaboration time and the Rust
/// core has no elaborator.  `proof/ConRon/Refine/BasisTables.lean` proves
/// that what the table builds abstracts to the cited `declsA`.
pub fn check_basis_decl(fe: FEnv, kind: &BasisKind) -> CheckM<FEnv> {
    match kind {
        BasisKind::QuotK => {
            if !basis_pins::eq_basis_pinned(&fe) {
                Err(core_types::not_implemented({ const M: [u32; 43] = [113, 117, 111, 116, 105, 101, 110, 116, 32, 98, 97, 115, 105, 115, 32, 114, 101, 113, 117, 105, 114, 101, 115, 32, 116, 104, 101, 32, 112, 105, 110, 110, 101, 100, 32, 69, 113, 32, 98, 97, 115, 105, 115]; core_types::code_points(&M) }))
            } else {
                install_basis_decls(fe, &basis_tables::basis_decls_a(kind), 0)
            }
        }
        _ => install_basis_decls(fe, &basis_tables::basis_decls_a(kind), 0),
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `kind.declsA.foldlM installBasisDecl env` of the `.basisDecl` arm, as
/// an index recursion threading the index by value.
pub fn install_basis_decls(fe: FEnv, decls: &Vec<ConstantInfo>, i: usize) -> CheckM<FEnv> {
    if i >= decls.len() {
        Ok(fe)
    } else {
        match install_basis_decl(fe, env::constant_info_dup(&decls[i])) {
            Err(err) => Err(err),
            Ok(fe2) => install_basis_decls(fe2, decls, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:419-562 checkDecl
/// The `.indDecl` arm.  **The declared parameter count first, and for both
/// routes** (con-leche task #228): official reads `nparams` off the
/// declaration and checks the block against it, and `indParamsOk` is that
/// check, one-sided, so a `false` is official's own reject.  It runs BEFORE
/// the dispatch because it is a property of the DECLARATION and not of a
/// route.
///
/// Deviation: the dispatch itself — `nativeParts?` and the two installs
/// `checkNative` / `checkModeled` — is `ConLeche/Kernel/Inductives/*`, a
/// family this task does not port, so the arm declines past the parameter
/// check.  A decline can only make the Rust *reject*, which is sound for the
/// accept direction (DESIGN.md §1).
pub fn check_ind_decl(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    block: &Vec<ConstantInfo>,
    n_p: u64,
) -> CheckM<FEnv> {
    let _ = mode;
    let _ = st;
    let _ = fe;
    if env::ind_params_ok(n_p, block) {
        Err(core_types::not_implemented({ const M: [u32; 54] = [105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 98, 108, 111, 99, 107, 58, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 108, 108, 32, 114, 111, 117, 116, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 112, 111, 114, 116, 101, 100, 32, 121, 101, 116]; core_types::code_points(&M) }))
    } else {
        Err(core_types::invalid({ const M: [u32; 29] = [110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 109, 105, 115, 109, 97, 116, 99, 104]; core_types::code_points(&M) }))
    }
}

/// con-leche: ConLeche/Kernel/Checker.lean:564-567 checkDeclsPure
/// Check a list of declarations in order, starting from the empty
/// environment.  Deviation: the fold starts at the *index* of the empty
/// environment, and the `CState` the memoizing knot needs is the caller's.
pub fn check_decls_pure(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    ds: &Vec<Declaration>,
) -> CheckM<FEnv> {
    check_decls_pure_from(mode, pins, st, fenv::mk_fenv(env::empty()), ds, 0)
}

/// con-leche: ConLeche/Kernel/Checker.lean:564-567 checkDeclsPure
/// The cited `foldlM` as an index recursion threading the index by value.
pub fn check_decls_pure_from(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe: FEnv,
    ds: &Vec<Declaration>,
    i: usize,
) -> CheckM<FEnv> {
    if i >= ds.len() {
        Ok(fe)
    } else {
        match check_decl(mode, pins, st, fe, &ds[i]) {
            Err(err) => Err(err),
            Ok(fe2) => check_decls_pure_from(mode, pins, st, fe2, ds, i + 1),
        }
    }
}

#[cfg(test)]
mod tests {

    /// The empty pin list, i.e. the `[]` arm of
    /// `checker::check_div_mod_pin_loop` (DESIGN.md §3.6: the list is a
    /// parameter, and the driver is what reads con-leche's own).  No test
    /// here defines a pin-certified `Nat` operation, so the arm is never
    /// reached and the list is only the parameter.
    fn no_pins() -> Vec<NatOpPinSet> {
        Vec::new()
    }
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::checker;
    use crate::kernel::core_k;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env;
    use crate::kernel::env::{
        CheckMode, ConstantInfo, ConstantVal, Declaration, ReducibilityHint,
    };
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::kernel::fenv;
    use crate::kernel::fenv::FEnv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::nat_op_pins::NatOpPinSet;
    use crate::kernel::prop_when;
    use crate::kernel::std_axioms;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn ax(n: Name, ty: Expr) -> ConstantInfo {
        ConstantInfo::AxiomInfo(ConstantVal { name: n, level_params: Vec::new(), ty })
    }

    fn cv(n: Name, ty: Expr) -> ConstantVal {
        ConstantVal { name: n, level_params: Vec::new(), ty }
    }

    /// `A : Sort 1`, `a : A` — hand-built axioms, newest first.
    fn env_aa() -> FEnv {
        let a_ty = expr::mk_const(nm("A"), Vec::new());
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ax(nm("a"), expr::dup(&a_ty)));
        consts.push(ax(nm("A"), expr::sort(level::succ(level::zero()))));
        fenv::mk_fenv(env::env_of(&consts))
    }

    fn is_invalid(e: &CheckError) -> bool {
        match e {
            CheckError::Invalid(_) => true,
            _ => false,
        }
    }

    fn is_not_implemented(e: &CheckError) -> bool {
        match e {
            CheckError::NotImplemented(_) => true,
            _ => false,
        }
    }

    /// **A `defn` whose value does not inhabit its stated type is
    /// `.invalid`.**  `d : A := Sort 1` passes every syntactic guard — the
    /// header types (`A : Sort 1`), the value annotates and resolves — and
    /// then `inferType (Sort 1) = Sort 2` is not definitionally equal to the
    /// axiom `A`, which is the one *reject* `checkDefnVal` can produce.  The
    /// positive control is `d : A := a`, which installs.
    #[test]
    fn a_defn_whose_value_has_the_wrong_type_is_rejected() {
        let mode = CheckMode::Verified;
        let a_ty = expr::mk_const(nm("A"), Vec::new());
        // the reject
        let mut st: CState = state_c::cstate_new();
        let bad = Declaration::DefnDecl(
            cv(nm("d"), expr::dup(&a_ty)),
            expr::sort(level::succ(level::zero())),
            ReducibilityHint::Abbrev,
        );
        match checker::check_decl(&mode, &no_pins(), &mut st, env_aa(), &bad) {
            Ok(_) => panic!("`d : A := Sort 1` must not check"),
            Err(e) => assert!(is_invalid(&e), "a type mismatch is a reject, not a decline"),
        }
        // the positive control: the value is the stored `a : A`
        let mut st2: CState = state_c::cstate_new();
        let good = Declaration::DefnDecl(
            cv(nm("d"), expr::dup(&a_ty)),
            expr::mk_const(nm("a"), Vec::new()),
            ReducibilityHint::Abbrev,
        );
        match checker::check_decl(&mode, &no_pins(), &mut st2, env_aa(), &good) {
            Ok(fe2) => {
                match fenv::find(&fe2, &nm("d")) {
                    Some(ConstantInfo::DefnInfo(cvd, value, _)) => {
                        assert!(name::beq(&cvd.name, &nm("d")));
                        assert!(expr::beq(value, &expr::mk_const(nm("a"), Vec::new())));
                    }
                    _ => panic!("the definition must be installed as a `defnInfo`"),
                }
                // the push advanced the visibility bound by exactly one
                assert_eq!(fe2.visible_below, 3);
                assert_eq!(fe2.env.consts.len(), 3);
            }
            Err(_) => panic!("`d : A := a` must check"),
        }
        // and a duplicate header is rejected before the value is looked at
        let mut st3: CState = state_c::cstate_new();
        let dup = Declaration::DefnDecl(
            cv(nm("a"), expr::dup(&a_ty)),
            expr::mk_const(nm("a"), Vec::new()),
            ReducibilityHint::Abbrev,
        );
        match checker::check_decl(&mode, &no_pins(), &mut st3, env_aa(), &dup) {
            Ok(_) => panic!("a duplicate definition must not check"),
            Err(e) => assert!(is_invalid(&e)),
        }
    }

    /// **The axiom pin.**  A stream declaring `propext` with a type that is
    /// not the pinned one is refused at the `axiomDecl` arm's pinned-name
    /// branch: `stdAxiomOk` says no, the name is neither
    /// `Lean.trustCompiler` nor an `ofReduce*`, and it *is* a pinned name, so
    /// the arm throws "standard axiom shape mismatch" rather than installing
    /// or falling through to the tolerated whitelist.  The same holds for
    /// `Classical.choice`.
    ///
    /// The pin comparison itself is asserted directly, on an environment
    /// that does not carry the pinned `Eq` basis `stdAxiomOk` requires
    /// (`kernel::basis_pins`): the pinned type matches its
    /// own pin, a wrong type does not, and the comparison forgives exactly
    /// the binder prop-ness datum that annotation computes — which is the
    /// deviation note of `std_axioms`, tested.
    #[test]
    fn the_axiom_pin_refuses_a_wrong_propext() {
        let mode = CheckMode::Verified;
        let a_ty = expr::mk_const(nm("A"), Vec::new());
        let mut st: CState = state_c::cstate_new();
        let wrong = Declaration::AxiomDecl(cv(std_axioms::propext_name(), expr::dup(&a_ty)));
        match checker::check_decl(&mode, &no_pins(), &mut st, env_aa(), &wrong) {
            Ok(_) => panic!("a mis-shaped `propext` must never be installed"),
            Err(e) => assert!(
                is_not_implemented(&e),
                "a pinned name with a non-pinned shape is a positive decline"
            ),
        }
        let mut st2: CState = state_c::cstate_new();
        let wrong_choice =
            Declaration::AxiomDecl(cv(std_axioms::choice_name(), expr::dup(&a_ty)));
        match checker::check_decl(&mode, &no_pins(), &mut st2, env_aa(), &wrong_choice) {
            Ok(_) => panic!("a mis-shaped `Classical.choice` must never be installed"),
            Err(e) => assert!(is_not_implemented(&e)),
        }
        // an axiom that is neither pinned nor tolerated is a decline too
        let mut st3: CState = state_c::cstate_new();
        let other = Declaration::AxiomDecl(cv(nm("myAxiom"), expr::dup(&a_ty)));
        match checker::check_decl(&mode, &no_pins(), &mut st3, env_aa(), &other) {
            Ok(_) => panic!("a non-standard axiom must not be installed"),
            Err(e) => assert!(is_not_implemented(&e)),
        }
        // `sorryAx` is *tolerated*: well-formedness-checked, not stored, and
        // the environment comes back unchanged
        let mut st4: CState = state_c::cstate_new();
        let sorry_ax = Declaration::AxiomDecl(cv(nm("sorryAx"), expr::dup(&a_ty)));
        match checker::check_decl(&mode, &no_pins(), &mut st4, env_aa(), &sorry_ax) {
            Ok(fe) => {
                assert!(fenv::find(&fe, &nm("sorryAx")).is_none());
                assert_eq!(fe.visible_below, 2);
            }
            Err(_) => panic!("`sorryAx` is tolerated, not declined"),
        }
        // the pin comparison, directly: reflexive on the pin, false on a
        // wrong type, and blind to the binder prop-ness datum
        let pin = std_axioms::propext_raw();
        assert!(std_axioms::matches_pin_fast(&pin, &std_axioms::propext_raw()));
        assert!(!std_axioms::matches_pin_fast(
            &cv(std_axioms::propext_name(), expr::dup(&a_ty)),
            &std_axioms::propext_raw()
        ));
        let annotated = ConstantVal {
            name: std_axioms::propext_name(),
            level_params: Vec::new(),
            ty: repw(&pin.ty),
        };
        assert!(
            std_axioms::matches_pin_fast(&annotated, &std_axioms::propext_raw()),
            "matchesPin forgives the pw datum, which is all annotation changes"
        );
        assert!(!expr::beq(&annotated.ty, &pin.ty), "the terms do differ");
    }

    /// Rewrite every binder's prop-ness datum to `ifAllZero []` — a stand-in
    /// for what the annotation pass computes, and the only thing it changes
    /// in a `letE`-free pin.
    fn repw(e: &Expr) -> Expr {
        let m = expr::binder_meta(prop_when::if_all_zero(Vec::new()));
        match &e.0.kind {
            expr::ExprKind::ForallE(t, b, _) => expr::forall_e(repw(t), repw(b), m),
            expr::ExprKind::Lam(t, b, _) => expr::lam(repw(t), repw(b), m),
            expr::ExprKind::App(f, a) => expr::app(repw(f), repw(a)),
            _ => expr::dup(e),
        }
    }

    /// The hand-pinned certificate *statements* (`divModCertStmts`): three
    /// certificates for `Nat.div`/`Nat.mod` (the recursive step under two
    /// `Nat.ble` guards, and two base cases), two for each bitwise and shift
    /// operation, and the `Nat.div`/`Nat.mod` right-hand sides differ in
    /// exactly the `Nat.succ` and the base value.
    #[test]
    fn the_pinned_certificate_statements() {
        let div = checker::div_mod_cert_stmts(&core_k::nat_div_name());
        let md = checker::div_mod_cert_stmts(&core_k::nat_mod_name());
        assert_eq!(div.len(), 3);
        assert_eq!(md.len(), 3);
        assert_eq!(div[0].0.len(), 2, "the recursive step has two guards");
        assert_eq!(div[1].0.len(), 1);
        for c in [
            core_k::nat_gcd_name(),
            core_k::nat_land_name(),
            core_k::nat_lor_name(),
            core_k::nat_xor_name(),
            core_k::nat_shift_left_name(),
            core_k::nat_shift_right_name(),
        ] {
            assert_eq!(checker::div_mod_cert_stmts(&c).len(), 2);
        }
        // `div`'s base value is `Nat.zero`, `mod`'s is `x`
        assert!(expr::beq(
            &checker::cert_base_rhs(&core_k::nat_div_name()),
            &checker::cert_zero()
        ));
        assert!(expr::beq(
            &checker::cert_base_rhs(&core_k::nat_mod_name()),
            &checker::cert_x()
        ));
        // the statements are open over `fvar 0`/`fvar 1` at `Nat`
        assert!(expr::beq(&checker::cert_x(), &expr::fvar(0, checker::cert_nat_ty())));
        assert!(expr::beq(&checker::cert_y(), &expr::fvar(1, checker::cert_nat_ty())));
        // and the proof is applied to one `fvar` per hypothesis
        let p = expr::mk_const(nm("pf"), Vec::new());
        let applied = checker::div_mod_cert_applied(&p, &div[0].0);
        assert_eq!(crate::kernel::expr_ops::get_app_args(&applied).len(), 4);
        let applied1 = checker::div_mod_cert_applied(&p, &div[1].0);
        assert_eq!(crate::kernel::expr_ops::get_app_args(&applied1).len(), 3);
    }

    /// The pin loop over an **empty** variant list is its `[]` arm: the
    /// stream declines, exactly as con-leche does for one matching no
    /// variant.  `nat_op_pin_sets` is task #22's table and is empty for now,
    /// so this is the loop's current behaviour end to end.
    #[test]
    fn the_pin_loop_declines_when_no_variant_matches() {
        let mode = CheckMode::Verified;
        let fe = env_aa();
        let mut st: CState = state_c::cstate_new();
        let variants: Vec<NatOpPinSet> = no_pins();
        assert_eq!(variants.len(), 0);
        let value = expr::mk_const(nm("a"), Vec::new());
        match checker::check_div_mod_pin_loop(
            &mode,
            &mut st,
            &fe,
            &core_k::nat_div_name(),
            &value,
            &variants,
            0,
        ) {
            Ok(()) => panic!("no variant can match an empty table"),
            Err(e) => assert!(is_not_implemented(&e), "no variant matching is a decline"),
        }
    }

    /// `checkDeclsPure` on the empty stream is the empty environment, and a
    /// two-declaration stream installs both in order.
    #[test]
    fn check_decls_pure_folds_in_order() {
        let mode = CheckMode::Verified;
        let mut st: CState = state_c::cstate_new();
        match checker::check_decls_pure(&mode, &no_pins(), &mut st, &Vec::new()) {
            Ok(fe) => {
                assert_eq!(fe.env.consts.len(), 0);
                assert_eq!(fe.visible_below, 0);
            }
            Err(_) => panic!("the empty stream checks"),
        }
        // `A : Sort 1` then `d : A := ...` — the second reads the first
        let mut st2: CState = state_c::cstate_new();
        let mut ds: Vec<Declaration> = Vec::new();
        ds.push(Declaration::AxiomDecl(cv(
            nm("A"),
            expr::sort(level::succ(level::zero())),
        )));
        ds.push(Declaration::DefnDecl(
            cv(nm("d"), expr::sort(level::succ(level::zero()))),
            expr::mk_const(nm("A"), Vec::new()),
            ReducibilityHint::Abbrev,
        ));
        // the first record is a non-standard axiom, so the fold declines at
        // it — which is the checker's own verdict, and it stops the fold
        match checker::check_decls_pure(&mode, &no_pins(), &mut st2, &ds) {
            Ok(_) => panic!("`A` is a non-standard axiom and must decline"),
            Err(e) => assert!(is_not_implemented(&e)),
        }
        // `installBasisDecl` is duplicate-checked on its own terms
        let fe = env_aa();
        match checker::install_basis_decl(fe, ax(nm("a"), expr::sort(level::zero()))) {
            Ok(_) => panic!("a duplicate basis constant must not install"),
            Err(e) => assert!(is_invalid(&e)),
        }
        let fe2 = env_aa();
        match checker::install_basis_decl(fe2, ax(nm("B"), expr::sort(level::zero()))) {
            Ok(fe3) => {
                assert!(fenv::find(&fe3, &nm("B")).is_some());
                // `consts` is oldest first, so the fresh constant is last
                let last = fe3.env.consts.len() - 1;
                assert_eq!(
                    env::constant_info_name(&fe3.env.consts[last]).0.hash,
                    nm("B").0.hash
                );
            }
            Err(_) => panic!("a fresh basis constant installs"),
        }
    }
}
