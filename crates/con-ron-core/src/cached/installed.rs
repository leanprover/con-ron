//! `ConLeche/Cached/Installed.lean` — **the declaration fold**: install
//! first, check afterwards.  `check_decls` is the port's entry point, the
//! function the binary runs and the one the refinement tier's capstone will
//! be stated about.
//!
//! The fold has two phases (the cited module docstring, `:8-59`):
//!
//! * **Phase A** folds `annot_decl_step` over the parsed records.  A
//!   `defn`/`opaque` record is annotated and INSTALLED without its
//!   inference; a `thm` record is installed BY STATEMENT (its header alone is
//!   annotated, the value is stored raw and never entered here).  Either way
//!   a `PendingCheck` (`crate::cached::parsed_c`) records what the check
//!   needs — the `ValueGroup` and the environment counter
//!   `fe.visible_below` the declaration was installed at.  Every other kind
//!   — axioms, inductive and basis blocks, and the pinned `Nat`-operation and
//!   `reduce*` branches, whose checks are not separable from their installs —
//!   takes the ordinary step `parsed_c::check_decl_step_c`.
//! * **Phase B** checks each record against the PREFIX VIEW
//!   `fenv::restrict_to(fe, pc.vis)`, each from a FRESH `CState`.
//!
//! A rejection carries the FOLD POSITION of the declaration it names, so the
//! driver reports the declaration by indexing the record list it already
//! holds.
//!
//! ## What is not ported, and why
//!
//! Everything in the cited file past `checkPendingList` that is *proof*:
//! `InstallRun` (`:186-191`), `InstalledEnv` (`:223-230`), `GroupChecked`
//! (`:259-262`), `FullyChecked`/`.assemble`/`.env` (`:266-274`),
//! `checkRecord` (`:337-341`), `CheckedRecord`/`RecordResult`/
//! `checkRecordResult` (`:345-358`), `collectChecks` (`:367-383`) and the ten
//! theorems.  These are the *parallel driver's* evidence plumbing: every one
//! of them is indexed by a `Prop` (`InstallRun`, `GroupChecked`) or returns
//! one (`PLift (GroupChecked …)`, `PLift (∀ i, …)`), so their run-time
//! content is either nothing at all or the `Nat` inside
//! `CheckedRecord = { k : Nat // GroupChecked … }`.  `checkRecord` computes
//! `checkPending` and throws its value away for a proof; `collectChecks`
//! walks a table of such proofs.  Rust has no `Prop`, so porting them would
//! mean inventing a run-time representation for evidence that con-leche
//! erases — and the thing they *decide*, "the first failing record in fold
//! order", is `check_pending_list`, which is ported and is what
//! `check_decls` runs.  A future parallel check phase (P4) re-derives the
//! plumbing in the Rust world against `check_pending`; the *verdict* it must
//! agree with is this file's.
//!
//! The taint-skip decline (`Main.lean:637-645`) is a **driver** rule above
//! `check_decls`: the frontend's skipped declarations never reach the fold,
//! and a clean fold over a stream with skips is still a decline.  The core
//! must not implement it (task #10's surprise 9); `con-ron-check` does.
//!
//! ## Deviations from the cited code
//!
//! 1. **The accumulator is a flat 3-tuple.**  Lean's
//!    `Nat × FEnv × Array PendingCheck` is right-nested and read by `.1`,
//!    `.2.1`, `.2.2`; the Rust is `(u64, FEnv, Vec<PendingCheck>)` and the
//!    `Nat`s are `u64` (§3.3).  `Array` is `Vec`.
//! 2. **The index is threaded by value** (task #14): every function here
//!    that the Lean gives an `FEnv` and returns a new one takes it by value
//!    and hands it back, and `check_pending` — whose Lean body shadows `fe`
//!    with `fe.restrictTo pc.vis` — takes the index at the installed bound,
//!    restricts it, and hands it back at the bound it came in at
//!    (`checker::check_div_mod_pin`'s deviation, module note 1 there).  A
//!    copy is not an option: `fenv::dup` rebuilds the whole index, so a copy
//!    per record would make phase B quadratic where con-leche's `restrictTo`
//!    is an `O(1)` field update.
//! 3. **The two folds are index recursions** (§3.4: no loops), as
//!    `checker::check_decls_pure_from` is: `annot_decl_fold_from(…, ds, i)`
//!    is the cited `foldlM` applied to `ds[i..]` and
//!    `check_pending_list_from(…, pend, i)` the cited `List` recursion at
//!    `pend[i..]`.
//! 4. **`check_decls` takes the pin list as a parameter** (§3.6's task-#22
//!    ruling): `pins : Vec NatOpPinSet` is data, not code.  This was a
//!    deviation while the cited code read the global `natOpPinSets`; the
//!    upstream change the ruling asked for — `checkDecls mode ds pins`, with
//!    the shipped fold its default — landed as con-leche task #285 and is
//!    vendored at task #74, so **the cited fold takes the list too** and the
//!    refinement is stated at the abstract list with no hypothesis about it.
//!    Task #31 threaded it all the way down —
//!    `annot_decl_fold_from` → `annot_decl_step` →
//!    `annot_step_c` → `parsed_c::check_decl_step_c` → … →
//!    `checker::check_div_mod_pin_loop`, whose `variants` it *is* — and
//!    deleted `kernel::nat_op_pins`' empty stub.  An **empty** list is still
//!    the loop's `[]` arm, i.e. a `Nat.div`/`Nat.mod` stream declines, which
//!    is sound for the accept direction (§1); the binary's own list is the
//!    embedded text `kernel::pins_text::PINS_TEXT`, decoded in the core
//!    (task #43), and `con-ron-check --pins FILE` is a test override.
//! 5. **Message strings** are the cited ones minus their interpolated names
//!    (§3.1: the theorem never reads them), spelled as `core_types`' code
//!    points — the same texts `parsed_c` and `kernel::checker_split` use, so
//!    a message is not evidence of which lane produced it.

use crate::cached::expr_ops_c;
use crate::cached::parsed_c;
use crate::cached::parsed_c::DeclC;
use crate::cached::parsed_c::PendingCheck;
use crate::cached::parsed_c::ValueGroup;
use crate::cached::parsed_c::ValueKind;
use crate::cached::state_c;
use crate::cached::state_c::CState;
use crate::cached::state_c::CheckCM;
use crate::kernel::basis_names;
use crate::kernel::checker_split;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::env;
use crate::kernel::env::CheckMode;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::ConstantVal;
use crate::kernel::env::Env;
use crate::kernel::env::ReducibilityHint;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::name;
use crate::kernel::nat_op_pins::NatOpPinSet;
use crate::kernel::prop_when;
use crate::kernel::trust_axioms;
use crate::kernel::type_checker;
use crate::kernel::validate;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// Phase A: install (`Installed.lean:68-180`)
// ---------------------------------------------------------------------------
//
// `PendingCheck` (`:74-77`) is `crate::cached::parsed_c` (task #14 took the
// three seam records together).

/// con-leche: ConLeche/Cached/Installed.lean:96-115 annotConstantValC
/// `checkConstantValC` minus its inference: the syntactic guards and the
/// annotation of the type — `checker_split::install_constant_val`'s cached
/// twin, i.e. that function with the `ExprC` guards of
/// `cached::expr_ops_c` and `constsResolveFC`.  Returns the header with its
/// type annotated, together with that type: the cited
/// `(⟨cv.name, cv.levelParams, jty⟩, jty)`, both components the same node.
///
/// Split at the annotation, as `parsed_c::check_constant_val_c` is: the
/// state-threading call is then a tail call and the two guard groups do not
/// join on a borrowed state (task #24's deviation 7).
pub fn annot_constant_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
) -> CheckCM<(ConstantVal, Expr)> {
    if fenv::find(fe, &cv.name).is_some() {
        Err(core_types::invalid({ const M: [u32; 21] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if name::contains(&basis_names::reserved_basis_names(), &cv.name) {
        Err(core_types::invalid({ const M: [u32; 19] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if level::name_is_proj_fn_shape(&cv.name) {
        Err(core_types::invalid({ const M: [u32; 24] = [114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 110, 97, 109, 101]; core_types::code_points(&M) }))
    } else if !level::name_nodup(&cv.level_params) {
        Err(core_types::invalid({ const M: [u32; 44] = [100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
    } else if !expr_ops_c::loose_bvars_bounded(0, &cv.ty) {
        Err(core_types::invalid({ const M: [u32; 28] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(&cv.ty) {
        Err(core_types::invalid({ const M: [u32; 32] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, &cv.ty) {
            Err(err) => Err(err),
            Ok(jty) => annot_constant_val_c_after_annot(fe, cv, jty),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:96-115 annotConstantValC
/// The tail past the annotation: the level-parameter and resolution guards on
/// the annotated type, and the header the cited `pure` builds.  Unlike
/// `parsed_c::check_constant_val_c_after_annot` there is no inference here —
/// that is exactly what phase A leaves to `check_pending` — so this needs
/// neither the mode nor the state.
pub fn annot_constant_val_c_after_annot(
    fe: &FEnv,
    cv: &ConstantVal,
    jty: Expr,
) -> CheckCM<(ConstantVal, Expr)> {
    if !expr_ops_c::all_level_params_defined(&cv.level_params, &jty) {
        Err(core_types::invalid({ const M: [u32; 37] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(fe, &jty) {
        Err(core_types::invalid({ const M: [u32; 24] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 116, 121, 112, 101]; core_types::code_points(&M) }))
    } else {
        let cv_a: ConstantVal = ConstantVal {
            name: name::dup(&cv.name),
            level_params: prop_when::names_copy(&cv.level_params),
            ty: expr::dup(&jty),
        };
        Ok((cv_a, jty))
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:121-133 annotValC
/// The value half of `checkDefnValC`/`checkThmValC`/`checkOpaqueValC` minus
/// its inference: the guards, the annotation, and the converted-constant
/// record — `checker_split::install_value`'s cached twin.  `record` is
/// `false` for an opaque, whose value is a discarded witness, and for the
/// theorem value phase B annotates.
pub fn annot_val_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    value: &Expr,
    record: bool,
) -> CheckCM<Expr> {
    if !expr_ops_c::loose_bvars_bounded(0, value) {
        Err(core_types::invalid({ const M: [u32; 29] = [108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if expr_ops_c::has_fvar(value) {
        Err(core_types::invalid({ const M: [u32; 33] = [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        match type_checker::annotate_core(mode, st, fe, 0, value) {
            Err(err) => Err(err),
            Ok(jv) => annot_val_c_after_annot(st, fe, cv_a, jty, jv, record),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:121-133 annotValC
/// The tail past the annotation: the two guards on the annotated value and
/// the `ienv` record, tagged with the very `Expr` objects the install pushes
/// (`vE := jv`, so both components of the value pair are that node).  The
/// record runs on the *accepting* path only, as the cited `do` block has it.
pub fn annot_val_c_after_annot(
    st: &mut CState,
    fe: &FEnv,
    cv_a: &ConstantVal,
    jty: &Expr,
    jv: Expr,
    record: bool,
) -> CheckCM<Expr> {
    if !expr_ops_c::all_level_params_defined(&cv_a.level_params, &jv) {
        Err(core_types::invalid({ const M: [u32; 38] = [117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else if !state_c::consts_resolve_fc(fe, &jv) {
        Err(core_types::invalid({ const M: [u32; 25] = [117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 105, 110, 32, 118, 97, 108, 117, 101]; core_types::code_points(&M) }))
    } else {
        state_c::record_c_const(
            st,
            name::dup(&cv_a.name),
            expr::dup(&cv_a.ty),
            expr::dup(jty),
            annot_val_c_record(&jv, record),
        );
        Ok(jv)
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:121-133 annotValC
/// The cited `if record then some (jv, jv) else none`, as a function: the
/// branch would otherwise sit inside an argument of `recordCConst` with the
/// state borrowed (task #24's rule — an arm must end in a call or a
/// constructor, never in a branch).
pub fn annot_val_c_record(jv: &Expr, record: bool) -> Option<(Expr, Expr)> {
    if record {
        Some((expr::dup(jv), expr::dup(jv)))
    } else {
        None
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:139-144 annotValueC
/// Phase A's install of a separable value declaration: the per-declaration
/// flush, then the header's and the value's install halves; returns the
/// header with its annotated type, that type, and the annotated value.
pub fn annot_value_c(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv: &ConstantVal,
    value: &Expr,
    record: bool,
) -> CheckCM<(ConstantVal, Expr, Expr)> {
    state_c::flush_c(st);
    match annot_constant_val_c(mode, st, fe, cv) {
        Err(err) => Err(err),
        Ok(r) => annot_value_c_tail(mode, st, fe, r.0, r.1, value, record),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:139-144 annotValueC
/// The cited tail past `annotConstantValC`: the value's install half, and the
/// triple.  Split off so the header's call is a tail call.
pub fn annot_value_c_tail(
    mode: &CheckMode,
    st: &mut CState,
    fe: &FEnv,
    cv_a: ConstantVal,
    jty: Expr,
    value: &Expr,
    record: bool,
) -> CheckCM<(ConstantVal, Expr, Expr)> {
    match annot_val_c(mode, st, fe, &cv_a, &jty, value, record) {
        Err(err) => Err(err),
        Ok(jv) => Ok((cv_a, jty, jv)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// Phase A's step body: annotate-and-install for the three value kinds, the
/// ordinary step `parsed_c::check_decl_step_c` for everything else.  `i` is
/// the fold position the record is tagged with.
///
/// The four arms are four functions, so every one of them is a tail call
/// (task #18's rule for a gated cascade, as `parsed_c::check_decl_c`).
/// Deviation: where the cited arms rebuild the declaration they matched
/// (`checkDeclStepC mode fe (.defnDecl cv value hint)`) the port hands
/// `check_decl_step_c` the `pd` it already has — the same value, one copy
/// fewer.
pub fn annot_step_c(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    pd: &DeclC,
) -> CheckCM<(FEnv, Vec<PendingCheck>)> {
    match pd {
        DeclC::DefnDecl(cv, value, hint) => {
            annot_step_defn_c(mode, pins, st, i, fe, pend, pd, cv, value, hint)
        }
        DeclC::ThmDecl(cv, value) => annot_step_thm_c(mode, st, i, fe, pend, cv, value),
        DeclC::OpaqueDecl(cv, value) => {
            annot_step_opaque_c(mode, pins, st, i, fe, pend, pd, cv, value)
        }
        _ => annot_step_other_c(mode, pins, st, fe, pend, pd),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The `.defnDecl` arm: a pin-certified operation takes the ordinary step
/// (its check is not separable from its install), everything else is
/// annotated, installed, and recorded as pending.
pub fn annot_step_defn_c(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    pd: &DeclC,
    cv: &ConstantVal,
    value: &Expr,
    hint: &ReducibilityHint,
) -> CheckCM<(FEnv, Vec<PendingCheck>)> {
    if name::contains(&core_k::nat_op_names(), &cv.name)
        || name::contains(&core_k::nat_div_mod_names(), &cv.name)
    {
        annot_step_other_c(mode, pins, st, fe, pend, pd)
    } else {
        match annot_value_c(mode, st, &fe, cv, value, true) {
            Err(err) => Err(err),
            Ok(r) => Ok(annot_step_defn_c_push(i, fe, pend, r.0, r.2, hint)),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The cited push, with the RC-linearity read the comment there insists on:
/// **the counter is read BEFORE the push**, so that the index reaches `push`
/// unshared.  The annotated type `r.2.1` is not read — it is `r.1`'s own
/// field.
pub fn annot_step_defn_c_push(
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    cv_a: ConstantVal,
    jv: Expr,
    hint: &ReducibilityHint,
) -> (FEnv, Vec<PendingCheck>) {
    let vis: u64 = fe.visible_below;
    let fe2: FEnv = fenv::push(
        fe,
        ConstantInfo::DefnInfo(
            env::constant_val_dup(&cv_a),
            expr::dup(&jv),
            env::reducibility_hint_dup(hint),
        ),
    );
    let mut pend2: Vec<PendingCheck> = pend;
    pend2.push(PendingCheck {
        vg: ValueGroup {
            kind: ValueKind::Defn,
            cv_a,
            jv,
        },
        pos: i,
        vis,
    });
    (fe2, pend2)
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The `.thmDecl` arm: **a theorem installs BY STATEMENT**.  The header's
/// install half runs and the constant is pushed with the record's own raw
/// value, which nothing ever reads (a theorem is opaque to reduction), so
/// phase A never enters a theorem's body; `check_pending` annotates it, at
/// the view.  The `ienv` record is written here with no value
/// (`recordCConst … none`).
pub fn annot_step_thm_c(
    mode: &CheckMode,
    st: &mut CState,
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckCM<(FEnv, Vec<PendingCheck>)> {
    state_c::flush_c(st);
    match annot_constant_val_c(mode, st, &fe, cv) {
        Err(err) => Err(err),
        Ok(r) => Ok(annot_step_thm_c_push(st, i, fe, pend, r.0, r.1, value)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The theorem arm's record and push.  The raw value is stored twice — in the
/// environment and in the `ValueGroup` — where Lean shares one node (§3.2's
/// copy rule).
pub fn annot_step_thm_c_push(
    st: &mut CState,
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    cv_a: ConstantVal,
    jty: Expr,
    value: &Expr,
) -> (FEnv, Vec<PendingCheck>) {
    state_c::record_c_const(st, name::dup(&cv_a.name), expr::dup(&cv_a.ty), jty, None);
    let vis: u64 = fe.visible_below;
    let fe2: FEnv = fenv::push(
        fe,
        ConstantInfo::ThmInfo(env::constant_val_dup(&cv_a), expr::dup(value)),
    );
    let mut pend2: Vec<PendingCheck> = pend;
    pend2.push(PendingCheck {
        vg: ValueGroup {
            kind: ValueKind::Thm,
            cv_a,
            jv: expr::dup(value),
        },
        pos: i,
        vis,
    });
    (fe2, pend2)
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The `.opaqueDecl` arm: a `reduce*` witness takes the ordinary step (its
/// identity certificate is part of its install), everything else is
/// annotated, installed **as an axiom** — the cited `.axiomInfo`, an opaque's
/// value being a discarded witness — and recorded as pending.
pub fn annot_step_opaque_c(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    pd: &DeclC,
    cv: &ConstantVal,
    value: &Expr,
) -> CheckCM<(FEnv, Vec<PendingCheck>)> {
    if name::contains(&trust_axioms::reduce_op_names(), &cv.name) {
        annot_step_other_c(mode, pins, st, fe, pend, pd)
    } else {
        match annot_value_c(mode, st, &fe, cv, value, false) {
            Err(err) => Err(err),
            Ok(r) => Ok(annot_step_opaque_c_push(i, fe, pend, r.0, r.2)),
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The opaque arm's push, the counter read before it.
pub fn annot_step_opaque_c_push(
    i: u64,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    cv_a: ConstantVal,
    jv: Expr,
) -> (FEnv, Vec<PendingCheck>) {
    let vis: u64 = fe.visible_below;
    let fe2: FEnv = fenv::push(fe, ConstantInfo::AxiomInfo(env::constant_val_dup(&cv_a)));
    let mut pend2: Vec<PendingCheck> = pend;
    pend2.push(PendingCheck {
        vg: ValueGroup {
            kind: ValueKind::Opaque,
            cv_a,
            jv,
        },
        pos: i,
        vis,
    });
    (fe2, pend2)
}

/// con-leche: ConLeche/Cached/Installed.lean:146-185 annotStepC
/// The catch-all arm, shared by the three gated branches above: the ordinary
/// step, which leaves the records untouched — axioms, inductive and basis
/// blocks and the pinned branches are checked in full at their install.
pub fn annot_step_other_c(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    fe: FEnv,
    pend: Vec<PendingCheck>,
    pd: &DeclC,
) -> CheckCM<(FEnv, Vec<PendingCheck>)> {
    match parsed_c::check_decl_step_c(mode, pins, st, fe, pd) {
        Err(err) => Err(err),
        Ok(fe2) => Ok((fe2, pend)),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:187-197 annotDeclStep
/// Phase A's step with the position carried and the error tagged: the
/// accumulator is `(i, fe, pend)`, and a failing step reports the
/// `CheckError` together with `i`, the fold position of the declaration that
/// failed.
///
/// Deviation 1 (the module note): the accumulator is a flat 3-tuple, so the
/// cited `p.1` is `p.0` here and the error is `(err, p.0)`.
pub fn annot_decl_step(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    p: (u64, FEnv, Vec<PendingCheck>),
    pd: &DeclC,
) -> Result<(u64, FEnv, Vec<PendingCheck>), (CheckError, u64)> {
    let i: u64 = p.0;
    match annot_step_c(mode, pins, st, i, p.1, p.2, pd) {
        Err(err) => Err((err, i)),
        Ok(q) => Ok((i + 1, q.0, q.1)),
    }
}

// ---------------------------------------------------------------------------
// Phase B: check (`Installed.lean:232-253`, `:398-403`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:262-276 checkPending
/// Phase B's check of one record **against the prefix view**, from a flushed
/// memo state: `checker_split::check_value_group`'s inference and conversion
/// calls — those of `checkConstantValC` and `check{Defn,Thm,Opaque}ValC`, in
/// their order — on the cached core at the view.  A theorem's value is
/// annotated here, at the view, before it is inferred.
///
/// Deviation 2 (the module note): the index comes in at the installed bound
/// and goes back out there, the cited `let fe := fe.restrictTo pc.vis`
/// happening in between.
pub fn check_pending(
    mode: &CheckMode,
    st: &mut CState,
    fe: FEnv,
    pc: &PendingCheck,
) -> CheckCM<FEnv> {
    state_c::flush_c(st);
    let k: u64 = fe.visible_below;
    let fe_v: FEnv = fenv::restrict_to(fe, pc.vis);
    match type_checker::infer_type_core(mode, st, &fe_v, 0, &pc.vg.cv_a.ty) {
        Err(err) => Err(err),
        Ok(jsty) => match parsed_c::op_s_ix_c(mode, st, &fe_v, 0, &jsty) {
            Err(err) => Err(err),
            Ok(u) => check_pending_value(mode, st, fe_v, k, pc, &u),
        },
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:262-276 checkPending
/// The cited `let jv ← if pc.vg.kind = .thm then … else pure pc.vg.jv`: a
/// theorem's statement must be a proposition, and its raw value's guards and
/// annotation run here (`annot_val_c` — `installValue`'s twin, at the view,
/// with no `ienv` value recorded).  A definition's or opaque's value was
/// annotated at the install and is taken as it is.
pub fn check_pending_value(
    mode: &CheckMode,
    st: &mut CState,
    fe_v: FEnv,
    k: u64,
    pc: &PendingCheck,
    u: &level::Level,
) -> CheckCM<FEnv> {
    if checker_split::is_thm(&pc.vg.kind) {
        match core_k::lift_fueled(level::is_equiv(u, &level::zero())) {
            Err(err) => Err(err),
            Ok(is_prop) => {
                if is_prop {
                    match annot_val_c(
                        mode,
                        st,
                        &fe_v,
                        &pc.vg.cv_a,
                        &pc.vg.cv_a.ty,
                        &pc.vg.jv,
                        false,
                    ) {
                        Err(err) => Err(err),
                        Ok(jv) => check_pending_tail(mode, st, fe_v, k, pc, jv),
                    }
                } else {
                    Err(core_types::invalid({ const M: [u32; 36] = [116, 121, 112, 101, 32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110]; core_types::code_points(&M) }))
                }
            }
        }
    } else {
        check_pending_tail(mode, st, fe_v, k, pc, expr::dup(&pc.vg.jv))
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:262-276 checkPending
/// The cited tail past the `let jv ← if …` join: the value's inferred type
/// against the declared one, and the index handed back at the bound it came
/// in at.  Split off so the two branches of the join are tail calls (task
/// #18's rule for a gated certificate whose arms rejoin).
pub fn check_pending_tail(
    mode: &CheckMode,
    st: &mut CState,
    fe_v: FEnv,
    k: u64,
    pc: &PendingCheck,
    jv: Expr,
) -> CheckCM<FEnv> {
    match type_checker::infer_type_core(mode, st, &fe_v, 0, &jv) {
        Err(err) => Err(err),
        Ok(jvt) => {
            match type_checker::is_def_eq_core(mode, st, &fe_v, 0, &jvt, &pc.vg.cv_a.ty) {
                Err(err) => Err(err),
                Ok(ok) => {
                    if ok {
                        Ok(fenv::restrict_to(fe_v, k))
                    } else {
                        Err(core_types::invalid({ const M: [u32; 28] = [116, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110]; core_types::code_points(&M) }))
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:433-438 checkPendingList
/// Phase B as a pure walk: **every record checked from a fresh memo state**,
/// a failure tagged with the record's fold position.  The entry point of the
/// index recursion below (deviation 3); the index is threaded by value
/// (deviation 2) and handed back, where the Lean returns `Unit` and the
/// caller keeps its own `fe`.
pub fn check_pending_list(
    mode: &CheckMode,
    fe: FEnv,
    pend: &Vec<PendingCheck>,
) -> Result<FEnv, (CheckError, u64)> {
    check_pending_list_from(mode, fe, pend, 0)
}

/// con-leche: ConLeche/Cached/Installed.lean:433-438 checkPendingList
/// The cited `checkPending mode fe pc {}`: one record's check from its own
/// **fresh `CState`**, so no memo crosses from one record's check to the next
/// (§3.1's memo policy — a record is checked at its own prefix view, where
/// another record's entries would be unsound).
///
/// Why this is a function of its own and not a `let` in the walk below (task
/// #32): the Lean's `{}` is consumed by the run and the run's state is
/// *dropped* at the end of the record; in Rust a `let mut st` in the walk's
/// body outlives the walk's recursive call — the frame owns it — so every
/// record's memo tables would stay alive until the whole of phase B is over.
/// That is what made `Init` grow to 21 GB where con-leche peaks at 481 MB.
/// A `CState` created inside this function is dropped when it returns, i.e.
/// before the next record is looked at, which is the Lean's lifetime exactly.
/// No memo *policy* changes: the state is fresh per record either way.
pub fn check_pending_fresh(
    mode: &CheckMode,
    fe: FEnv,
    pc: &PendingCheck,
) -> CheckCM<FEnv> {
    let mut st: CState = state_c::cstate_new();
    check_pending(mode, &mut st, fe, pc)
}

/// con-leche: ConLeche/Cached/Installed.lean:433-438 checkPendingList
/// The cited `List` recursion at `pend[i..]`, one record per step through
/// `check_pending_fresh` (the cited `checkPending … {}`).
pub fn check_pending_list_from(
    mode: &CheckMode,
    fe: FEnv,
    pend: &Vec<PendingCheck>,
    i: usize,
) -> Result<FEnv, (CheckError, u64)> {
    if i >= pend.len() {
        Ok(fe)
    } else {
        match check_pending_fresh(mode, fe, &pend[i]) {
            Err(err) => Err((err, pend[i].pos)),
            Ok(fe2) => check_pending_list_from(mode, fe2, pend, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// The fold (`Installed.lean:405-411`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/Installed.lean:440-447 checkDecls
/// **The declaration fold**: install every record (phase A), check every
/// recorded declaration (phase B), return the environment.  This is the
/// function `ConLeche.no_proof_of_False` is stated about and the algorithm
/// the binary's driver runs.
///
/// Note 4 (the module note): `pins` is the `Nat`-operation pin list, §3.6's
/// parameter, threaded from here through `annot_decl_step` to
/// `checker::check_div_mod_pin_loop` (task #31).  It is the cited fold's own
/// last argument since con-leche task #285 (vendored at task #74), where it
/// defaults to `natOpPinSets`, so this is no longer a deviation.
///
/// Deviation 5 (task #73, and the one line of this function con-leche has no
/// counterpart for — see `kernel::validate`'s module note): before the fold
/// runs, **the input is validated**.  con-leche's `@[computed_field]`s are
/// correct by construction, so `checkDecls` has nothing to check; the port's
/// node fields are `pub`, so a forged `data` word would make `expr::beq`
/// inexact and the refinement false.  `Refine/Main.lean`'s capstones used to
/// assume it away as `hds : ∀ d ∈ ds.val, DeclCWF d`; this pass *establishes*
/// it, and a declaration that fails it is declined with `CheckError::Native`
/// — the port's own failure, about which the full-outcome ruling (DESIGN.md
/// §3) claims nothing.  The position reported is `0`: the outcome is
/// `Native`, so `Installed.ErrSimPos` is vacuous at it, and nothing outside
/// rendering reads the number.
pub fn check_decls(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    ds: &Vec<DeclC>,
) -> Result<Env, (CheckError, u64)> {
    // `.0` on the spot, so the visited set is dropped **here** rather than at
    // the end of the function: a binding that held the whole tuple would keep
    // one table entry per distinct node alive for the length of the fold, and
    // that is 0.5 GB of peak RSS at `Init` scale for nothing (task #73).
    let ok: bool = validate::validate_decls(validate::seen_new(), ds).0;
    if ok {
        check_decls_go(mode, pins, ds)
    } else {
        Err((core_types::native(validate_reject_message()), 0))
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The decline the validation pass produces.  Its own function so that
/// `check_decls`' two branches are each one call, which is what lets
/// `Refine/Validate.lean` state the gate (`check_decls_gate`) without naming
/// the fold's body.
pub fn validate_reject_message() -> Vec<u32> {
    const M: [u32; 49] = [
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 114, 101, 106, 101, 99,
        116, 101, 100, 32, 98, 121, 32, 116, 104, 101, 32, 105, 110, 112, 117, 116, 32,
        118, 97, 108, 105, 100, 97, 116, 105, 111, 110, 32, 112, 97, 115, 115,
    ];
    core_types::code_points(&M)
}

/// con-leche: ConLeche/Cached/Installed.lean:440-447 checkDecls
/// **The fold proper**, i.e. the cited `checkDecls` body: `check_decls` above
/// is this function behind task #73's validation pass.  Split out so that the
/// pass is one line and the refinement lemma's gate can name what follows it
/// (`Refine/Validate.lean`'s `check_decls_gate`,
/// `Refine/Installed.lean`'s `check_decls_refines`).
pub fn check_decls_go(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    ds: &Vec<DeclC>,
) -> Result<Env, (CheckError, u64)> {
    let mut st: CState = state_c::cstate_new();
    match annot_decl_fold_from(
        mode,
        pins,
        &mut st,
        (0, fenv::mk_fenv(env::empty()), Vec::new()),
        ds,
        0,
    ) {
        Err(err) => Err(err),
        Ok(p) => check_decls_phase_b(mode, p.1, p.2),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:440-447 checkDecls
/// The cited `checkPendingList mode p.2.1 p.2.2.toList; pure p.2.1.env`: the
/// records walked, then the environment of the index phase A built.
pub fn check_decls_phase_b(
    mode: &CheckMode,
    fe: FEnv,
    pend: Vec<PendingCheck>,
) -> Result<Env, (CheckError, u64)> {
    match check_pending_list(mode, fe, &pend) {
        Err(err) => Err(err),
        Ok(fe2) => Ok(fe2.env),
    }
}

/// con-leche: ConLeche/Cached/Installed.lean:440-447 checkDecls
/// The cited `ds.foldlM (annotDeclStep mode) (0, mkFEnv Env.empty, #[])` as
/// an index recursion threading the accumulator by value (deviation 3), i.e.
/// the fold applied to `ds[i..]`.  The `CState` is the caller's — the cited
/// `{}` is `check_decls`' own fresh one, and a driver that runs phase A in
/// steps (con-leche's `Main.lean`, `con-ron-check --stats`) owns it across
/// the steps.
pub fn annot_decl_fold_from(
    mode: &CheckMode,
    pins: &Vec<NatOpPinSet>,
    st: &mut CState,
    p: (u64, FEnv, Vec<PendingCheck>),
    ds: &Vec<DeclC>,
    i: usize,
) -> Result<(u64, FEnv, Vec<PendingCheck>), (CheckError, u64)> {
    if i >= ds.len() {
        Ok(p)
    } else {
        match annot_decl_step(mode, pins, st, p, &ds[i]) {
            Err(err) => Err(err),
            Ok(q) => annot_decl_fold_from(mode, pins, st, q, ds, i + 1),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::cached::installed;
    use crate::cached::parsed_c::DeclC;
    use crate::cached::state_c;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env;
    use crate::kernel::env::CheckMode;
    use crate::kernel::env::ConstantVal;
    use crate::kernel::env::Env;
    use crate::kernel::env::ReducibilityHint;
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::kernel::fenv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::nat_op_pins::NatOpPinSet;
    use crate::kernel::validate;
    use crate::ron::ptr;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn no_pins() -> Vec<NatOpPinSet> {
        Vec::new()
    }

    /// `Sort 0`, i.e. `Prop`.
    fn prop() -> Expr {
        expr::sort(level::zero())
    }

    /// `Sort 1`, i.e. `Type` — the type of `Prop`, so `Sort 0 : Sort 1` is
    /// the one true judgement available in the **empty** environment.  An
    /// axiom would need one of con-leche's pins (`checkAxiomDeclC`), and an
    /// honest proposition would need an inductive block, so every stream
    /// here is built out of sorts alone.
    fn type0() -> Expr {
        expr::sort(level::succ(level::zero()))
    }

    fn cv(n: &str, ty: Expr) -> ConstantVal {
        ConstantVal {
            name: nm(n),
            level_params: Vec::new(),
            ty,
        }
    }

    /// `def <n> : <ty> := <value>`.
    fn defn(n: &str, ty: Expr, value: Expr) -> DeclC {
        DeclC::DefnDecl(cv(n, ty), value, ReducibilityHint::Regular(0))
    }

    fn env_names(e: &Env) -> Vec<Name> {
        e.consts
            .iter()
            .map(|c| env::constant_info_name(c))
            .collect()
    }

    /// An empty stream is an accept at the empty environment: both folds run
    /// zero steps.
    #[test]
    fn the_empty_stream_is_accepted() {
        let ds: Vec<DeclC> = Vec::new();
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(e) => assert_eq!(e.consts.len(), 0),
            Err(_) => panic!("the empty stream is an accept"),
        }
    }

    /// Task #73: a **well-formed** declaration passes the validation pass, so
    /// the pass costs an accept nothing.  (Every other test in this module is
    /// the same statement said less loudly: they all run `check_decls`, which
    /// now validates first.)
    #[test]
    fn a_well_formed_declaration_passes_the_validator() {
        let ds: Vec<DeclC> = vec![defn("b", type0(), prop())];
        assert!(validate::validate_decls(validate::seen_new(), &ds).0);
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(e) => assert_eq!(e.consts.len(), 1),
            Err(_) => panic!("a well-formed definition is an accept"),
        }
    }

    /// Task #73: a declaration carrying a node whose stored `data` word does
    /// not match its children is declined with `CheckError::Native` — the
    /// port's own failure, which claims nothing about con-leche.  The fields
    /// are `pub`, so this is exactly the input `hds` used to assume away.
    #[test]
    fn a_forged_data_word_inside_a_declaration_is_declined() {
        let good = expr::mk_const(nm("b"), Vec::new());
        let forged = Expr(ptr::new(expr::ExprNode {
            data: expr::data(&good) ^ 1,
            kind: expr::ExprKind::Const(nm("b"), ptr::new(Vec::new())),
        }));
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", type0(), forged),
        ];
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(_) => panic!("a forged data word must be declined"),
            Err((e, pos)) => {
                match e {
                    CheckError::Native(_) => {}
                    _ => panic!("the decline is the port's own Native error"),
                }
                assert_eq!(pos, 0);
            }
        }
        // …and the very same stream with the honest node is an accept, so
        // the decline is the word and nothing else.
        let ok: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", type0(), expr::mk_const(nm("b"), Vec::new())),
        ];
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ok) {
            Ok(e) => assert_eq!(e.consts.len(), 2),
            Err(_) => panic!("the honest stream is an accept"),
        }
    }

    /// `def b : Type := Prop`, `def c : Type := b` — the separable install
    /// twice, the second reading the first through the prefix view.  Both
    /// phases accept and the environment holds the two constants in
    /// installation order (`Env.consts` is the cited list reversed, task #50).
    #[test]
    fn a_stream_of_definitions_is_accepted() {
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", type0(), expr::mk_const(nm("b"), Vec::new())),
        ];
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(e) => {
                let ns: Vec<Name> = env_names(&e);
                assert_eq!(ns.len(), 2);
                assert!(name::beq(&ns[0], &nm("b")));
                assert!(name::beq(&ns[1], &nm("c")));
            }
            Err(_) => panic!("the two definitions accept"),
        }
    }

    /// **Phase B is what catches a bad definition.**  `def c : Prop := Prop`
    /// is a type error the install never looks at — phase A annotates the
    /// value and pushes the constant — so the error surfaces in phase B,
    /// tagged with the declaration's FOLD POSITION, 1, and not with its
    /// index among the records.
    #[test]
    fn a_type_error_is_reported_at_its_fold_position() {
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", prop(), prop()),
        ];
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(_) => panic!("`Prop : Type` is not a proof of `Prop`"),
            Err(e) => {
                assert_eq!(e.1, 1);
                match e.0 {
                    CheckError::Invalid(_) => (),
                    _ => panic!("a type mismatch is a reject"),
                }
            }
        }
    }

    /// A duplicate declaration fails in **phase A**, at the fold position of
    /// the second one: `annot_constant_val_c`'s first guard, which reads the
    /// index the fold has built so far.
    #[test]
    fn phase_a_rejects_a_duplicate_at_its_fold_position() {
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", type0(), prop()),
            defn("c", type0(), prop()),
        ];
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(_) => panic!("`c` is declared twice"),
            Err(e) => {
                assert_eq!(e.1, 2);
                match e.0 {
                    CheckError::Invalid(_) => (),
                    _ => panic!("a duplicate is a reject"),
                }
            }
        }
    }

    /// **A theorem installs by statement**, and its proposition test is
    /// phase B's: `theorem t : Type := b` passes phase A — the header is
    /// annotated and the constant pushed with the raw value — and is
    /// rejected in phase B, at its fold position, because `Type` is not a
    /// proposition.  Nothing else rejects a well-formed header this late.
    #[test]
    fn a_theorem_is_installed_by_statement_and_checked_in_phase_b() {
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            DeclC::ThmDecl(cv("t", type0()), expr::mk_const(nm("b"), Vec::new())),
        ];
        let mut st = state_c::cstate_new();
        match installed::annot_decl_fold_from(
            &CheckMode::Verified,
            &no_pins(),
            &mut st,
            (0, fenv::mk_fenv(env::empty()), Vec::new()),
            &ds,
            0,
        ) {
            Err(_) => panic!("phase A installs a theorem by its statement"),
            Ok(p) => {
                assert_eq!(p.1.visible_below, 2);
                assert_eq!(p.2.len(), 2);
            }
        }
        match installed::check_decls(&CheckMode::Verified, &no_pins(), &ds) {
            Ok(_) => panic!("`Type` is not a proposition"),
            Err(e) => {
                assert_eq!(e.1, 1);
                match e.0 {
                    CheckError::Invalid(_) => (),
                    _ => panic!("a non-proposition statement is a reject"),
                }
            }
        }
    }

    /// **The pending records carry the fold position and the visibility
    /// bound**, which is what makes phase B's prefix view right: record `j`'s
    /// `vis` is the number of constants installed before its declaration, so
    /// a record never sees the constant it is about to justify, nor any
    /// later one.
    #[test]
    fn the_records_carry_the_position_and_the_bound() {
        let ds: Vec<DeclC> = vec![
            defn("b", type0(), prop()),
            defn("c", type0(), prop()),
            defn("d", type0(), prop()),
        ];
        let mut st = state_c::cstate_new();
        match installed::annot_decl_fold_from(
            &CheckMode::Verified,
            &no_pins(),
            &mut st,
            (0, fenv::mk_fenv(env::empty()), Vec::new()),
            &ds,
            0,
        ) {
            Err(_) => panic!("phase A accepts this stream"),
            Ok(p) => {
                assert_eq!(p.0, 3);
                assert_eq!(p.1.visible_below, 3);
                assert_eq!(p.2.len(), 3);
                assert_eq!(p.2[0].pos, 0);
                assert_eq!(p.2[0].vis, 0);
                assert_eq!(p.2[1].pos, 1);
                assert_eq!(p.2[1].vis, 1);
                assert_eq!(p.2[2].pos, 2);
                assert_eq!(p.2[2].vis, 2);
            }
        }
    }
}
