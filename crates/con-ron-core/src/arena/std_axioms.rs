//! `arena::std_axioms` — the recognized standard axioms, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/StdAxioms.lean`, which is con-leche's
//! `Kernel/StdAxioms.lean`: the eight reserved names, the shape comparison a
//! pin hit is decided by, and the pinned `Iff` / `Nonempty` families with
//! `propext` and `Classical.choice`.
//!
//! Two deviations, each of them one of DESIGN.md §8's own rules:
//!
//! 1. **The pins are values, interned** (`arena::intern`'s module note).  The
//!    Lean twin interns con-leche's `iffA`, `propextA`, … ; the Rust interns
//!    `con_ron_core::kernel::std_axioms`' own, which are the same values
//!    ported at task #18.  Each twin is one line.
//! 2. **`stdAxiomOk` is `arena::decl_check`'s**, which cites both halves of
//!    con-leche's `Env`/`FEnv` pair.
//!
//! Since con-leche's task #342 the comparison `matchesPin` is plain equality
//! (no binder datum is left to forgive), and over handles it is handle
//! equality: interning is injective (DESIGN.md §8.3), so index equality IS
//! structural equality.  (Task #119: the lockstep `erasePwEq` descent is
//! gone with the datum.)

use crate::arena::env::{IConstantInfo, IConstantVal};
use crate::arena::handle::NIdx;
use crate::arena::intern::{intern_ci, intern_cv};
use crate::arena::monad::AState;
use crate::kernel::basis_pins;
use crate::kernel::core_types::CheckError;
use crate::kernel::std_axioms as cstd;
use crate::ron::hashmap::Eq2;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The message of this module's one decline
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The reserved names, interned (`StdAxioms.lean:34-51` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:33-34 propextName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:36-37 propextName`.
pub fn propext_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_propext(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:36-37 choiceName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:38-39 choiceName`.
pub fn choice_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_choice(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:39-40 iffName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:40-41 iffName`.
pub fn iff_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:42-43 iffIntroName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:42-43 iffIntroName`.
pub fn iff_intro_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff_intro(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:45-46 iffRecName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:44-45 iffRecName`.
pub fn iff_rec_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff_rec(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:48-49 nonemptyName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:46-47 nonemptyName`.
pub fn nonempty_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:51-52 nonemptyIntroName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:48-49 nonemptyIntroName`.
pub fn nonempty_intro_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty_intro(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:54-55 nonemptyRecName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:50-51 nonemptyRecName`.
pub fn nonempty_rec_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty_rec(st)
}

// ---------------------------------------------------------------------------
// The shape comparison (`StdAxioms.lean:52-59` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:57-91 ConstantVal.matchesPin
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:50-59 IConstantVal.matchesPin`
/// — shape comparison for the standard pins: exact name, level parameters and
/// type.  Since con-leche's task #342 this is plain equality, and over handles
/// handle equality (the module note).
pub fn i_constant_val_matches_pin(
    cv: &IConstantVal,
    pin: &IConstantVal,
) -> bool {
    cv.name.eq2(&pin.name)
        && crate::arena::canon::nidx_vec_beq(&cv.level_params, &pin.level_params, 0)
        && cv.ty.eq2(&pin.ty)
}

// ---------------------------------------------------------------------------
// The pins (`StdAxioms.lean:61-91` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:93-95 iffA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:66-67 iffA`.
pub fn iff_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:97-105 iffIntroA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:68-69 iffIntroA`.
pub fn iff_intro_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_intro_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:114-124 iffRecA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:70-71 iffRecA`.
pub fn iff_rec_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_rec_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:126-133 propextA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:72-73 propextA`.
pub fn propext_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &cstd::propext_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:135-137 nonemptyA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:74-75 nonemptyA`.
pub fn nonempty_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-145 nonemptyIntroA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:76-77 nonemptyIntroA`.
pub fn nonempty_intro_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_intro_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:147-159 nonemptyRecA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:78-79 nonemptyRecA`.
pub fn nonempty_rec_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_rec_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:161-166 choiceA
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:80-81 choiceA`.
pub fn choice_a(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &cstd::choice_a())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:30-46 _
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:83-87 eqA` — the stored `Eq`
/// pin, interned.  It is the comparand of every "requires the pinned `Eq`
/// basis" test in the checker, compared by whole-constant equality.
pub fn eq_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &basis_pins::eq_a())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:30-46 _
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:89-91 natA` — the stored
/// `Nat` pin, interned.
pub fn nat_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &basis_pins::nat_a())
}
