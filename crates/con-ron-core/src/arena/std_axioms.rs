//! `arena::std_axioms` — the recognized standard axioms, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/StdAxioms.lean`, which is con-leche's
//! `Kernel/StdAxioms.lean`: the eight reserved names, the shape comparison a
//! pin hit is decided by, and the pinned `Iff` / `Nonempty` families with
//! `propext` and `Classical.choice`.
//!
//! Three deviations, each of them one of DESIGN.md §8's own rules:
//!
//! 1. **The pins are values, interned** (`arena::intern`'s module note).  The
//!    Lean twin interns con-leche's `iffRaw`, `propextRaw`, … ; the Rust
//!    interns `con_ron_core::kernel::std_axioms`' own, which are the same
//!    values ported at task #18.  Each twin is one line.
//! 2. **`erasePw` and `erasePwEq` collapse into one twin**, as `arena::canon`'s
//!    comparisons do: con-leche carries the rebuild as the specification and
//!    the lockstep descent as the executed `@[csimp]` twin, and the arena
//!    writes the executed one.
//! 3. **`stdAxiomOk` is `arena::decl_check`'s**, which cites both halves of
//!    con-leche's `Env`/`FEnv` pair.
//!
//! ## The annotated pins are the raw ones, and that is con-ron-core's ruling
//!
//! The Lean twin compares a stored `Iff` family against `iffA`/`iffIntroA`/
//! `iffRecA` and `propextA`/`choiceA` — the pins `#annotate_basis` computes
//! while con-leche elaborates.  `con-ron-core` has no elaborator and therefore
//! no such values, and it does not need them: the comparison is
//! `matchesPin`, which **erases the binder `pw` datum on both sides**, and the
//! `pw` datum is the only thing annotation writes.  So `matchesPin cv iffRaw`
//! and `matchesPin cv iffA` are the same predicate, and this module carries
//! the raw pins only — `con_ron_core::kernel::std_axioms`' own choice, its
//! module note's argument, and what makes the differential test against that
//! crate exact.  The one pin compared by *equality* rather than by `matchesPin`
//! is the annotated `Eq` basis, and that one `con-ron-core` does have
//! (`kernel::basis_pins::eq_a`, generated at task #22).

use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env::{IConstantInfo, IConstantVal};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::intern::{intern_ci, intern_ci_list, intern_cv, intern_expr};
use crate::arena::monad::{fail, view, AState};
use crate::arena::store::ENodeView;
use crate::kernel::basis_pins;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr;
use crate::kernel::std_axioms as cstd;
use crate::ron::hashmap::Eq2;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The message of this module's one decline
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: erasePwEq"`, as code points.
pub const M_FUEL_ERASE_PW: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 101, 114,
    97, 115, 101, 80, 119, 69, 113
];

// ---------------------------------------------------------------------------
// The reserved names, interned (`StdAxioms.lean:34-51` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:38-39 propextName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:36-37 propextName`.
pub fn propext_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_propext(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:41-42 choiceName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:38-39 choiceName`.
pub fn choice_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_choice(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:44-45 iffName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:40-41 iffName`.
pub fn iff_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:47-48 iffIntroName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:42-43 iffIntroName`.
pub fn iff_intro_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff_intro(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:50-51 iffRecName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:44-45 iffRecName`.
pub fn iff_rec_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_iff_rec(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:53-54 nonemptyName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:46-47 nonemptyName`.
pub fn nonempty_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:56-57 nonemptyIntroName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:48-49 nonemptyIntroName`.
pub fn nonempty_intro_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty_intro(st)
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:59-60 nonemptyRecName
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:50-51 nonemptyRecName`.
pub fn nonempty_rec_name(st: &mut AState) -> Result<NIdx, CheckError> {
    crate::arena::pins::pin_nonempty_rec(st)
}

// ---------------------------------------------------------------------------
// The shape comparison (`StdAxioms.lean:53-99` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:62-113 Expr.erasePw
/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:55-88 erasePwEq` —
/// `a.erasePw = b.erasePw`, decided in lockstep on two handles.  `erasePw`
/// preserves every node's constructor and its non-recursive fields (it only
/// resets the binder `pw` datum), so two erased terms are equal iff the
/// originals agree constructor by constructor down to their leaves.  The `pw`
/// datum is the one thing not compared, which is exactly what the erasure
/// forgives.
pub fn erase_pw_eq(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ERASE_PW)))
    } else {
        match view(pers, st, a) {
            Err(e) => Err(e),
            Ok(va) => match view(pers, st, b) {
                Err(e) => Err(e),
                Ok(vb) => erase_pw_eq_at(pers, st, fuel - 1, va, vb),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:55-88 erasePwEq` — the ten
/// arms, past the two views.
pub fn erase_pw_eq_at(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    va: ENodeView,
    vb: ENodeView,
) -> Result<bool, CheckError> {
    match (va, vb) {
        (ENodeView::BVar(i), ENodeView::BVar(j)) => Ok(i == j),
        (ENodeView::FVar(i, t), ENodeView::FVar(j, t2)) => {
            if i == j {
                erase_pw_eq(pers, st, fuel, &t, &t2)
            } else {
                Ok(false)
            }
        }
        (ENodeView::Sort(u), ENodeView::Sort(v)) => Ok(u.eq2(&v)),
        (ENodeView::Const(n, us), ENodeView::Const(n2, us2)) => {
            Ok(n.eq2(&n2) && us.eq2(&us2))
        }
        (ENodeView::App(f, x), ENodeView::App(f2, x2)) => {
            erase_pw_eq_two(pers, st, fuel, &f, &f2, &x, &x2)
        }
        (ENodeView::Lam(t, bd, _), ENodeView::Lam(t2, bd2, _)) => {
            erase_pw_eq_two(pers, st, fuel, &t, &t2, &bd, &bd2)
        }
        (ENodeView::ForallE(t, bd, _), ENodeView::ForallE(t2, bd2, _)) => {
            erase_pw_eq_two(pers, st, fuel, &t, &t2, &bd, &bd2)
        }
        (ENodeView::LetE(t, v, bd), ENodeView::LetE(t2, v2, bd2)) => {
            match erase_pw_eq(pers, st, fuel, &t, &t2) {
                Err(e) => Err(e),
                Ok(r) => {
                    if r {
                        erase_pw_eq_two(pers, st, fuel, &v, &v2, &bd, &bd2)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        (ENodeView::Lit(l), ENodeView::Lit(l2)) => Ok(expr::literal_beq(&l, &l2)),
        (ENodeView::Proj(s, i, e), ENodeView::Proj(s2, i2, e2)) => {
            if s.eq2(&s2) && i == i2 {
                erase_pw_eq(pers, st, fuel, &e, &e2)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:55-88 erasePwEq` — the twin's
/// `if ← erasePwEq … then erasePwEq … else pure false`, which four of its arms
/// spell identically (`arena::canon::canon_expr_eq_two`'s reason).
pub fn erase_pw_eq_two(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    a: &EIdx,
    a2: &EIdx,
    b: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match erase_pw_eq(pers, st, fuel, a, a2) {
        Err(e) => Err(e),
        Ok(r) => {
            if r {
                erase_pw_eq(pers, st, fuel, b, b2)
            } else {
                Ok(false)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:115-117 ConstantVal.matchesPin
/// con-leche: ConLeche/Kernel/StdAxioms.lean:197-201 ConstantVal.matchesPinFast
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:90-99 IConstantVal.matchesPin`
/// — shape comparison for the standard pins: exact name, level parameters and
/// counts, type up to the `pw` datum.  A name comparison is a handle
/// comparison (DESIGN.md §8.3: `denoteN` is injective, so index inequality IS
/// structural inequality).
pub fn i_constant_val_matches_pin(
    pers: &PersTier,
    st: &AState,
    cv: &IConstantVal,
    pin: &IConstantVal,
) -> Result<bool, CheckError> {
    if cv.name.eq2(&pin.name)
        && crate::arena::canon::nidx_vec_beq(&cv.level_params, &pin.level_params, 0)
    {
        erase_pw_eq(pers, st, CORE_WALK_FUEL, &cv.ty, &pin.ty)
    } else {
        Ok(false)
    }
}

// ---------------------------------------------------------------------------
// The pins (`StdAxioms.lean:101-158` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:208-210 iffRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:108-109 iffRaw`.
pub fn iff_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:212-220 iffIntroRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:110-111 iffIntroRaw`.
pub fn iff_intro_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_intro_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:222-227 iffRecIntro
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:112-113 iffRecIntro`.
pub fn iff_rec_intro(pers: &PersTier, st: &mut AState) -> Result<EIdx, CheckError> {
    intern_expr(pers, st, &cstd::iff_rec_intro())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:229-239 iffRecRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:114-115 iffRecRaw`.
pub fn iff_rec_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::iff_rec_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:241-243 iffFamily
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:116-117 iffFamily`.
pub fn iff_family(pers: &PersTier, st: &mut AState) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &cstd::iff_family())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:245-252 propextRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:118-119 propextRaw`.
pub fn propext_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &cstd::propext_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:254-256 nonemptyRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:120-121 nonemptyRaw`.
pub fn nonempty_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:258-264 nonemptyIntroRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:122-123 nonemptyIntroRaw`.
pub fn nonempty_intro_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_intro_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:266-278 nonemptyRecRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:124-125 nonemptyRecRaw`.
pub fn nonempty_rec_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &cstd::nonempty_rec_raw())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:280-282 nonemptyFamily
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:126-128 nonemptyFamily`.
pub fn nonempty_family(pers: &PersTier, st: &mut AState) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &cstd::nonempty_family())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:284-289 choiceRaw
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:129-130 choiceRaw`.
pub fn choice_raw(pers: &PersTier, st: &mut AState) -> Result<IConstantVal, CheckError> {
    intern_cv(pers, st, &cstd::choice_raw())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-49 _
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:132-136 eqA` — the ANNOTATED `Eq`
/// pin, interned.  It is the comparand of every "requires the pinned `Eq`
/// basis" test in the checker, and the one pin compared by whole-constant
/// EQUALITY rather than by `matchesPin` (the module note).
pub fn eq_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &basis_pins::eq_a())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-49 _
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:138-140 natA` — the ANNOTATED
/// `Nat` pin, interned.
pub fn nat_a(pers: &PersTier, st: &mut AState) -> Result<IConstantInfo, CheckError> {
    intern_ci(pers, st, &basis_pins::nat_a())
}
