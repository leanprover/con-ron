//! `ConLeche/Kernel/StdAxioms.lean` — the two recognized standard axioms
//! (`propext`, `Classical.choice`), the prerequisite shapes they quantify
//! over, and the pin comparison every pinned shape is checked with.
//!
//! A stream may use `propext` and `Classical.choice`; both are true in the
//! set-theoretic model — `propext` by extensionality of propositions through
//! the stored `Iff` recursor, `Classical.choice` by global choice through the
//! stored `Nonempty` recursor — so the checker accepts exactly these two,
//! after pinning their types *and the shapes of the inductives they quantify
//! over* to the toolchain's.
//!
//! ## `matchesPin` is compared against the RAW pins, and that is exact
//!
//! con-leche writes the pins twice: the *raw* ones here (hand-written with
//! the builder, `basis_builder`), and the *annotated* ones `iffA`,
//! `iffIntroA`, `iffRecA`, `nonemptyA`, `nonemptyIntroA`, `nonemptyRecA`,
//! `propextA`, `choiceA`, computed from them at elaboration time by
//! `#annotate_basis`/`#annotate_pins`.  `stdAxiomOk` compares against the
//! annotated ones — and it compares with `ConstantVal.matchesPin`, whose type
//! test is `a.erasePw == b.erasePw`, i.e. **up to every binder's prop-ness
//! datum**.
//!
//! The annotation pass changes nothing else in a term without a `letE` node
//! (`annotateBody`, `Kernel/Core.lean:2746`: the `bvar`/`fvar`/`sort`/
//! `const`/`lit`/`app`/`proj` arms rebuild the node, the `lam`/`forallE` arms
//! recompute `pw`, and only the `letE` arm changes the shape — by zeta
//! reduction, and no pin here has a `letE`).  So
//!
//! ```text
//! matchesPin cv (annotate pin) = matchesPin cv pin
//! ```
//!
//! and the port compares against the **raw** pin, which it can write down,
//! instead of the annotated one, which is a generated table (task #22).  Each
//! raw-pin function therefore carries its annotated twin's citation too, and
//! this is the whole reason `std_axioms` needs no pin table.  The two pins
//! that are *not* consumed through `matchesPin` — `eqA` and `natA`, compared
//! by exact `ConstantInfo` equality — are `kernel::basis_pins`' stubs.
//!
//! ## What else is here
//!
//! `Expr.erasePw` is the specification of the comparison and
//! `Expr.erasePwEq` its executed lockstep form (`@[csimp]`): the spec
//! rebuilds both trees, which is `O(tree)` on the side that comes from the
//! stream and exhausts memory on a DAG-shared tower; the lockstep descent
//! stops at the first disagreement and is bounded by the *pin*'s size.  The
//! port implements both, as task #13's `@[csimp]` rule asks, and calls the
//! fast one.

use crate::kernel::basis_builder;
use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::basis_pins;
use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprKind};
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The pinned names (`StdAxioms.lean:38-69`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:38-39 propextName
/// The name `propext`.  Deviation (task #18's point 10): a pinned name is a
/// function that rebuilds its `Name`, because the Aeneas subset has no
/// module-initialization constant.
pub fn propext_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 7] = [112, 114, 111, 112, 101, 120, 116]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:41-42 choiceName
/// The name `Classical.choice`.
pub fn choice_name() -> Name {
    name::mk_str(
        name::mk_str(
            name::anonymous(),
            { const S: [u32; 9] = [67, 108, 97, 115, 115, 105, 99, 97, 108]; core_types::code_points(&S) },
        ),
        { const S: [u32; 6] = [99, 104, 111, 105, 99, 101]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:44-45 iffName
/// The name `Iff`.
pub fn iff_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 3] = [73, 102, 102]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:47-48 iffIntroName
/// The name `Iff.intro`.
pub fn iff_intro_name() -> Name {
    name::mk_str(iff_name(), { const S: [u32; 5] = [105, 110, 116, 114, 111]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:50-51 iffRecName
/// The name `Iff.rec`.
pub fn iff_rec_name() -> Name {
    name::mk_str(iff_name(), { const S: [u32; 3] = [114, 101, 99]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:53-54 nonemptyName
/// The name `Nonempty`.
pub fn nonempty_name() -> Name {
    name::mk_str(
        name::anonymous(),
        { const S: [u32; 8] = [78, 111, 110, 101, 109, 112, 116, 121]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:56-57 nonemptyIntroName
/// The name `Nonempty.intro`.
pub fn nonempty_intro_name() -> Name {
    name::mk_str(nonempty_name(), { const S: [u32; 5] = [105, 110, 116, 114, 111]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:59-60 nonemptyRecName
/// The name `Nonempty.rec`.
pub fn nonempty_rec_name() -> Name {
    name::mk_str(nonempty_name(), { const S: [u32; 3] = [114, 101, 99]; core_types::code_points(&S) })
}

// ---------------------------------------------------------------------------
// The pin comparison (`StdAxioms.lean:71-215`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:62-113 Expr.erasePw
/// Reset every binder's prop-ness datum to `.never`, leaving every other
/// field alone.  **The specification** of `matchesPin`'s type test; the
/// executed comparison is `erase_pw_eq` below (`@[csimp]`).  Ported, and
/// uncalled, so the provenance gate stays in step with its source.
pub fn erase_pw(e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Bvar(i) => expr::bvar(*i),
        ExprKind::Fvar(i, ty) => expr::fvar(*i, erase_pw(ty)),
        ExprKind::Sort(u) => expr::sort(level::dup(u)),
        ExprKind::Const(n, us) => expr::mk_const(name::dup(n), env::levels_copy(us)),
        ExprKind::App(f, a) => expr::app(erase_pw(f), erase_pw(a)),
        ExprKind::Lam(ty, b, _) => {
            expr::lam(erase_pw(ty), erase_pw(b), basis_builder::never_meta())
        }
        ExprKind::ForallE(ty, b, _) => {
            expr::forall_e(erase_pw(ty), erase_pw(b), basis_builder::never_meta())
        }
        ExprKind::LetE(ty, v, b) => expr::let_e(erase_pw(ty), erase_pw(v), erase_pw(b)),
        ExprKind::Lit(l) => expr::lit(expr::literal_dup(l)),
        ExprKind::Proj(s, i, sub) => expr::proj(name::dup(s), *i, erase_pw(sub)),
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:115-117 ConstantVal.matchesPin
/// Shape comparison for the pins: exact name, level parameters and counts,
/// type up to the `pw` datum.  **The specification** every proof about a pin
/// hit consumes; the executed one is `matches_pin_fast`.  Ported, and
/// uncalled, so the gate stays in step with its source.
pub fn matches_pin(cv: &ConstantVal, pin: &ConstantVal) -> bool {
    if name::beq(&cv.name, &pin.name) {
        if prop_when::names_beq(&cv.level_params, &pin.level_params) {
            expr::beq(&erase_pw(&cv.ty), &erase_pw(&pin.ty))
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-153 Expr.erasePwEq
/// `a.erasePw = b.erasePw`, decided by descending **both** terms together and
/// stopping at the first disagreement: wherever the two agree they have the
/// pin's shape, so the walk is bounded by the PIN's tree size however large
/// the stream side is.
pub fn erase_pw_eq(a: &Expr, b: &Expr) -> bool {
    match (&a.0.kind, &b.0.kind) {
        (ExprKind::Bvar(i), ExprKind::Bvar(j)) => *i == *j,
        (ExprKind::Fvar(i, t), ExprKind::Fvar(j, t2)) => {
            if *i == *j {
                erase_pw_eq(t, t2)
            } else {
                false
            }
        }
        (ExprKind::Sort(u), ExprKind::Sort(v)) => level::beq(u, v),
        (ExprKind::Const(n, us), ExprKind::Const(n2, us2)) => {
            if name::beq(n, n2) {
                expr::levels_beq(us, us2)
            } else {
                false
            }
        }
        (ExprKind::App(f, x), ExprKind::App(f2, x2)) => {
            if erase_pw_eq(f, f2) {
                erase_pw_eq(x, x2)
            } else {
                false
            }
        }
        (ExprKind::Lam(t, b, _), ExprKind::Lam(t2, b2, _)) => {
            if erase_pw_eq(t, t2) {
                erase_pw_eq(b, b2)
            } else {
                false
            }
        }
        (ExprKind::ForallE(t, b, _), ExprKind::ForallE(t2, b2, _)) => {
            if erase_pw_eq(t, t2) {
                erase_pw_eq(b, b2)
            } else {
                false
            }
        }
        (ExprKind::LetE(t, v, b), ExprKind::LetE(t2, v2, b2)) => {
            if erase_pw_eq(t, t2) {
                if erase_pw_eq(v, v2) {
                    erase_pw_eq(b, b2)
                } else {
                    false
                }
            } else {
                false
            }
        }
        (ExprKind::Lit(l), ExprKind::Lit(l2)) => expr::literal_beq(l, l2),
        (ExprKind::Proj(s, i, e), ExprKind::Proj(s2, j, e2)) => {
            if name::beq(s, s2) {
                if *i == *j {
                    erase_pw_eq(e, e2)
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:197-201 ConstantVal.matchesPinFast
/// con-leche: ConLeche/Kernel/StdAxioms.lean:203-206 ConstantVal.matchesPin_eq_matchesPinFast
/// `matchesPin` at the lockstep comparison: **the executed shape test**, and
/// the one every pin guard below calls.  The cited `@[csimp]` lemma is a
/// kernel-checked equation with `matches_pin`, so the refinement of the
/// specification is that equation.
pub fn matches_pin_fast(cv: &ConstantVal, pin: &ConstantVal) -> bool {
    if name::beq(&cv.name, &pin.name) {
        if prop_when::names_beq(&cv.level_params, &pin.level_params) {
            erase_pw_eq(&cv.ty, &pin.ty)
        } else {
            false
        }
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The raw pins (`StdAxioms.lean:217-298`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:208-210 iffRaw
/// con-leche: ConLeche/Kernel/StdAxioms.lean:299-305 _
/// `Iff (a b : Prop) : Prop`.  The second citation is the `#annotate_basis`
/// command that computes the *annotated* pin `iffA` the guard below compares
/// against; see the module note for why the raw one gives the same verdict.
/// Deviation: `IndCaps`' `{}` is `env::ind_caps_default()`.
pub fn iff_raw() -> ConstantInfo {
    ConstantInfo::IndInfo(
        ConstantVal {
            name: iff_name(),
            level_params: Vec::new(),
            ty: basis_builder::pi(
                basis_builder::prop(),
                basis_builder::pi(basis_builder::prop(), basis_builder::prop()),
            ),
        },
        env::ind_caps_default(),
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:212-220 iffIntroRaw
/// `Iff.intro (a b : Prop) (mp : a → b) (mpr : b → a) : Iff a b`.
pub fn iff_intro_raw() -> ConstantInfo {
    ConstantInfo::CtorInfo(
        ConstantVal {
            name: iff_intro_name(),
            level_params: Vec::new(),
            ty: basis_builder::pi(
                basis_builder::prop(),
                basis_builder::pi(
                    basis_builder::prop(),
                    basis_builder::pi(
                        basis_builder::pi(basis_builder::bv(1), basis_builder::bv(1)),
                        basis_builder::pi(
                            basis_builder::pi(basis_builder::bv(1), basis_builder::bv(3)),
                            basis_builder::ap2(
                                basis_builder::cnst(iff_name(), Vec::new()),
                                basis_builder::bv(3),
                                basis_builder::bv(2),
                            ),
                        ),
                    ),
                ),
            ),
        },
        2,
        2,
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:222-227 iffRecIntro
/// `Iff.rec`'s minor premise, in the `a`/`b`/`motive` binder context:
/// `∀ (mp : a → b) (mpr : b → a), motive (Iff.intro a b mp mpr)`.
pub fn iff_rec_intro() -> Expr {
    basis_builder::pi(
        basis_builder::pi(basis_builder::bv(2), basis_builder::bv(2)),
        basis_builder::pi(
            basis_builder::pi(basis_builder::bv(2), basis_builder::bv(4)),
            expr::app(
                basis_builder::bv(2),
                basis_builder::ap4(
                    basis_builder::cnst(iff_intro_name(), Vec::new()),
                    basis_builder::bv(4),
                    basis_builder::bv(3),
                    basis_builder::bv(1),
                    basis_builder::bv(0),
                ),
            ),
        ),
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:229-239 iffRecRaw
/// `Iff.rec.{u} (a b : Prop) (motive : Iff a b → Sort u)`
/// `(intro : ∀ mp mpr, motive (Iff.intro a b mp mpr)) (t : Iff a b) :`
/// `motive t`.
pub fn iff_rec_raw() -> ConstantInfo {
    let mut lps: Vec<Name> = Vec::new();
    lps.push(basis_builder::u_n());
    ConstantInfo::RecInfo(
        ConstantVal {
            name: iff_rec_name(),
            level_params: lps,
            ty: basis_builder::pi(
                basis_builder::prop(),
                basis_builder::pi(
                    basis_builder::prop(),
                    basis_builder::pi(
                        basis_builder::pi(
                            basis_builder::ap2(
                                basis_builder::cnst(iff_name(), Vec::new()),
                                basis_builder::bv(1),
                                basis_builder::bv(0),
                            ),
                            basis_builder::srt(basis_builder::u()),
                        ),
                        basis_builder::pi(
                            iff_rec_intro(),
                            basis_builder::pi(
                                basis_builder::ap2(
                                    basis_builder::cnst(iff_name(), Vec::new()),
                                    basis_builder::bv(3),
                                    basis_builder::bv(2),
                                ),
                                expr::app(basis_builder::bv(2), basis_builder::bv(0)),
                            ),
                        ),
                    ),
                ),
            ),
        },
        4,
        4,
        Vec::new(),
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:241-243 iffFamily
/// The raw `Iff` family, as an export carries it (dependency order).
pub fn iff_family() -> Vec<ConstantInfo> {
    let mut fam: Vec<ConstantInfo> = Vec::new();
    fam.push(iff_raw());
    fam.push(iff_intro_raw());
    fam.push(iff_rec_raw());
    fam
}

/// con-leche: none — the level list `[.succ .zero]` the pinned `Eq` carries
/// Lean writes it inline; a `Vec` literal needs a push (task #18's point 10).
pub fn one_level() -> Vec<Level> {
    let mut us: Vec<Level> = Vec::new();
    us.push(level::succ(level::zero()));
    us
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:245-252 propextRaw
/// con-leche: ConLeche/Kernel/StdAxioms.lean:307-310 _
/// `propext (a b : Prop) : Iff a b → Eq.{1} Prop a b`.  The second citation
/// is the `#annotate_pins` command computing `propextA` (see the module
/// note).
pub fn propext_raw() -> ConstantVal {
    ConstantVal {
        name: propext_name(),
        level_params: Vec::new(),
        ty: basis_builder::pi(
            basis_builder::prop(),
            basis_builder::pi(
                basis_builder::prop(),
                basis_builder::pi(
                    basis_builder::ap2(
                        basis_builder::cnst(iff_name(), Vec::new()),
                        basis_builder::bv(1),
                        basis_builder::bv(0),
                    ),
                    basis_builder::ap3(
                        basis_builder::cnst(basis_names::eq_name(), one_level()),
                        basis_builder::prop(),
                        basis_builder::bv(2),
                        basis_builder::bv(1),
                    ),
                ),
            ),
        ),
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:254-256 nonemptyRaw
/// `Nonempty.{u} (α : Sort u) : Prop`.
pub fn nonempty_raw() -> ConstantInfo {
    let mut lps: Vec<Name> = Vec::new();
    lps.push(basis_builder::u_n());
    ConstantInfo::IndInfo(
        ConstantVal {
            name: nonempty_name(),
            level_params: lps,
            ty: basis_builder::pi(
                basis_builder::srt(basis_builder::u()),
                basis_builder::prop(),
            ),
        },
        env::ind_caps_default(),
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:258-264 nonemptyIntroRaw
/// `Nonempty.intro.{u} (α : Sort u) (val : α) : Nonempty α`.
pub fn nonempty_intro_raw() -> ConstantInfo {
    let mut lps: Vec<Name> = Vec::new();
    lps.push(basis_builder::u_n());
    let mut us: Vec<Level> = Vec::new();
    us.push(basis_builder::u());
    ConstantInfo::CtorInfo(
        ConstantVal {
            name: nonempty_intro_name(),
            level_params: lps,
            ty: basis_builder::pi(
                basis_builder::srt(basis_builder::u()),
                basis_builder::pi(
                    basis_builder::bv(0),
                    expr::app(
                        basis_builder::cnst(nonempty_name(), us),
                        basis_builder::bv(1),
                    ),
                ),
            ),
        },
        1,
        1,
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:266-278 nonemptyRecRaw
/// `Nonempty.rec.{u} (α : Sort u) (motive : Nonempty α → Prop)`
/// `(intro : ∀ val, motive (Nonempty.intro α val)) (t : Nonempty α) :`
/// `motive t`.  The motive sort is pinned to `Prop` (the cited guidance: a
/// pin that fixes a level is easier to consume than one that quantifies it).
pub fn nonempty_rec_raw() -> ConstantInfo {
    let mut lps: Vec<Name> = Vec::new();
    lps.push(basis_builder::u_n());
    let mut us1: Vec<Level> = Vec::new();
    us1.push(basis_builder::u());
    let mut us2: Vec<Level> = Vec::new();
    us2.push(basis_builder::u());
    let mut us3: Vec<Level> = Vec::new();
    us3.push(basis_builder::u());
    ConstantInfo::RecInfo(
        ConstantVal {
            name: nonempty_rec_name(),
            level_params: lps,
            ty: basis_builder::pi(
                basis_builder::srt(basis_builder::u()),
                basis_builder::pi(
                    basis_builder::pi(
                        expr::app(
                            basis_builder::cnst(nonempty_name(), us1),
                            basis_builder::bv(0),
                        ),
                        basis_builder::prop(),
                    ),
                    basis_builder::pi(
                        basis_builder::pi(
                            basis_builder::bv(1),
                            expr::app(
                                basis_builder::bv(1),
                                basis_builder::ap2(
                                    basis_builder::cnst(nonempty_intro_name(), us2),
                                    basis_builder::bv(2),
                                    basis_builder::bv(0),
                                ),
                            ),
                        ),
                        basis_builder::pi(
                            expr::app(
                                basis_builder::cnst(nonempty_name(), us3),
                                basis_builder::bv(2),
                            ),
                            expr::app(basis_builder::bv(2), basis_builder::bv(0)),
                        ),
                    ),
                ),
            ),
        },
        3,
        3,
        Vec::new(),
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:280-282 nonemptyFamily
/// The raw `Nonempty` family.
pub fn nonempty_family() -> Vec<ConstantInfo> {
    let mut fam: Vec<ConstantInfo> = Vec::new();
    fam.push(nonempty_raw());
    fam.push(nonempty_intro_raw());
    fam.push(nonempty_rec_raw());
    fam
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:284-289 choiceRaw
/// `Classical.choice.{u} (α : Sort u) : Nonempty α → α`.
pub fn choice_raw() -> ConstantVal {
    let mut lps: Vec<Name> = Vec::new();
    lps.push(basis_builder::u_n());
    let mut us: Vec<Level> = Vec::new();
    us.push(basis_builder::u());
    ConstantVal {
        name: choice_name(),
        level_params: lps,
        ty: basis_builder::pi(
            basis_builder::srt(basis_builder::u()),
            basis_builder::pi(
                expr::app(
                    basis_builder::cnst(nonempty_name(), us),
                    basis_builder::bv(0),
                ),
                basis_builder::bv(1),
            ),
        ),
    }
}

// ---------------------------------------------------------------------------
// The install guard (`StdAxioms.lean:322-373`, `DeclCheck.lean:240-273`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Iff` type former against the pin.  Factored out of the guard's
/// `&&` cascade (task #3's pattern 9), so each `match` on a lookup ends
/// before the next one begins (task #14's borrow rule).
pub fn iff_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &iff_name()) {
        Some(ConstantInfo::IndInfo(cv_i, _)) => {
            matches_pin_fast(cv_i, &env::to_constant_val(&iff_raw()))
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Iff.intro` against the pin, at the pinned arity `2 2`.
pub fn iff_intro_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &iff_intro_name()) {
        Some(ConstantInfo::CtorInfo(cv_ii, n_p, n_f)) => {
            if *n_p == 2 {
                if *n_f == 2 {
                    matches_pin_fast(cv_ii, &env::to_constant_val(&iff_intro_raw()))
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Iff.rec` against the pin, at the pinned arity `4 4`.  Only its
/// *type* is used, never its reduction rules (the cited note).
pub fn iff_rec_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &iff_rec_name()) {
        Some(ConstantInfo::RecInfo(cv_ir, m_i, r_p, _)) => {
            if *m_i == 4 {
                if *r_p == 4 {
                    matches_pin_fast(cv_ir, &env::to_constant_val(&iff_rec_raw()))
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Nonempty` type former against the pin.
pub fn nonempty_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &nonempty_name()) {
        Some(ConstantInfo::IndInfo(cv_n, _)) => {
            matches_pin_fast(cv_n, &env::to_constant_val(&nonempty_raw()))
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Nonempty.intro` against the pin, at the pinned arity `1 1`.
pub fn nonempty_intro_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &nonempty_intro_name()) {
        Some(ConstantInfo::CtorInfo(cv_ni, n_p, n_f)) => {
            if *n_p == 1 {
                if *n_f == 1 {
                    matches_pin_fast(cv_ni, &env::to_constant_val(&nonempty_intro_raw()))
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// The stored `Nonempty.rec` against the pin, at the pinned arity `3 3`.
pub fn nonempty_rec_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &nonempty_rec_name()) {
        Some(ConstantInfo::RecInfo(cv_nr, m_i, r_p, _)) => {
            if *m_i == 3 {
                if *r_p == 3 {
                    matches_pin_fast(cv_nr, &env::to_constant_val(&nonempty_rec_raw()))
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:313-364 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// Is this checked axiom one of the two recognized standard axioms, over
/// standardly-shaped stored `Iff` / `Nonempty` families (and the pinned `Eq`
/// basis)?  A pure predicate, so `check_decl`'s `axiomDecl` arm stays a
/// single conditional.  All three of each family's constants are pinned, not
/// just the type: the verification has to *realize* the axiom, and nothing
/// turns an inhabitant of an opaque family into its fields except that
/// family's own recursor.
///
/// Deviation (task #18's point 3): the `Env` and `FEnv` twins are this one
/// function, and the pins compared against are the raw ones (module note).
pub fn std_axiom_ok(fe: &FEnv, cv_a: &ConstantVal) -> bool {
    if name::beq(&cv_a.name, &propext_name()) {
        if basis_pins::eq_basis_pinned(fe) {
            if iff_pinned(fe) {
                if iff_intro_pinned(fe) {
                    if iff_rec_pinned(fe) {
                        matches_pin_fast(cv_a, &propext_raw())
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else if name::beq(&cv_a.name, &choice_name()) {
        if nonempty_pinned(fe) {
            if nonempty_intro_pinned(fe) {
                if nonempty_rec_pinned(fe) {
                    matches_pin_fast(cv_a, &choice_raw())
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::basis_builder;
    use crate::kernel::basis_pins;
    use crate::kernel::env;
    use crate::kernel::env::{ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::kernel::fenv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::prop_when;
    use crate::kernel::std_axioms;
    use crate::kernel::trust_axioms;

    /// The lockstep comparison and the spec agree on every pair the pins
    /// produce, and both forgive exactly the binder prop-ness datum.  This is
    /// the module's whole justification for comparing against the *raw* pins
    /// rather than the generated annotated ones.
    #[test]
    fn erase_pw_eq_is_erase_pw_equality() {
        let pins: Vec<Expr> = vec![
            std_axioms::propext_raw().ty,
            std_axioms::choice_raw().ty,
            env::to_constant_val(&std_axioms::iff_raw()).ty,
            env::to_constant_val(&std_axioms::iff_intro_raw()).ty,
            env::to_constant_val(&std_axioms::iff_rec_raw()).ty,
            env::to_constant_val(&std_axioms::nonempty_raw()).ty,
            env::to_constant_val(&std_axioms::nonempty_intro_raw()).ty,
            env::to_constant_val(&std_axioms::nonempty_rec_raw()).ty,
            trust_axioms::reduce_op_raw(&trust_axioms::reduce_nat_name()).ty,
            trust_axioms::of_reduce_raw(&trust_axioms::of_reduce_bool_name()).ty,
        ];
        for a in pins.iter() {
            for b in pins.iter() {
                let spec = expr::beq(&std_axioms::erase_pw(a), &std_axioms::erase_pw(b));
                assert_eq!(
                    std_axioms::erase_pw_eq(a, b),
                    spec,
                    "the lockstep descent must answer what the spec answers"
                );
            }
        }
        // reflexive, and blind to a rewritten `pw`
        for a in pins.iter() {
            assert!(std_axioms::erase_pw_eq(a, a));
            let repw = rewrite_pw(a);
            assert!(std_axioms::erase_pw_eq(a, &repw));
            assert!(std_axioms::erase_pw_eq(&std_axioms::erase_pw(a), a));
        }
        // …but not to anything else: `Iff` and `Nonempty` do not match
        assert!(!std_axioms::erase_pw_eq(
            &env::to_constant_val(&std_axioms::iff_raw()).ty,
            &env::to_constant_val(&std_axioms::nonempty_raw()).ty
        ));
    }

    fn rewrite_pw(e: &Expr) -> Expr {
        let m = expr::binder_meta(prop_when::if_all_zero(Vec::new()));
        match &e.0.kind {
            expr::ExprKind::ForallE(t, b, _) => expr::forall_e(rewrite_pw(t), rewrite_pw(b), m),
            expr::ExprKind::Lam(t, b, _) => expr::lam(rewrite_pw(t), rewrite_pw(b), m),
            expr::ExprKind::App(f, a) => expr::app(rewrite_pw(f), rewrite_pw(a)),
            _ => expr::dup(e),
        }
    }

    /// The pinned names, the families' order, and the guards' arity tests:
    /// `stdAxiomOk` refuses a stored `Iff.intro` at the wrong arity even when
    /// its type is the pinned one, because the `some (.ctorInfo cvIi 2 2)`
    /// pattern is part of the pin.
    #[test]
    fn the_pinned_families_and_their_arities() {
        assert_eq!(std_axioms::iff_family().len(), 3);
        assert_eq!(std_axioms::nonempty_family().len(), 3);
        // `Iff.intro` and `Iff.rec` are children of `Iff`
        assert!(name::beq(
            &std_axioms::iff_intro_name(),
            &name::mk_str(std_axioms::iff_name(), vec![105, 110, 116, 114, 111])
        ));
        // the raw pins carry the parse placeholder on every binder
        let m = expr::binder_meta(prop_when::never());
        assert!(expr::binder_meta_beq(&basis_builder::never_meta(), &m));
        // the `Iff` guard: right type, wrong arity
        let cv_ii = env::to_constant_val(&std_axioms::iff_intro_raw());
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ConstantInfo::CtorInfo(env::constant_val_dup(&cv_ii), 1, 2));
        let fe_bad = fenv::mk_fenv(env::env_of(&consts));
        assert!(!std_axioms::iff_intro_pinned(&fe_bad));
        let mut consts2: Vec<ConstantInfo> = Vec::new();
        consts2.push(ConstantInfo::CtorInfo(env::constant_val_dup(&cv_ii), 2, 2));
        let fe_ok = fenv::mk_fenv(env::env_of(&consts2));
        assert!(std_axioms::iff_intro_pinned(&fe_ok));
        // …and the pinned `Eq` basis is not there, so `stdAxiomOk` still says
        // no (`basis_pins`' stub; task #22 supplies the table)
        assert!(!basis_pins::eq_basis_pinned(&fe_ok));
        let propext: ConstantVal = std_axioms::propext_raw();
        assert!(!std_axioms::std_axiom_ok(&fe_ok, &propext));
        // an unrelated name is never a standard axiom
        let other = ConstantVal {
            name: name::mk_str(name::anonymous(), vec![120]),
            level_params: Vec::new(),
            ty: expr::sort(level::zero()),
        };
        assert!(!std_axioms::std_axiom_ok(&fe_ok, &other));
    }
}
