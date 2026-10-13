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
//! ## The pins are plain values
//!
//! Since con-leche's task #342 a binder carries no datum, so the pins are
//! hand-written through the builder (`basis_builder`) and compared with
//! `ConstantVal.matchesPin`, which is plain equality of name, level
//! parameters and type.  The two pins compared by exact `ConstantInfo`
//! equality — `eqA` and `natA` — are `kernel::basis_pins`' stubs.

use crate::kernel::basis_builder;
use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, ConstantVal};
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The pinned names (`StdAxioms.lean:38-69`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:33-34 propextName
/// The name `propext`.  Deviation (task #18's point 10): a pinned name is a
/// function that rebuilds its `Name`, because the Aeneas subset has no
/// module-initialization constant.
pub fn propext_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 7] = [112, 114, 111, 112, 101, 120, 116]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:36-37 choiceName
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:39-40 iffName
/// The name `Iff`.
pub fn iff_name() -> Name {
    name::mk_str(name::anonymous(), { const S: [u32; 3] = [73, 102, 102]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:42-43 iffIntroName
/// The name `Iff.intro`.
pub fn iff_intro_name() -> Name {
    name::mk_str(iff_name(), { const S: [u32; 5] = [105, 110, 116, 114, 111]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:45-46 iffRecName
/// The name `Iff.rec`.
pub fn iff_rec_name() -> Name {
    name::mk_str(iff_name(), { const S: [u32; 3] = [114, 101, 99]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:48-49 nonemptyName
/// The name `Nonempty`.
pub fn nonempty_name() -> Name {
    name::mk_str(
        name::anonymous(),
        { const S: [u32; 8] = [78, 111, 110, 101, 109, 112, 116, 121]; core_types::code_points(&S) },
    )
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:51-52 nonemptyIntroName
/// The name `Nonempty.intro`.
pub fn nonempty_intro_name() -> Name {
    name::mk_str(nonempty_name(), { const S: [u32; 5] = [105, 110, 116, 114, 111]; core_types::code_points(&S) })
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:54-55 nonemptyRecName
/// The name `Nonempty.rec`.
pub fn nonempty_rec_name() -> Name {
    name::mk_str(nonempty_name(), { const S: [u32; 3] = [114, 101, 99]; core_types::code_points(&S) })
}

// ---------------------------------------------------------------------------
// The pins (`StdAxioms.lean:93-166`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/StdAxioms.lean:93-95 iffA
/// `Iff (a b : Prop) : Prop`.
/// Deviation: `IndCaps`' `{}` is `env::ind_caps_default()`.
pub fn iff_a() -> ConstantInfo {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:97-105 iffIntroA
/// `Iff.intro (a b : Prop) (mp : a → b) (mpr : b → a) : Iff a b`.
pub fn iff_intro_a() -> ConstantInfo {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:107-112 iffRecIntro
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:114-124 iffRecA
/// `Iff.rec.{u} (a b : Prop) (motive : Iff a b → Sort u)`
/// `(intro : ∀ mp mpr, motive (Iff.intro a b mp mpr)) (t : Iff a b) :`
/// `motive t`.
pub fn iff_rec_a() -> ConstantInfo {
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

/// con-leche: none — the level list `[.succ .zero]` the pinned `Eq` carries
/// Lean writes it inline; a `Vec` literal needs a push (task #18's point 10).
pub fn one_level() -> Vec<Level> {
    let mut us: Vec<Level> = Vec::new();
    us.push(level::succ(level::zero()));
    us
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:126-133 propextA
/// `propext (a b : Prop) : Iff a b → Eq.{1} Prop a b`.
pub fn propext_a() -> ConstantVal {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:135-137 nonemptyA
/// `Nonempty.{u} (α : Sort u) : Prop`.
pub fn nonempty_a() -> ConstantInfo {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:139-145 nonemptyIntroA
/// `Nonempty.intro.{u} (α : Sort u) (val : α) : Nonempty α`.
pub fn nonempty_intro_a() -> ConstantInfo {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:147-159 nonemptyRecA
/// `Nonempty.rec.{u} (α : Sort u) (motive : Nonempty α → Prop)`
/// `(intro : ∀ val, motive (Nonempty.intro α val)) (t : Nonempty α) :`
/// `motive t`.  The motive sort is pinned to `Prop` (the cited guidance: a
/// pin that fixes a level is easier to consume than one that quantifies it).
pub fn nonempty_rec_a() -> ConstantInfo {
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

/// con-leche: ConLeche/Kernel/StdAxioms.lean:161-166 choiceA
/// `Classical.choice.{u} (α : Sort u) : Nonempty α → α`.
pub fn choice_a() -> ConstantVal {
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

#[cfg(test)]
mod tests {
    use crate::kernel::name;
    use crate::kernel::std_axioms;

    /// The pinned names: `Iff.intro` is a child of `Iff`.
    #[test]
    fn the_pinned_names() {
        assert!(name::beq(
            &std_axioms::iff_intro_name(),
            &name::mk_str(std_axioms::iff_name(), vec![105, 110, 116, 114, 111])
        ));
    }
}
