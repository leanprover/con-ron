//! **The pinned basis, end to end** (task #27, DESIGN.md §5 P1.5).
//!
//! `Cached/Installed.lean` is not ported yet, so there is no stream to feed;
//! this is the shortest path that exercises the whole wiring the three P1.5
//! tasks now share:
//!
//! * `kernel::checker::check_basis_decl` — `checkDecl`'s `.basisDecl` arm,
//! * over `kernel::basis_tables::basis_decls_a` — `BasisKind.declsA`, task
//!   #22's generated table,
//! * through `install_basis_decl`'s duplicate guard and `fenv::push`,
//! * and back out through `kernel::basis_pins` — the two pins the checker
//!   compares as whole `ConstantInfo`s, over `env::constant_info_beq`.
//!
//! It is an integration test (`tests/`) rather than a `#[cfg(test)]` module
//! because it crosses five modules and belongs to none of them.

use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::basis_pins;
use con_ron_core::kernel::basis_tables;
use con_ron_core::kernel::checker;
use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{BasisKind, ConstantInfo, ConstantVal, IndCaps};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::fenv;
use con_ron_core::kernel::fenv::FEnv;
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

/// Install the six pinned blocks into an empty index, in `BasisA.lean`'s own
/// order (`Eq` first — the quotient block's guard requires it).
fn install_all() -> FEnv {
    let kinds = [
        BasisKind::EqK,
        BasisKind::NatK,
        BasisKind::PunitK,
        BasisKind::EmptyK,
        BasisKind::FalseK,
        BasisKind::QuotK,
    ];
    let mut fe: FEnv = fenv::mk_fenv(env::empty());
    for k in kinds.iter() {
        fe = match checker::check_basis_decl(fe, k) {
            Ok(fe2) => fe2,
            Err(_) => panic!("a pinned basis block must install"),
        };
    }
    fe
}

/// The six blocks install from empty, and every constant of every block is
/// then stored, under its own name and equal to the table's entry.
#[test]
fn the_six_pinned_blocks_install_from_empty() {
    let fe = install_all();
    let kinds = [
        BasisKind::EqK,
        BasisKind::NatK,
        BasisKind::PunitK,
        BasisKind::EmptyK,
        BasisKind::FalseK,
        BasisKind::QuotK,
    ];
    let mut total = 0usize;
    for k in kinds.iter() {
        let block: Vec<ConstantInfo> = basis_tables::basis_decls_a(k);
        assert!(!block.is_empty(), "a basis block is never empty");
        total += block.len();
        for ci in block.iter() {
            let n: Name = env::constant_info_name(ci);
            match fenv::find(&fe, &n) {
                Some(stored) => assert!(
                    env::constant_info_beq(stored, ci),
                    "the stored constant is the table's, unchanged"
                ),
                None => panic!("every constant of an installed block is stored"),
            }
        }
    }
    // 3 + 4 + 3 + 2 + 2 + 5 — `BasisKind.declsA`'s own block sizes
    assert_eq!(total, 19);
}

/// `False`, `Eq` and `Nat` are found by name after the install, and each is
/// stored under the kind the pin declares.
#[test]
fn false_eq_and_nat_are_found() {
    let fe = install_all();
    match fenv::find(&fe, &basis_names::false_name()) {
        Some(ConstantInfo::IndInfo(cv, _)) => {
            assert!(name::beq(&cv.name, &basis_names::false_name()));
            assert!(cv.level_params.is_empty(), "`False` has no level parameter");
        }
        _ => panic!("`False` must be stored as an inductive type former"),
    }
    match fenv::find(&fe, &basis_names::eq_name()) {
        Some(ConstantInfo::IndInfo(cv, caps)) => {
            assert_eq!(cv.level_params.len(), 1, "`Eq` has one level parameter");
            assert!(caps.rule_k, "the pinned `Eq` carries rule K");
        }
        _ => panic!("`Eq` must be stored as an inductive type former"),
    }
    match fenv::find(&fe, &basis_names::nat_name()) {
        Some(ConstantInfo::IndInfo(cv, _)) => {
            assert!(cv.level_params.is_empty(), "`Nat` has no level parameter");
        }
        _ => panic!("`Nat` must be stored as an inductive type former"),
    }
    // and a name that was never installed is not found
    let bogus = name::mk_str(name::anonymous(), vec![90, 122]);
    assert!(fenv::find(&fe, &bogus).is_none());
}

/// **The pinned-`Eq` predicate on the real store**: true on the constant the
/// install left behind, and false on a perturbed copy of it — here the same
/// `ConstantVal` with the `ruleK` capability dropped, which
/// `ConstantVal.matchesPin` would not even see.
#[test]
fn the_pinned_eq_predicate_reads_the_installed_constant() {
    let fe = install_all();
    let stored: &ConstantInfo = match fenv::find(&fe, &basis_names::eq_name()) {
        Some(ci) => ci,
        None => panic!("`Eq` must be stored"),
    };
    assert!(basis_pins::is_pinned_eq_basis(stored));
    assert!(basis_pins::eq_basis_pinned(&fe));
    assert!(basis_pins::nat_basis_pinned(&fe));

    let perturbed: ConstantInfo = match stored {
        ConstantInfo::IndInfo(cv, caps) => {
            let mut c2: IndCaps = env::ind_caps_dup(caps);
            c2.rule_k = false;
            ConstantInfo::IndInfo(env::constant_val_dup(cv), c2)
        }
        _ => panic!("`Eq` is an `indInfo`"),
    };
    assert!(!basis_pins::is_pinned_eq_basis(&perturbed));

    // and so is one whose type differs by a single node
    let perturbed2: ConstantInfo = match stored {
        ConstantInfo::IndInfo(cv, caps) => ConstantInfo::IndInfo(
            ConstantVal {
                name: name::dup(&cv.name),
                level_params: Vec::new(),
                ty: expr::dup(&cv.ty),
            },
            env::ind_caps_dup(caps),
        ),
        _ => panic!("`Eq` is an `indInfo`"),
    };
    assert!(!basis_pins::is_pinned_eq_basis(&perturbed2));

    // an environment holding the perturbed `Eq` fails the guard, so the
    // quotient block declines rather than installing (DESIGN.md §1)
    let mut consts: Vec<ConstantInfo> = Vec::new();
    consts.push(perturbed);
    let fe_bad: FEnv = fenv::mk_fenv(env::env_of(&consts));
    assert!(!basis_pins::eq_basis_pinned(&fe_bad));
    assert!(checker::check_basis_decl(fe_bad, &BasisKind::QuotK).is_err());
}

/// Installing the same block twice is `installBasisDecl`'s duplicate
/// rejection, not a second copy.
#[test]
fn a_second_install_of_a_block_is_rejected() {
    let fe = install_all();
    assert!(checker::check_basis_decl(fe, &BasisKind::EqK).is_err());
}
