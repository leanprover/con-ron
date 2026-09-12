//! `ConLeche/Kernel/BasisA.lean`'s **two exactly-compared pins**, over task
//! #22's generated table.
//!
//! `BasisA.lean` holds the annotated pinned basis blocks — `eqA`, `natA`,
//! `punitA`, …, `quotSoundA` and `BasisKind.declsA` — and it does not *write*
//! them: they are computed from the raw pins (`ConLeche/Kernel/Basis/*`) by
//! the checker's own annotation pass while the module elaborates
//! (`#annotate_basis`, `ConLeche/Kernel/BasisGen.lean`).  The *values* are
//! therefore carried as generated source in
//! `crate::kernel::basis_tables` (task #22), and `BasisKind.declsA` is
//! `basis_tables::basis_decls_a`, which is what `checkDecl`'s `.basisDecl`
//! arm folds `installBasisDecl` over.
//!
//! ## What is left for this module
//!
//! Two of the nineteen annotated pins are consumed by an **exact
//! `ConstantInfo` comparison** rather than through
//! `ConstantVal.matchesPin`: `env.find? eqName = some eqA`
//! (`Kernel/StdAxioms.lean:346`, `Kernel/TrustAxioms.lean:193`,
//! `Kernel/Checker.lean:284,528`, `Kernel/DeclCheck.lean:243,299,313,744`,
//! `Kernel/Inductives/Modeled.lean:448,493,603,653`,
//! `Cached/CheckerC.lean:143`, `Cached/ParsedC.lean:228`) and
//! `env.find? natName = some natA` (`Kernel/TrustAxioms.lean:180`,
//! `Kernel/DeclCheck.lean:290`).  `matchesPin` erases every binder's
//! prop-ness datum (`Expr.erasePw`), which is the *only* thing annotation
//! changes in a raw pin, so every other pin is compared against its raw form
//! in `std_axioms`/`trust_axioms` with no table at all (those modules'
//! notes).  These two are not: they read the stored capabilities
//! (`IndCaps`, `ruleK := true` on `Eq`) and the whole constant, so they need
//! the annotated value and the derived `DecidableEq` of
//! `Kernel/Env.lean` — which is `env::constant_info_beq`.
//!
//! The comparison con-leche uses is the derived structural one.  A grep of
//! the implementation tree settles it: every site above spells `==` or
//! `decide (… = some …)` on `ConstantInfo`, and `ConstantInfo.canonEq`
//! (`Frontend/Export.lean:279`, which canonicalises level-parameter *names*)
//! is used by the frontend alone and never by the kernel.
//!
//! Each pin is the **first** constant of its annotated block, which is the
//! install order `BasisKind.declsA` fixes (`.eqK => [eqA, eqReflA, eqRecA]`,
//! `.natK => [natA, natZeroA, natSuccA, natRecA]`).  Reading it off the
//! generated table rather than spelling it a second time is what makes a
//! change upstream a *test* failure (`basis_tables`' regeneration) instead
//! of a silent verdict change.

use crate::kernel::basis_names;
use crate::kernel::basis_tables;
use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// con-leche: ConLeche/Kernel/Basis/Eq.lean:22-28 eqRaw
/// The pinned annotated `Eq` type former, `eqA` — the head of the `.eqK`
/// block (`BasisKind.declsA .eqK = [eqA, eqReflA, eqRecA]`).
///
/// (`eqA` has no `def` line to cite: it is one entry of the
/// `#annotate_basis over []` command the first citation's range covers, so
/// that citation names no declaration.)
///
/// **`eqA = eqRaw`, and that is a fact, not an assumption** — which is why
/// the raw pin is cited here too.  `eqA` is `#annotate_basis`'s output, i.e.
/// `annotateCore .verified` applied to `eqRaw`'s type, and every binder of
/// `∀ {α : Sort u} (a b : α), Prop` has a codomain that is a `Sort` or a `∀`
/// whose datum is already `.never`, so `annotPwPi`'s head-symbol reader
/// answers `.never` at all three — the parse placeholder the raw pin
/// carries.  The test `eq_a_is_annotated` runs the port's own annotation pass
/// on the table's value and compares, so a change upstream breaks a test
/// rather than a verdict.
pub fn eq_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_eq();
    env::constant_info_dup(&block[0])
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// The pinned annotated `Nat` type former, `natA` — the head of the `.natK`
/// block (`BasisKind.declsA .natK = [natA, natZeroA, natSuccA, natRecA]`).
pub fn nat_a() -> ConstantInfo {
    let block: Vec<ConstantInfo> = basis_tables::basis_decls_nat();
    env::constant_info_dup(&block[0])
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Eq` type former?  This is
/// the `some ci = some eqA` half of `env.find? eqName = some eqA`, i.e. the
/// derived `DecidableEq (ConstantInfo)` against the table's pin.
pub fn is_pinned_eq_basis(ci: &ConstantInfo) -> bool {
    env::constant_info_beq(ci, &eq_a())
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Is the stored constant *the* pinned annotated `Nat` type former
/// (`env.find? natName = some natA`, `reduceElemOk`)?
pub fn is_pinned_nat_basis(ci: &ConstantInfo) -> bool {
    env::constant_info_beq(ci, &nat_a())
}

/// con-leche: ConLeche/Kernel/StdAxioms.lean:322-373 stdAxiomOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:240-270 stdAxiomOkF
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:435-455 checkIndRecs
/// con-leche: ConLeche/Kernel/Inductives/Modeled.lean:475-495 checkProjLookups
/// **"The pinned `Eq` basis is installed, unmodified"** — the whole guard
/// `decide (env.find? eqName = some eqA)`, through the index.  Twelve sites
/// spell it (the module note lists them); two of those are in a pure `Bool`,
/// so a monadic "run the annotation pass now" is not available and the
/// comparison has to be against a value the core can write down.
pub fn eq_basis_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::eq_name()) {
        Some(ci) => is_pinned_eq_basis(ci),
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/TrustAxioms.lean:177-184 reduceElemOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:288-294 reduceElemOkF
/// The same for `Nat`: `decide (env.find? natName = some natA)`, the element
/// inductive an `ofReduceNat` axiom needs.
pub fn nat_basis_pinned(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::nat_name()) {
        Some(ci) => is_pinned_nat_basis(ci),
        None => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cached::core_c;
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::core_k;
    use crate::kernel::env::{CheckMode, ConstantVal, Env, IndCaps};
    use crate::kernel::expr;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;

    /// **`eqA` really is `eqRaw`**: running the checker's own annotation pass
    /// on the pin's type over the empty environment reproduces it, which is
    /// what `#annotate_basis` computes
    /// (`ConLeche/Kernel/BasisGen.lean`).  Every binder of
    /// `∀ {α : Sort u} (a b : α), Prop` has a codomain that is a `Sort` or a
    /// `∀` whose datum is already `.never`, so `annotPwPi`'s head-symbol
    /// reader answers `.never` at all three — the parse placeholder the raw
    /// pin carries.  (Task #25's test, moved here with the pin.)
    #[test]
    fn eq_a_is_annotated() {
        let fe: FEnv = fenv::mk_fenv(Env { consts: Vec::new() });
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let pin = eq_a();
        let ty = env::constant_info_type(&pin);
        match core_c::annotate(&mode, core_k::check_fuel(), &mut st, &fe, 0, &ty) {
            Ok(a) => assert!(
                expr::beq(&a, &ty),
                "the annotation pass must be the identity on the Eq pin"
            ),
            Err(_) => panic!("annotating the Eq pin failed"),
        }
    }

    /// The pin is the head of the `.eqK` block, and the table's dispatcher
    /// agrees with the block function.
    #[test]
    fn eq_a_heads_the_eq_block() {
        let block = basis_tables::basis_decls_eq();
        assert_eq!(block.len(), 3);
        assert!(env::constant_info_beq(&eq_a(), &block[0]));
        assert!(name::beq(
            &env::constant_info_name(&eq_a()),
            &basis_names::eq_name()
        ));
        let nat = basis_tables::basis_decls_nat();
        assert_eq!(nat.len(), 4);
        assert!(env::constant_info_beq(&nat_a(), &nat[0]));
        assert!(name::beq(
            &env::constant_info_name(&nat_a()),
            &basis_names::nat_name()
        ));
        // the two pins are not each other
        assert!(!is_pinned_eq_basis(&nat_a()));
        assert!(!is_pinned_nat_basis(&eq_a()));
    }

    /// `eq_basis_pinned` accepts the pin and rejects a perturbed copy — the
    /// `Eq` type former stored *without* the `ruleK` capability is not the
    /// pin, even though its `ConstantVal` is identical.  (Task #25's test,
    /// moved here with the pin.)
    #[test]
    fn eq_basis_pinned_reads_the_store() {
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(eq_a());
        let fe: FEnv = fenv::mk_fenv(Env { consts });
        assert!(eq_basis_pinned(&fe));
        let mut consts2: Vec<ConstantInfo> = Vec::new();
        let ty = env::constant_info_type(&eq_a());
        let mut l: Vec<Name> = Vec::new();
        l.push(name::mk_str(name::anonymous(), vec![117]));
        let caps: IndCaps = env::ind_caps_default();
        consts2.push(ConstantInfo::IndInfo(
            ConstantVal {
                name: basis_names::eq_name(),
                level_params: l,
                ty,
            },
            caps,
        ));
        let fe2: FEnv = fenv::mk_fenv(Env { consts: consts2 });
        assert!(!eq_basis_pinned(&fe2));
        // and an empty environment has no pin
        let fe3: FEnv = fenv::mk_fenv(Env { consts: Vec::new() });
        assert!(!eq_basis_pinned(&fe3));
        assert!(!nat_basis_pinned(&fe3));
    }

    /// The derived equality is componentwise and blind to nothing: a
    /// rewritten binder datum, a dropped level parameter and a changed
    /// capability each make the stored constant not the pin.
    #[test]
    fn constant_info_beq_is_the_derived_one() {
        let pin = eq_a();
        assert!(env::constant_info_beq(&pin, &eq_a()));
        match &pin {
            ConstantInfo::IndInfo(cv, caps) => {
                // same value, one capability flipped
                let mut c2: IndCaps = env::ind_caps_dup(caps);
                c2.unitlike = !c2.unitlike;
                let ci2 = ConstantInfo::IndInfo(env::constant_val_dup(cv), c2);
                assert!(!env::constant_info_beq(&pin, &ci2));
                // same value, no level parameter
                let ci3 = ConstantInfo::IndInfo(
                    ConstantVal {
                        name: name::dup(&cv.name),
                        level_params: Vec::new(),
                        ty: expr::dup(&cv.ty),
                    },
                    env::ind_caps_dup(caps),
                );
                assert!(!env::constant_info_beq(&pin, &ci3));
                // same value, a rewritten binder datum (what `matchesPin`
                // erases and this comparison does not)
                let mut ns: Vec<Name> = Vec::new();
                ns.push(name::dup(&cv.name));
                let ty2 = match &cv.ty.0.kind {
                    expr::ExprKind::ForallE(d, b, _) => expr::forall_e(
                        expr::dup(d),
                        expr::dup(b),
                        expr::BinderMeta {
                            pw: prop_when::if_all_zero(ns),
                        },
                    ),
                    _ => expr::dup(&cv.ty),
                };
                let ci4 = ConstantInfo::IndInfo(
                    ConstantVal {
                        name: name::dup(&cv.name),
                        level_params: prop_when::names_copy(&cv.level_params),
                        ty: ty2,
                    },
                    env::ind_caps_dup(caps),
                );
                assert!(!env::constant_info_beq(&pin, &ci4));
                // a different constructor is never equal
                let ci5 = ConstantInfo::AxiomInfo(env::constant_val_dup(cv));
                assert!(!env::constant_info_beq(&pin, &ci5));
            }
            _ => panic!("eqA is an `indInfo`"),
        }
    }
}
