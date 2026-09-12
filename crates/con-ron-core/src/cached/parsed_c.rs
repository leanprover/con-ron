//! The parsed-declaration driver's data: `DeclC` (`ConLeche/Cached/ParsedC.lean`)
//! and the two records that cross the install/check seam, `ValueGroup`
//! (`ConLeche/Kernel/CheckerSplit.lean`) and `PendingCheck`
//! (`ConLeche/Cached/Installed.lean`).
//!
//! **Types only.**  The driver itself — `checkConstantValC`, `checkDefnValC`,
//! `annotConstantValC`, `annotStepC`, `annotDeclStep`, `checkPending`,
//! `checkDecls` — runs the core knot and the syntactic guards
//! (`ExprC.looseBVarsBounded`, `ExprC.hasFvar`, `constsResolveFC`,
//! `reservedBasisNames`), none of which is ported yet.  What is here is the
//! shape of the list `check_decls` consumes and the shape of what phase A
//! hands phase B.
//!
//! `DeclC` is `Declaration` with the *value* constructors' payloads at
//! `ExprC`, which is `Expr` (task #10, surprise 1), and **without**
//! `Declaration`'s `deriving DecidableEq, Repr, Inhabited` — con-leche
//! derives nothing on `DeclC`, deliberately (task #10's note on the
//! round-trip comparison).  Its `indDecl` carries *installed*
//! `ConstantInfo`s, so a parsed declaration transitively contains `IndCaps`,
//! `RecRule` (with `RecRuleFire`) and `ProjTable`, whose install-computed
//! fields are at their parse placeholders (task #10, surprise 2;
//! `env::rec_rule_parsed`, `env::ind_caps_default`).

use crate::kernel::env::BasisKind;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::ConstantVal;
use crate::kernel::env::ReducibilityHint;
use crate::kernel::expr::Expr;
use std::vec::Vec;

/// con-leche: ConLeche/Cached/ParsedC.lean:55-61 DeclC
/// A parsed declaration over `ExprC`.  Its constant-value records *are*
/// `ConLeche.ConstantVal` (con-leche task #198: the separate `ConstantValC`
/// is gone), so the header's type is an ordinary `Expr` — which is the same
/// type as the value payloads here, `ExprC` being `Expr`.
pub enum DeclC {
    AxiomDecl(ConstantVal),
    DefnDecl(ConstantVal, Expr, ReducibilityHint),
    ThmDecl(ConstantVal, Expr),
    OpaqueDecl(ConstantVal, Expr),
    BasisDecl(BasisKind),
    IndDecl(Vec<ConstantInfo>, u64),
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:38-42 ValueKind
/// The three declaration kinds whose value check is separable from their
/// install.  `ValueKind.word` (`:45-48`) is not ported: it renders the
/// kind into a type-mismatch message, and §3.1 says message strings need not
/// match.
pub enum ValueKind {
    Defn,
    Thm,
    Opaque,
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:38-42 ValueKind
/// The copy.
pub fn value_kind_dup(k: &ValueKind) -> ValueKind {
    match k {
        ValueKind::Defn => ValueKind::Defn,
        ValueKind::Thm => ValueKind::Thm,
        ValueKind::Opaque => ValueKind::Opaque,
    }
}

/// con-leche: ConLeche/Kernel/CheckerSplit.lean:56-59 ValueGroup
/// What the install half hands the check half: the kind, the header with its
/// type annotated, and the value — **annotated** for a definition or an
/// opaque (the install half annotated it and stored it), **raw** for a
/// theorem (the install half never looked at it: a theorem is stored by its
/// statement, and the check half annotates the value itself).
pub struct ValueGroup {
    pub kind: ValueKind,
    pub cv_a: ConstantVal,
    pub jv: Expr,
}

/// con-leche: ConLeche/Cached/Installed.lean:74-77 PendingCheck
/// A phase-A record awaiting its phase-B check: the datum that crosses the
/// install/check seam, the fold position of the declaration (its error tag)
/// and the environment counter at the install — `fe.visibleBelow` before the
/// push, i.e. the number of constants installed before it, which phase B
/// feeds to `fenv::restrict_to`.
///
/// Deviation: the two `Nat`s are `u64` (§3.3).
pub struct PendingCheck {
    pub vg: ValueGroup,
    pub pos: u64,
    pub vis: u64,
}

#[cfg(test)]
mod tests {
    use crate::kernel::env;
    use crate::kernel::env::BasisKind;
    use crate::kernel::env::ConstantInfo;
    use crate::kernel::env::ConstantVal;
    use crate::kernel::expr;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::cached::parsed_c;
    use crate::cached::parsed_c::DeclC;
    use crate::cached::parsed_c::ValueKind;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn cv(s: &str) -> ConstantVal {
        ConstantVal {
            name: nm(s),
            level_params: Vec::new(),
            ty: expr::sort(level::zero()),
        }
    }

    /// A `DeclC` list is what `check_decls` consumes; an `indDecl` block
    /// carries *installed* records at their parse placeholders.
    #[test]
    fn decl_list_shape() {
        let ds = vec![
            DeclC::AxiomDecl(cv("ax")),
            DeclC::BasisDecl(BasisKind::NatK),
            DeclC::IndDecl(
                vec![
                    ConstantInfo::IndInfo(cv("T"), env::ind_caps_default()),
                    ConstantInfo::CtorInfo(cv("T.mk"), 0, 0),
                    ConstantInfo::RecInfo(
                        cv("T.rec"),
                        0,
                        0,
                        vec![env::rec_rule_parsed(nm("T.mk"), 0, expr::bvar(0))],
                    ),
                ],
                0,
            ),
        ];
        assert_eq!(ds.len(), 3);
        match &ds[2] {
            DeclC::IndDecl(block, n_p) => {
                assert_eq!(*n_p, 0);
                assert!(env::recs_form_suffix(block));
                assert!(env::ind_params_ok(*n_p, block));
            }
            _ => panic!("wrong constructor"),
        }
    }

    /// `PendingCheck` records the datum, the fold position and the
    /// installation counter the prefix view is taken at.
    #[test]
    fn pending_check_carries_the_seam() {
        let pc = parsed_c::PendingCheck {
            vg: parsed_c::ValueGroup {
                kind: ValueKind::Thm,
                cv_a: cv("t"),
                jv: expr::bvar(0),
            },
            pos: 4,
            vis: 3,
        };
        assert_eq!((pc.pos, pc.vis), (4, 3));
        assert!(matches!(pc.vg.kind, ValueKind::Thm));
        assert!(name::beq(&pc.vg.cv_a.name, &nm("t")));
        assert!(matches!(
            parsed_c::value_kind_dup(&ValueKind::Opaque),
            ValueKind::Opaque
        ));
    }
}
