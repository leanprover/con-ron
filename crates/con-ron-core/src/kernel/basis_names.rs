//! The pinned basis names — `ConLeche/Kernel/Basis/Names.lean`.
//!
//! Ported here because `Kernel/Core.lean` (task #18) reads every one of
//! them: the `Nat`/`String` literal guards, `isUnitLikeTy`'s `PUnit` pin,
//! the `And`-only η rescue and the `reservedBasisNames` exclusions in the
//! structure-η certificate.  The rest of `Kernel/Basis.lean` (the pinned
//! declarations themselves, one module per basis type) is a later task; this
//! file is self-contained and mentions no expression representation, exactly
//! as the Lean's does.
//!
//! **Lean's `def` is a value, Rust's is a function.**  Each cited `def` is a
//! closed top-level `Name`, built once at module initialization by Lean's
//! runtime and marked persistent.  The Aeneas subset has no such thing (task
//! #11's `bvarPool` note: a `static` cannot allocate a `P` tree and the
//! lazy alternatives are outside DESIGN.md §3.4), so each name is a
//! *function* that rebuilds its `Name` — the same value, at the cost of one
//! `P` allocation per call.  The interned checker looks names up through
//! `FEnv`'s index, so no comparison sees the difference; the saving can come
//! back in P1.6 as a pinned-name table in `CState` without touching the
//! model, because the model is the built name either way.
//!
//! String literals are `Vec<u32>` code points (DESIGN.md §3.3), spelled as a
//! `const […]` inside the function that needs it and copied by
//! `core_types::code_points`.

use crate::kernel::core_types;
use crate::kernel::name;
use crate::kernel::name::Name;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/Basis/Names.lean:17-18 eqName
/// The name of the basis equality type.
pub fn eq_name() -> Name {
    const S: [u32; 2] = [69, 113];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:20-21 eqReflName
/// The name of the basis equality constructor.
pub fn eq_refl_name() -> Name {
    const S: [u32; 4] = [114, 101, 102, 108];
    name::mk_str(eq_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:23-24 punitName
/// The name of the basis unit type.
pub fn punit_name() -> Name {
    const S: [u32; 5] = [80, 85, 110, 105, 116];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:105-115 reservedBasisNames
/// `n.str "rec"`, the recursor-name suffix five of the reserved names share
/// (`eqName.str "rec"`, `natName.str "rec"`, …).  A named helper because
/// Rust has no string literals in the core; the Lean spells the suffix out
/// at each of the five sites.
pub fn rec_of(n: Name) -> Name {
    const S: [u32; 3] = [114, 101, 99];
    name::mk_str(n, core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:26-29 punitRecName
/// The name of the basis unit type's recursor.  A top-level constant in the
/// Lean so that `isUnitLikeTy` does not rebuild it per proof-irrelevance
/// attempt (con-leche's task #161 item C1); the port rebuilds it, as every
/// name in this module (the module note).
pub fn punit_rec_name() -> Name {
    rec_of(punit_name())
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:31-32 natName
/// The name `Nat`.
pub fn nat_name() -> Name {
    const S: [u32; 3] = [78, 97, 116];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:34-35 natZeroName
/// The name `Nat.zero`.
pub fn nat_zero_name() -> Name {
    const S: [u32; 4] = [122, 101, 114, 111];
    name::mk_str(nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:37-38 natSuccName
/// The name `Nat.succ`.
pub fn nat_succ_name() -> Name {
    const S: [u32; 4] = [115, 117, 99, 99];
    name::mk_str(nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:40-41 punitUnitName
/// The name of the basis unit constructor.
pub fn punit_unit_name() -> Name {
    const S: [u32; 4] = [117, 110, 105, 116];
    name::mk_str(punit_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:43-43 emptyName
/// The name `Empty`.
pub fn empty_name() -> Name {
    const S: [u32; 5] = [69, 109, 112, 116, 121];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:45-49 falseName
/// The name of the pinned `False` basis type.
pub fn false_name() -> Name {
    const S: [u32; 5] = [70, 97, 108, 115, 101];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:51-52 quotName
/// The name of the basis quotient type.
pub fn quot_name() -> Name {
    const S: [u32; 4] = [81, 117, 111, 116];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:54-55 quotMkName
/// The name of the basis quotient constructor.
pub fn quot_mk_name() -> Name {
    const S: [u32; 2] = [109, 107];
    name::mk_str(quot_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:57-58 quotLiftName
/// The name of the basis quotient lift eliminator.
pub fn quot_lift_name() -> Name {
    const S: [u32; 4] = [108, 105, 102, 116];
    name::mk_str(quot_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:60-61 quotIndName
/// The name of the basis quotient induction eliminator.
pub fn quot_ind_name() -> Name {
    const S: [u32; 3] = [105, 110, 100];
    name::mk_str(quot_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:63-64 quotSoundName
/// The name of the basis quotient soundness axiom.
pub fn quot_sound_name() -> Name {
    const S: [u32; 5] = [115, 111, 117, 110, 100];
    name::mk_str(quot_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:73-74 stringName
/// The name `String`.
pub fn string_name() -> Name {
    const S: [u32; 6] = [83, 116, 114, 105, 110, 103];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:76-77 stringOfListName
/// The name `String.ofList`.
pub fn string_of_list_name() -> Name {
    const S: [u32; 6] = [111, 102, 76, 105, 115, 116];
    name::mk_str(string_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:79-80 listName
/// The name `List`.
pub fn list_name() -> Name {
    const S: [u32; 4] = [76, 105, 115, 116];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:82-83 listNilName
/// The name `List.nil`.
pub fn list_nil_name() -> Name {
    const S: [u32; 3] = [110, 105, 108];
    name::mk_str(list_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:85-86 listConsName
/// The name `List.cons`.
pub fn list_cons_name() -> Name {
    const S: [u32; 4] = [99, 111, 110, 115];
    name::mk_str(list_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:88-89 charName
/// The name `Char`.
pub fn char_name() -> Name {
    const S: [u32; 4] = [67, 104, 97, 114];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:91-97 andName
/// The name `And`: the one propositional structure whose recursor is rescued
/// on a stuck proof (`core_k::major_to_ctor`'s `And` branch).
pub fn and_name() -> Name {
    const S: [u32; 3] = [65, 110, 100];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:99-100 andIntroName
/// The name `And.intro`.
pub fn and_intro_name() -> Name {
    const S: [u32; 5] = [105, 110, 116, 114, 111];
    name::mk_str(and_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:102-103 charOfNatName
/// The name `Char.ofNat`.
pub fn char_of_nat_name() -> Name {
    const S: [u32; 5] = [111, 102, 78, 97, 116];
    name::mk_str(char_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:105-115 reservedBasisNames
/// Names reserved for the pinned basis blocks; no other declaration may use
/// them.  The cited `List Name` is a `Vec<Name>` built in the cited order,
/// and the five `… .str "rec"` entries go through `rec_of`.  `PSigma'` is not
/// among them (con-leche's task #175 W6).
pub fn reserved_basis_names() -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    ns.push(eq_name());
    ns.push(eq_refl_name());
    ns.push(rec_of(eq_name()));
    ns.push(nat_name());
    ns.push(nat_zero_name());
    ns.push(nat_succ_name());
    ns.push(rec_of(nat_name()));
    ns.push(punit_name());
    ns.push(punit_unit_name());
    ns.push(rec_of(punit_name()));
    ns.push(empty_name());
    ns.push(rec_of(empty_name()));
    ns.push(false_name());
    ns.push(rec_of(false_name()));
    ns.push(quot_name());
    ns.push(quot_mk_name());
    ns.push(quot_lift_name());
    ns.push(quot_ind_name());
    ns.push(quot_sound_name());
    ns
}

#[cfg(test)]
mod tests {
    use crate::kernel::basis_names as bn;
    use crate::kernel::name;

    /// Every reserved name is distinct, and the list is the cited 19.
    #[test]
    fn reserved_names_are_nineteen_and_distinct() {
        let ns = bn::reserved_basis_names();
        assert_eq!(ns.len(), 19);
        for i in 0..ns.len() {
            for j in 0..ns.len() {
                assert_eq!(name::beq(&ns[i], &ns[j]), i == j, "{i} vs {j}");
            }
        }
    }

    /// The shapes the checker's pins rely on: prefix, suffix and the `rec_of`
    /// helper agreeing with the spelled-out names.
    #[test]
    fn name_shapes() {
        assert!(name::beq(&bn::punit_rec_name(), &bn::rec_of(bn::punit_name())));
        assert!(name::beq(
            &bn::nat_zero_name(),
            &bn::reserved_basis_names()[4]
        ));
        // distinct heads
        assert!(!name::beq(&bn::nat_name(), &bn::string_name()));
        assert!(!name::beq(&bn::and_name(), &bn::and_intro_name()));
        // `Name.beq` is structural, so a rebuilt name equals the first build
        assert!(name::beq(&bn::char_of_nat_name(), &bn::char_of_nat_name()));
    }
}
