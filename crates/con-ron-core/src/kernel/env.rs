//! `ConLeche/Kernel/Env.lean`: the checker's mode, the stored-constant
//! records, the input declarations and the global environment.
//!
//! Conventions this module fixes for everything below it:
//!
//! * **`Nat` counters are `u64`** (DESIGN.md §3.3): parameter, field, index
//!   and height counts are never large, `abs` casts, and an overflow is a
//!   Rust failure — harmless for the accept direction.  Where such a count
//!   indexes a `Vec` it is cast to `usize` at the index site.
//! * **`List` fields are `Vec`s** (`levelParams`, `guards`, `rules`,
//!   `block`), with the *same order* — with **one exception**, `Env.consts`,
//!   which is stored **reversed**: index `0` is the *oldest* constant and the
//!   newest is at the back, so `fenv::push` is a `Vec::push` (`O(1)`
//!   amortised) instead of a front insertion, and no function of the port
//!   calls `Vec::insert` (task #50; the model of `Vec::insert` is an
//!   overwrite, `AENEAS_FINDINGS.md` §3.9).  Every reader of the list goes
//!   through this module's `find` — which scans it from the *back*, i.e. the
//!   cited list from the front, so the newest binding of a name still wins,
//!   exactly as `List.find?` does — or through `fenv`'s index; `env_of`
//!   takes the cited newest-first list and reverses it, and the model reads
//!   `Env.consts` reversed (`Refine/Abs.lean`'s `absEnv`).
//! * **No `Repr`, no `Inhabited`, and the derived equality written out by
//!   hand.**  `deriving DecidableEq` on these records has two executable
//!   consumers and no more: the block-partition decision con-leche
//!   *substitutes away* (`blockRecSuffixDec`, `Env.lean:737`, whose whole
//!   point is that the tag pass `recsFormSuffix` decides it without
//!   comparing an expression — `block_rec_suffix_ok` below), and the **two
//!   pinned-basis guards that compare a whole stored `ConstantInfo`**
//!   (`env.find? eqName = some eqA`, `env.find? natName = some natA`; see
//!   `crate::kernel::basis_pins`).  §3.4 forbids the `derive`, and a derived
//!   `PartialEq` would compare the `P` trees structurally with no pointer
//!   fast path, so the instances are spelled out as the `*_beq` family
//!   below, componentwise in the cited field order, over the crate's own
//!   `name::beq`/`expr::beq`/`level::beq`/`prop_when::beq` (§3.2).
//!   Everything else the checker compares is `Name.beq`, `Expr.beq` and the
//!   `==` inside `sameRegular`.
//! * **An explicit `*_dup` per type** rather than `#[derive(Clone)]`, as
//!   `nat.rs`/`name.rs`/`expr.rs` do.  A `dup` of a `Name`, `Level`, `Expr`
//!   or `PropWhen` is a `P` bump; a `dup` of a record copies its `Vec`s.

use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The mode (`Env.lean:69-194`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:20-58 CheckMode
/// The checker's mode: `--verified` or `--trusted`.  The official kernel's
/// `m_eager_reduce` flag is not the mode's: it is internal to the knot
/// (`arena::core::KnotMode`).  `deriving DecidableEq, Repr, Inhabited` is
/// dropped: nothing executable compares two modes (`verified_checks` below is
/// what the kernel reads).
pub enum CheckMode {
    Verified,
    Trusted,
}

/// con-leche: ConLeche/Kernel/Env.lean:60-81 CheckMode.verifiedChecks
/// The verified mode's extra checks: the η and λ/λ body-type comparisons and
/// the certificate families (the K/`And` rescues' proof irrelevance, ι's
/// case-3 decision, the projection fire's arity check) — everything the
/// trusted mode omits.
pub fn verified_checks(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => false,
    }
}

// ---------------------------------------------------------------------------
// Copy helpers for the `Vec` fields (`List`s in the Lean, shared by value)
// ---------------------------------------------------------------------------

/// con-leche: none — a `Vec<Expr>` copy; Lean's `Array Expr` is shared by value
/// The entry point of the index recursion below.
pub fn exprs_copy(es: &Vec<Expr>) -> Vec<Expr> {
    exprs_copy_from(es, 0, Vec::with_capacity(es.len()))
}

/// con-leche: none — the index recursion behind `exprs_copy`
/// Each element is a `P` bump; only the spine is copied.
pub fn exprs_copy_from(es: &Vec<Expr>, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if i >= es.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&es[i]));
        exprs_copy_from(es, i + 1, out)
    }
}

// ---------------------------------------------------------------------------
// The stored-constant records (`Env.lean:197-496`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:84-88 ConstantVal
/// Data common to all constants.  Deviation: the field `type` is `ty` —
/// `type` is a Rust keyword (task #6's modulo rule).
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
}

/// con-leche: ConLeche/Kernel/Env.lean:90-122 RecRuleFire
/// How a stored recursor rule fires (read off the recursor's record; the
/// parse placeholder is `.plain`): `.plain` at a member major, `.nested lvls
/// pins` at an outside one (the comparands of a case-3 fire), `.levels lvls`
/// at a quotient eliminator (the comparand levels, over the recursor's own
/// level parameters).
pub enum RecRuleFire {
    Plain,
    Nested(Vec<Level>, Vec<Expr>),
    Levels(Vec<Level>),
}

/// con-leche: ConLeche/Kernel/Env.lean:124-139 RecRule
/// One iota rule of a recursor: the record's three fields, as Lean's
/// `RecursorRule` has them, and `fire`, read off the recursor's record (the
/// parse placeholder `.plain`).
pub struct RecRule {
    pub ctor: Name,
    pub nfields: u64,
    pub fire: RecRuleFire,
    pub rhs: Expr,
}

/// con-leche: ConLeche/Kernel/Env.lean:147-151 ReducibilityHint
/// The reducibility hint of a definition.  Deviation: `opaque` and `abbrev`
/// are spelled `Opaque`/`Abbrev` (the Lean writes them in `«»` because they
/// are Lean keywords; they are not Rust ones, but the constructor case is
/// Rust's).
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u64),
}

/// con-leche: ConLeche/Kernel/Env.lean:147-151 ReducibilityHint
/// The copy.
pub fn reducibility_hint_dup(h: &ReducibilityHint) -> ReducibilityHint {
    match h {
        ReducibilityHint::Opaque => ReducibilityHint::Opaque,
        ReducibilityHint::Abbrev => ReducibilityHint::Abbrev,
        ReducibilityHint::Regular(n) => ReducibilityHint::Regular(*n),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:158-163 ReducibilityHint.lt
/// `h₁.lt h₂`: `h₁` is strictly less eager to unfold than `h₂`.  The cited
/// five arms overlap, so they are read *in order*: the first arm matching a
/// pair wins.  Spelled here as one nested match in the same order, with
/// `_, .opaque => false` first.
pub fn reducibility_hint_lt(h1: &ReducibilityHint, h2: &ReducibilityHint) -> bool {
    match h2 {
        ReducibilityHint::Opaque => false,
        ReducibilityHint::Abbrev => match h1 {
            ReducibilityHint::Abbrev => false,
            ReducibilityHint::Opaque => true,
            ReducibilityHint::Regular(_) => true,
        },
        ReducibilityHint::Regular(h2h) => match h1 {
            ReducibilityHint::Abbrev => false,
            ReducibilityHint::Opaque => true,
            ReducibilityHint::Regular(h1h) => *h1h < *h2h,
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:173-175 ReducibilityHint.sameRegular
/// Both hints are `regular` at the *same* height.
pub fn reducibility_hint_same_regular(h1: &ReducibilityHint, h2: &ReducibilityHint) -> bool {
    match h1 {
        ReducibilityHint::Regular(a) => match h2 {
            ReducibilityHint::Regular(b) => *a == *b,
            ReducibilityHint::Opaque => false,
            ReducibilityHint::Abbrev => false,
        },
        ReducibilityHint::Opaque => false,
        ReducibilityHint::Abbrev => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:179-182 BasisKind
/// The trusted basis inductives.
pub enum BasisKind {
    EqK,
    NatK,
    EmptyK,
    FalseK,
    QuotK,
}

/// con-leche: ConLeche/Kernel/Env.lean:179-182 BasisKind
/// The copy.
pub fn basis_kind_dup(k: &BasisKind) -> BasisKind {
    match k {
        BasisKind::EqK => BasisKind::EqK,
        BasisKind::NatK => BasisKind::NatK,
        BasisKind::EmptyK => BasisKind::EmptyK,
        BasisKind::FalseK => BasisKind::FalseK,
        BasisKind::QuotK => BasisKind::QuotK,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:184-227 IndCaps
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::IndCaps_refines, then delete this line
/// Definitional capabilities of a stored inductive type that its block alone
/// decides, read off the block's records.  The family's result sort is on no
/// record, so what depends on it is computed where it is read.  Every field of
/// the cited structure has a default; see `ind_caps_default`.
pub struct IndCaps {
    /// official's `is_non_rec_structure`: one constructor, no index, a block
    /// that is not recursive
    pub eta: bool,
    /// the block's members (official's `all`), itself included
    pub all: Vec<Name>,
    /// the family's parameter count (official's `inductive_val.nparams`)
    pub nparams: u64,
    /// the family's index count (official's `inductive_val.nindices`), read
    /// off the block's recursor record
    pub n_idx: u64,
    /// the family's constructors, in declaration order (official's `cnstrs`)
    pub ctors: Vec<Name>,
    /// the family's sort is never zero at every level instantiation, read off
    /// the former's stored type at its check; `false` claims nothing
    pub never_zero: bool,
}

/// con-leche: ConLeche/Kernel/Env.lean:184-227 IndCaps
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::ind_caps_default_refines, then delete this line
/// The cited structure's *field defaults*, which Rust has not: `eta :=
/// false`, `never_zero := false`, every count `0`, every list empty.
pub fn ind_caps_default() -> IndCaps {
    IndCaps {
        eta: false,
        all: Vec::new(),
        nparams: 0,
        n_idx: 0,
        ctors: Vec::new(),
        never_zero: false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:288-312 ConstantInfo
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove env::ConstantInfo_refines, then delete this line
/// Information stored about an accepted constant.  A constructor carries its
/// family's name (official's `ConstructorVal.induct`).  A recursor carries its
/// record's K flag (official's `recursor_val::is_k`), the `bool` before its
/// rules.
pub enum ConstantInfo {
    AxiomInfo(ConstantVal),
    DefnInfo(ConstantVal, Expr, ReducibilityHint),
    ThmInfo(ConstantVal),
    IndInfo(ConstantVal, IndCaps),
    CtorInfo(ConstantVal, u64, u64, Name),
    RecInfo(ConstantVal, u64, u64, bool, Vec<RecRule>),
}

// ---------------------------------------------------------------------------
// The derived structural equalities (`deriving DecidableEq` on the records
// above) — what the two pinned-basis guards read (`kernel::basis_pins`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:141-151 ReducibilityHint
/// Lean's `deriving DecidableEq` on `ReducibilityHint`.
pub fn reducibility_hint_beq(a: &ReducibilityHint, b: &ReducibilityHint) -> bool {
    match a {
        ReducibilityHint::Opaque => match b {
            ReducibilityHint::Opaque => true,
            _ => false,
        },
        ReducibilityHint::Abbrev => match b {
            ReducibilityHint::Abbrev => true,
            _ => false,
        },
        ReducibilityHint::Regular(h1) => match b {
            ReducibilityHint::Regular(h2) => h1 == h2,
            _ => false,
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:314-325 QuotKind
/// Which of the four quotient constants a `#QUOT` record declares — the
/// record's `kind` field, decoded — plus `Sound`, which is not a kind the
/// decoder reads but the slot `Quot.sound`'s own axiom record is compared at
/// (con-leche task #293).
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
    Sound,
}

/// con-leche: ConLeche/Kernel/Env.lean:327-330 QuotKind.slot
/// The quotient constant's position in the pinned block.
///
/// Deviation: the cited `Nat` is a `u64` (§3.3).
pub fn quot_kind_slot(k: &QuotKind) -> u64 {
    match k {
        QuotKind::Type => 0,
        QuotKind::Ctor => 1,
        QuotKind::Lift => 2,
        QuotKind::Ind => 3,
        QuotKind::Sound => 4,
    }
}

/// con-leche: none — the copy of a `QuotKind` (Lean's value semantics)
pub fn quot_kind_dup(k: &QuotKind) -> QuotKind {
    match k {
        QuotKind::Type => QuotKind::Type,
        QuotKind::Ctor => QuotKind::Ctor,
        QuotKind::Lift => QuotKind::Lift,
        QuotKind::Ind => QuotKind::Ind,
        QuotKind::Sound => QuotKind::Sound,
    }
}

// ---------------------------------------------------------------------------
// The block's recursor suffix, decided on the tags (`Env.lean:666-675`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use crate::kernel::env;
    use crate::kernel::env::CheckMode;
    use crate::kernel::env::ReducibilityHint;

    #[test]
    fn mode_accessors() {
        for m in [CheckMode::Verified, CheckMode::Trusted] {
            let _ = env::verified_checks(&m);
        }
        assert!(env::verified_checks(&CheckMode::Verified));
        assert!(!env::verified_checks(&CheckMode::Trusted));
    }

    #[test]
    fn reducibility_hint_order() {
        let o = ReducibilityHint::Opaque;
        let a = ReducibilityHint::Abbrev;
        let r3 = ReducibilityHint::Regular(3);
        let r5 = ReducibilityHint::Regular(5);
        // opaque < regular h < abbrev
        assert!(env::reducibility_hint_lt(&o, &r3));
        assert!(env::reducibility_hint_lt(&o, &a));
        assert!(env::reducibility_hint_lt(&r3, &a));
        assert!(env::reducibility_hint_lt(&r3, &r5));
        assert!(!env::reducibility_hint_lt(&r5, &r3));
        assert!(!env::reducibility_hint_lt(&r3, &r3));
        // nothing is less eager than opaque, abbrev is less than nothing
        assert!(!env::reducibility_hint_lt(&a, &o));
        assert!(!env::reducibility_hint_lt(&a, &r3));
        assert!(!env::reducibility_hint_lt(&o, &o));
        assert!(!env::reducibility_hint_lt(&a, &a));
        // sameRegular
        assert!(env::reducibility_hint_same_regular(&r3, &r3));
        assert!(!env::reducibility_hint_same_regular(&r3, &r5));
        assert!(!env::reducibility_hint_same_regular(&o, &o));
        assert!(!env::reducibility_hint_same_regular(&a, &a));
    }

}
