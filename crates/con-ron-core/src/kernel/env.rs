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
//!
//! `ProjTable.bodies` is an `Array Expr` and `ProjTable.guards` a `List
//! Level` in the Lean; the port does not inherit the asymmetry (task #10,
//! surprise 8) — both are `Vec`s.

use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The mode (`Env.lean:69-194`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:57-60 CheckMode
/// The checker's two-valued mode setting, validated once at startup and
/// threaded as configuration.  `deriving DecidableEq, Repr, Inhabited` is
/// dropped: nothing executable compares two modes (the five accessors below
/// are what the kernel reads).
pub enum CheckMode {
    Verified,
    Trusted,
}

/// con-leche: ConLeche/Kernel/Env.lean:67-68 CheckMode.ttChecks
/// The seven TT-lane checks: constantly `false` since con-leche's task #148.
/// The cited wildcard arm is spelled out over the two constructors.
pub fn tt_checks(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => false,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:79-81 CheckMode.verifiedChecks
/// The verified mode's extra checks (the λ-rule's codomain-sort check).
pub fn verified_checks(m: &CheckMode) -> bool {
    match m {
        CheckMode::Trusted => false,
        CheckMode::Verified => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:106-108 CheckMode.betaGate
/// The β-certificate gate.
pub fn beta_gate(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:128-129 CheckMode.ioGate
/// The io-grade knot slot: `true` at both modes.  The cited wildcard arm is
/// spelled out over the two constructors.
pub fn io_gate(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:160-162 CheckMode.certs
/// The certificate families: the work that exists only so the soundness
/// proof can consume it.
pub fn certs(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:171-172 CheckMode.betaSkip
/// The β site's read: `!mode.certs || (mode.betaGate && pw.isNever)`.
pub fn beta_skip(m: &CheckMode, pw: &PropWhen) -> bool {
    !certs(m) || (beta_gate(m) && prop_when::is_never(pw))
}

/// con-leche: ConLeche/Kernel/Env.lean:180-181 CheckMode.ioSkip
/// The io site's read: `!mode.certs || pw.isNever`.
pub fn io_skip(m: &CheckMode, pw: &PropWhen) -> bool {
    !certs(m) || prop_when::is_never(pw)
}

// ---------------------------------------------------------------------------
// Copy helpers for the `Vec` fields (`List`s in the Lean, shared by value)
// ---------------------------------------------------------------------------

/// con-leche: none — a `Vec<Level>` copy; Lean's `List Level` is shared by value
/// The entry point of the index recursion below (task #9's `*_from` pattern).
pub fn levels_copy(us: &Vec<Level>) -> Vec<Level> {
    levels_copy_from(us, 0, Vec::with_capacity(us.len()))
}

/// con-leche: none — the index recursion behind `levels_copy`
/// The accumulator is passed by value and returned (task #6's rule).
pub fn levels_copy_from(us: &Vec<Level>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= us.len() {
        out
    } else {
        let mut out = out;
        out.push(level::dup(&us[i]));
        levels_copy_from(us, i + 1, out)
    }
}

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

/// con-leche: ConLeche/Kernel/Env.lean:184-188 ConstantVal
/// Data common to all constants.  Deviation: the field `type` is `ty` —
/// `type` is a Rust keyword (task #6's modulo rule).
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
}

/// con-leche: ConLeche/Kernel/Env.lean:184-188 ConstantVal
/// The record copy: two `P` bumps and one `Vec<Name>` spine.
pub fn constant_val_dup(cv: &ConstantVal) -> ConstantVal {
    ConstantVal {
        name: name::dup(&cv.name),
        level_params: prop_when::names_copy(&cv.level_params),
        ty: expr::dup(&cv.ty),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:225-229 RecRuleFire
/// How a stored recursor rule may fire (install-computed; the parse
/// placeholder is `.inert`).
pub enum RecRuleFire {
    Inert,
    Plain,
    Nested(Vec<Level>, Vec<Expr>),
}

/// con-leche: ConLeche/Kernel/Env.lean:225-229 RecRuleFire
/// The copy; `.nested`'s two lists are copied spine-wise.
pub fn rec_rule_fire_dup(f: &RecRuleFire) -> RecRuleFire {
    match f {
        RecRuleFire::Inert => RecRuleFire::Inert,
        RecRuleFire::Plain => RecRuleFire::Plain,
        RecRuleFire::Nested(lvls, pins) => {
            RecRuleFire::Nested(levels_copy(lvls), exprs_copy(pins))
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:231-274 RecRule
/// One iota rule of a recursor.  The five install-computed fields
/// (`ctorParams`, `fire`, `k`, `eta`, `paramsBlind`) carry parse
/// placeholders `0`/`.inert`/`false` until the install computes them
/// (task #10, surprise 2); the Lean's `:= false`/`:= 0` field defaults
/// become `rec_rule_parsed` below, since Rust has none.
pub struct RecRule {
    pub ctor: Name,
    pub nfields: u64,
    pub ctor_params: u64,
    pub fire: RecRuleFire,
    pub rhs: Expr,
    pub k: bool,
    pub eta: bool,
    pub params_blind: bool,
}

/// con-leche: ConLeche/Kernel/Env.lean:231-274 RecRule
/// The record copy.
pub fn rec_rule_dup(r: &RecRule) -> RecRule {
    RecRule {
        ctor: name::dup(&r.ctor),
        nfields: r.nfields,
        ctor_params: r.ctor_params,
        fire: rec_rule_fire_dup(&r.fire),
        rhs: expr::dup(&r.rhs),
        k: r.k,
        eta: r.eta,
        params_blind: r.params_blind,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:231-274 RecRule
/// con-leche: ConLeche/Kernel/Basis/Builder.lean:117-121 BasisDSL.rule
/// A rule at the cited *parse placeholders* — the Lean's field defaults
/// `ctorParams := 0`, `fire := .inert`, `k := eta := paramsBlind := false`,
/// which a parsed stream always carries (task #10's census: all 2 715 parsed
/// rules).  Rust has no field defaults, so the record the parser builds goes
/// through this constructor.
pub fn rec_rule_parsed(ctor: Name, nfields: u64, rhs: Expr) -> RecRule {
    RecRule {
        ctor,
        nfields,
        ctor_params: 0,
        fire: RecRuleFire::Inert,
        rhs,
        k: false,
        eta: false,
        params_blind: false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:300-304 ReducibilityHint
/// The reducibility hint of a definition.  Deviation: `opaque` and `abbrev`
/// are spelled `Opaque`/`Abbrev` (the Lean writes them in `«»` because they
/// are Lean keywords; they are not Rust ones, but the constructor case is
/// Rust's).
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u64),
}

/// con-leche: ConLeche/Kernel/Env.lean:300-304 ReducibilityHint
/// The copy.
pub fn reducibility_hint_dup(h: &ReducibilityHint) -> ReducibilityHint {
    match h {
        ReducibilityHint::Opaque => ReducibilityHint::Opaque,
        ReducibilityHint::Abbrev => ReducibilityHint::Abbrev,
        ReducibilityHint::Regular(n) => ReducibilityHint::Regular(*n),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:311-316 ReducibilityHint.lt
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

/// con-leche: ConLeche/Kernel/Env.lean:326-328 ReducibilityHint.sameRegular
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

/// con-leche: ConLeche/Kernel/Env.lean:332-335 BasisKind
/// The trusted basis inductives.
pub enum BasisKind {
    EqK,
    NatK,
    EmptyK,
    FalseK,
    QuotK,
}

/// con-leche: ConLeche/Kernel/Env.lean:332-335 BasisKind
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

/// con-leche: ConLeche/Kernel/Env.lean:337-384 IndCaps
/// Definitional capabilities of a stored inductive type, recorded at
/// install.  Every field of the cited structure has a default; see
/// `ind_caps_default`.
pub struct IndCaps {
    pub eta: bool,
    pub eta_ctor: Name,
    pub eta_params: u64,
    pub eta_fields: u64,
    pub unitlike: bool,
    pub unit_params: u64,
    pub rule_k: bool,
    pub sort_z: PropWhen,
    /// the block's members (official's `all`), itself included
    pub all: Vec<Name>,
    /// the family's parameter count (official's `inductive_val.nparams`)
    pub nparams: u64,
    /// the family's constructors, in declaration order (official's `cnstrs`)
    pub ctors: Vec<Name>,
}

/// con-leche: ConLeche/Kernel/Env.lean:337-384 IndCaps
/// The cited structure's *field defaults*, which Rust has not: `eta :=
/// false`, `etaCtor := .anonymous`, `etaParams := etaFields := 0`,
/// `unitlike := false`, `unitParams := 0`, `ruleK := false` and — the one
/// that is not the obvious zero — **`sortZ := .ifAllZero []`**, which reads
/// "zero at every valuation" and not `.never` (task #10, surprise 6: picking
/// the other one changes the structure-η rescue's guard).  This is the
/// record every parsed `IndCaps` carries (task #10's census: all 1 917).
pub fn ind_caps_default() -> IndCaps {
    IndCaps {
        eta: false,
        eta_ctor: name::anonymous(),
        eta_params: 0,
        eta_fields: 0,
        unitlike: false,
        unit_params: 0,
        rule_k: false,
        sort_z: prop_when::if_all_zero(Vec::new()),
        all: Vec::new(),
        nparams: 0,
        ctors: Vec::new(),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:337-384 IndCaps
/// The record copy.
pub fn ind_caps_dup(c: &IndCaps) -> IndCaps {
    IndCaps {
        eta: c.eta,
        eta_ctor: name::dup(&c.eta_ctor),
        eta_params: c.eta_params,
        eta_fields: c.eta_fields,
        unitlike: c.unitlike,
        unit_params: c.unit_params,
        rule_k: c.rule_k,
        sort_z: prop_when::dup(&c.sort_z),
        all: prop_when::names_copy(&c.all),
        nparams: c.nparams,
        ctors: prop_when::names_copy(&c.ctors),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:408-438 ProjTable
/// One structure's projection table: everything the checker's `.proj` rules
/// consume about a structure `T`, stored once at the structure's install as
/// one constant under `proj_table_name T`.
pub struct ProjTable {
    pub struct_name: Name,
    pub level_params: Vec<Name>,
    pub num_params: u64,
    pub ctor: Name,
    pub num_fields: u64,
    pub struct_sort: Level,
    pub bodies: Vec<Expr>,
    pub guards: Vec<Level>,
    pub off: u64,
}

/// con-leche: ConLeche/Kernel/Env.lean:408-438 ProjTable
/// The record copy.
pub fn proj_table_dup(t: &ProjTable) -> ProjTable {
    ProjTable {
        struct_name: name::dup(&t.struct_name),
        level_params: prop_when::names_copy(&t.level_params),
        num_params: t.num_params,
        ctor: name::dup(&t.ctor),
        num_fields: t.num_fields,
        struct_sort: level::dup(&t.struct_sort),
        bodies: exprs_copy(&t.bodies),
        guards: levels_copy(&t.guards),
        off: t.off,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:468-493 ConstantInfo
/// Information stored about an accepted constant.
pub enum ConstantInfo {
    AxiomInfo(ConstantVal),
    DefnInfo(ConstantVal, Expr, ReducibilityHint),
    ThmInfo(ConstantVal, Expr),
    IndInfo(ConstantVal, IndCaps),
    CtorInfo(ConstantVal, u64, u64),
    RecInfo(ConstantVal, u64, u64, Vec<RecRule>),
    ProjInfo(ProjTable),
}

/// con-leche: none — a `Vec<RecRule>` copy; Lean's `List RecRule` is shared by value
/// The entry point of the index recursion below.
pub fn rec_rules_copy(rs: &Vec<RecRule>) -> Vec<RecRule> {
    rec_rules_copy_from(rs, 0, Vec::with_capacity(rs.len()))
}

/// con-leche: none — the index recursion behind `rec_rules_copy`
/// The accumulator is passed by value and returned.
pub fn rec_rules_copy_from(rs: &Vec<RecRule>, i: usize, out: Vec<RecRule>) -> Vec<RecRule> {
    if i >= rs.len() {
        out
    } else {
        let mut out = out;
        out.push(rec_rule_dup(&rs[i]));
        rec_rules_copy_from(rs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:468-493 ConstantInfo
/// The record copy; what `fenv::push` needs, because a pushed constant lands
/// both in `env.consts` and in the index (where Lean shares one value).
pub fn constant_info_dup(c: &ConstantInfo) -> ConstantInfo {
    match c {
        ConstantInfo::AxiomInfo(v) => ConstantInfo::AxiomInfo(constant_val_dup(v)),
        ConstantInfo::DefnInfo(v, value, hint) => ConstantInfo::DefnInfo(
            constant_val_dup(v),
            expr::dup(value),
            reducibility_hint_dup(hint),
        ),
        ConstantInfo::ThmInfo(v, value) => {
            ConstantInfo::ThmInfo(constant_val_dup(v), expr::dup(value))
        }
        ConstantInfo::IndInfo(v, caps) => {
            ConstantInfo::IndInfo(constant_val_dup(v), ind_caps_dup(caps))
        }
        ConstantInfo::CtorInfo(v, np, nf) => {
            ConstantInfo::CtorInfo(constant_val_dup(v), *np, *nf)
        }
        ConstantInfo::RecInfo(v, mi, rp, rules) => ConstantInfo::RecInfo(
            constant_val_dup(v),
            *mi,
            *rp,
            rec_rules_copy(rules),
        ),
        ConstantInfo::ProjInfo(tbl) => ConstantInfo::ProjInfo(proj_table_dup(tbl)),
    }
}

// ---------------------------------------------------------------------------
// The derived structural equalities (`deriving DecidableEq` on the records
// above) — what the two pinned-basis guards read (`kernel::basis_pins`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:294-304 ReducibilityHint
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

/// con-leche: ConLeche/Kernel/Env.lean:495-506 QuotKind
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

/// con-leche: ConLeche/Kernel/Env.lean:508-511 QuotKind.slot
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
    use crate::kernel::env::BasisKind;
    use crate::kernel::env::CheckMode;
    use crate::kernel::env::ConstantInfo;
    use crate::kernel::env::ConstantVal;
    use crate::kernel::env::ReducibilityHint;
    use crate::kernel::expr;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;

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

    #[test]
    fn mode_accessors() {
        for m in [CheckMode::Verified, CheckMode::Trusted] {
            assert!(!env::tt_checks(&m));
            assert!(env::io_gate(&m));
            // `certs` and `verifiedChecks` agree at both constructors, and
            // `betaGate` differs from them nowhere either (Env.lean:97-101).
            assert_eq!(env::certs(&m), env::verified_checks(&m));
            assert_eq!(env::beta_gate(&m), env::certs(&m));
        }
        assert!(env::verified_checks(&CheckMode::Verified));
        assert!(!env::verified_checks(&CheckMode::Trusted));
        // betaSkip/ioSkip: at `.trusted` both are the literal `true`.
        let never = prop_when::never();
        let always = prop_when::if_all_zero(Vec::new());
        assert!(env::beta_skip(&CheckMode::Trusted, &always));
        assert!(env::io_skip(&CheckMode::Trusted, &always));
        assert!(env::beta_skip(&CheckMode::Verified, &never));
        assert!(!env::beta_skip(&CheckMode::Verified, &always));
        assert!(env::io_skip(&CheckMode::Verified, &never));
        assert!(!env::io_skip(&CheckMode::Verified, &always));
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

    #[test]
    fn dups_are_faithful() {
        let ci = ConstantInfo::RecInfo(
            cv("R"),
            3,
            2,
            vec![env::rec_rule_parsed(nm("C"), 1, expr::bvar(0))],
        );
        let c2 = env::constant_info_dup(&ci);
        match c2 {
            ConstantInfo::RecInfo(cv2, mi, rp, rules) => {
                assert!(name::beq(&cv2.name, &nm("R")));
                assert_eq!((mi, rp), (3, 2));
                assert_eq!(rules.len(), 1);
                // the parse placeholders (task #10, surprise 2)
                assert_eq!(rules[0].ctor_params, 0);
                assert!(!rules[0].k && !rules[0].eta && !rules[0].params_blind);
                assert!(matches!(rules[0].fire, env::RecRuleFire::Inert));
            }
            _ => panic!("wrong constructor"),
        }
        // `IndCaps`'s one non-obvious default: `sortZ = ifAllZero []`, not
        // `never` (task #10, surprise 6)
        let caps = env::ind_caps_default();
        assert!(!prop_when::is_never(&caps.sort_z));
        assert!(!prop_when::has_params(&caps.sort_z));
        let caps2 = env::ind_caps_dup(&caps);
        assert!(prop_when::beq(&caps.sort_z, &caps2.sort_z));
        // the remaining copies
        assert!(matches!(
            env::basis_kind_dup(&BasisKind::QuotK),
            BasisKind::QuotK
        ));
    }
}
