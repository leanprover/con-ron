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
//!   `block`, `Env.consts`), with the *same order*.  `Env.consts` is
//!   con-leche's own "newest first": index `0` is the most recently
//!   installed constant, and `find?` is the linear search over that order,
//!   exactly as `List.find?` is.
//! * **No derived equality, no `Repr`, no `Inhabited`.**  `deriving
//!   DecidableEq` on these records is used by con-leche only in `Prop`s and
//!   in the block-partition decision it *substitutes away*
//!   (`blockRecSuffixDec`, `Env.lean:737`, whose whole point is that the tag
//!   pass `recsFormSuffix` decides it without comparing an expression); the
//!   executable comparisons the checker does are `Name.beq`, `Expr.beq` and
//!   the `==` inside `sameRegular`, and those are ported.  DESIGN.md §3.4:
//!   derive nothing you do not need.
//! * **An explicit `*_dup` per type** rather than `#[derive(Clone)]`, as
//!   `nat.rs`/`name.rs`/`expr.rs` do.  A `dup` of a `Name`, `Level`, `Expr`
//!   or `PropWhen` is an `Rc` bump; a `dup` of a record copies its `Vec`s.
//!
//! `ProjTable.bodies` is an `Array Expr` and `ProjTable.guards` a `List
//! Level` in the Lean; the port does not inherit the asymmetry (task #10,
//! surprise 8) — both are `Vec`s.

use crate::core_types;
use crate::expr;
use crate::expr::Expr;
use crate::expr::ExprKind;
use crate::level;
use crate::level::Level;
use crate::name;
use crate::name::Name;
use crate::prop_when;
use crate::prop_when::PropWhen;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The mode (`Env.lean:69-194`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:69-72 CheckMode
/// The checker's two-valued mode setting, validated once at startup and
/// threaded as configuration.  `deriving DecidableEq, Repr, Inhabited` is
/// dropped: nothing executable compares two modes (the five accessors below
/// are what the kernel reads).
pub enum CheckMode {
    Verified,
    Trusted,
}

/// con-leche: ConLeche/Kernel/Env.lean:69-72 CheckMode
/// The `Rc`-free copy of a two-constructor enum.
pub fn check_mode_dup(m: &CheckMode) -> CheckMode {
    match m {
        CheckMode::Verified => CheckMode::Verified,
        CheckMode::Trusted => CheckMode::Trusted,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:80-81 CheckMode.ttChecks
/// The seven TT-lane checks: constantly `false` since con-leche's task #148.
/// The cited wildcard arm is spelled out over the two constructors.
pub fn tt_checks(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => false,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:92-94 CheckMode.verifiedChecks
/// The verified mode's extra checks (the λ-rule's codomain-sort check).
pub fn verified_checks(m: &CheckMode) -> bool {
    match m {
        CheckMode::Trusted => false,
        CheckMode::Verified => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:119-121 CheckMode.betaGate
/// The β-certificate gate.
pub fn beta_gate(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:141-142 CheckMode.ioGate
/// The io-grade knot slot: `true` at both modes.  The cited wildcard arm is
/// spelled out over the two constructors.
pub fn io_gate(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:173-175 CheckMode.certs
/// The certificate families: the work that exists only so the soundness
/// proof can consume it.
pub fn certs(m: &CheckMode) -> bool {
    match m {
        CheckMode::Verified => true,
        CheckMode::Trusted => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:184-185 CheckMode.betaSkip
/// The β site's read: `!mode.certs || (mode.betaGate && pw.isNever)`.
pub fn beta_skip(m: &CheckMode, pw: &PropWhen) -> bool {
    !certs(m) || (beta_gate(m) && prop_when::is_never(pw))
}

/// con-leche: ConLeche/Kernel/Env.lean:193-194 CheckMode.ioSkip
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
    levels_copy_from(us, 0, Vec::new())
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
    exprs_copy_from(es, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `exprs_copy`
/// Each element is an `Rc` bump; only the spine is copied.
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

/// con-leche: ConLeche/Kernel/Env.lean:197-201 ConstantVal
/// Data common to all constants.  Deviation: the field `type` is `ty` —
/// `type` is a Rust keyword (task #6's modulo rule).
pub struct ConstantVal {
    pub name: Name,
    pub level_params: Vec<Name>,
    pub ty: Expr,
}

/// con-leche: ConLeche/Kernel/Env.lean:197-201 ConstantVal
/// The record copy: two `Rc` bumps and one `Vec<Name>` spine.
pub fn constant_val_dup(cv: &ConstantVal) -> ConstantVal {
    ConstantVal {
        name: name::dup(&cv.name),
        level_params: prop_when::names_copy(&cv.level_params),
        ty: expr::dup(&cv.ty),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:243-247 RecRuleFire
/// How a stored recursor rule may fire (install-computed; the parse
/// placeholder is `.inert`).
pub enum RecRuleFire {
    Inert,
    Plain,
    Nested(Vec<Level>, Vec<Expr>),
}

/// con-leche: ConLeche/Kernel/Env.lean:243-247 RecRuleFire
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

/// con-leche: ConLeche/Kernel/Env.lean:259-292 RecRule
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

/// con-leche: ConLeche/Kernel/Env.lean:259-292 RecRule
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

/// con-leche: ConLeche/Kernel/Env.lean:259-292 RecRule
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

/// con-leche: ConLeche/Kernel/Env.lean:298-301 RecRule.compareParams
/// Whether the ι step compares this rule's parameter comparands.
pub fn rec_rule_compare_params(rl: &RecRule) -> bool {
    match rl.fire {
        RecRuleFire::Plain => !rl.params_blind,
        RecRuleFire::Inert => true,
        RecRuleFire::Nested(..) => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:318-322 ReducibilityHint
/// The reducibility hint of a definition.  Deviation: `opaque` and `abbrev`
/// are spelled `Opaque`/`Abbrev` (the Lean writes them in `«»` because they
/// are Lean keywords; they are not Rust ones, but the constructor case is
/// Rust's).
pub enum ReducibilityHint {
    Opaque,
    Abbrev,
    Regular(u64),
}

/// con-leche: ConLeche/Kernel/Env.lean:318-322 ReducibilityHint
/// The copy.
pub fn reducibility_hint_dup(h: &ReducibilityHint) -> ReducibilityHint {
    match h {
        ReducibilityHint::Opaque => ReducibilityHint::Opaque,
        ReducibilityHint::Abbrev => ReducibilityHint::Abbrev,
        ReducibilityHint::Regular(n) => ReducibilityHint::Regular(*n),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:329-334 ReducibilityHint.lt
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

/// con-leche: ConLeche/Kernel/Env.lean:344-346 ReducibilityHint.sameRegular
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

/// con-leche: ConLeche/Kernel/Env.lean:352-354 BasisKind
/// The trusted basis inductives.
pub enum BasisKind {
    EqK,
    NatK,
    PunitK,
    EmptyK,
    FalseK,
    QuotK,
}

/// con-leche: ConLeche/Kernel/Env.lean:352-354 BasisKind
/// The copy.
pub fn basis_kind_dup(k: &BasisKind) -> BasisKind {
    match k {
        BasisKind::EqK => BasisKind::EqK,
        BasisKind::NatK => BasisKind::NatK,
        BasisKind::PunitK => BasisKind::PunitK,
        BasisKind::EmptyK => BasisKind::EmptyK,
        BasisKind::FalseK => BasisKind::FalseK,
        BasisKind::QuotK => BasisKind::QuotK,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:362-384 IndCaps
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
}

/// con-leche: ConLeche/Kernel/Env.lean:362-384 IndCaps
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
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:362-384 IndCaps
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
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:411-441 ProjTable
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

/// con-leche: ConLeche/Kernel/Env.lean:411-441 ProjTable
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

/// con-leche: ConLeche/Kernel/Env.lean:447-462 ProjEntry
/// The per-field view of a `ProjTable`, i.e. what `find_proj` returns.
pub struct ProjEntry {
    pub struct_name: Name,
    pub idx: u64,
    pub level_params: Vec<Name>,
    pub num_params: u64,
    pub ctor: Name,
    pub num_fields: u64,
    pub body: Expr,
    pub field_sort: Level,
    pub struct_sort: Level,
    pub off: u64,
}

/// con-leche: ConLeche/Kernel/Expr.lean:285-403 Expr
/// `default : Expr`, i.e. the cited inductive's `deriving Inhabited` at
/// `Expr.lean:403`: Lean's derived instance is the first constructor at its
/// arguments' own defaults, `.bvar 0`.  Task #11 deliberately did not port
/// the instance; the one place the checker needs the value is
/// `ProjTable.entry`'s `bodies.getD i default`, so it is spelled here.
pub fn default_expr() -> Expr {
    expr::bvar(0)
}

/// con-leche: ConLeche/Kernel/Env.lean:466-468 ProjTable.entry
/// The per-field view of a table at field `i` (meaningful for `i <
/// numFields`).  The two `getD`s are out-of-range guards: Lean's `default :
/// Expr` is `.bvar 0` (`default_expr`) and `guards.getD i .zero` falls back
/// to `Level.zero`.
pub fn proj_table_entry(tbl: &ProjTable, i: u64) -> ProjEntry {
    let body = if i < tbl.bodies.len() as u64 {
        expr::dup(&tbl.bodies[i as usize])
    } else {
        default_expr()
    };
    let field_sort = if i < tbl.guards.len() as u64 {
        level::dup(&tbl.guards[i as usize])
    } else {
        level::zero()
    };
    ProjEntry {
        struct_name: name::dup(&tbl.struct_name),
        idx: i,
        level_params: prop_when::names_copy(&tbl.level_params),
        num_params: tbl.num_params,
        ctor: name::dup(&tbl.ctor),
        num_fields: tbl.num_fields,
        body,
        field_sort,
        struct_sort: level::dup(&tbl.struct_sort),
        off: tbl.off,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:471-496 ConstantInfo
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
    rec_rules_copy_from(rs, 0, Vec::new())
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

/// con-leche: ConLeche/Kernel/Env.lean:471-496 ConstantInfo
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

/// con-leche: none — a `Vec<ConstantInfo>` copy; Lean's `List ConstantInfo` is shared by value
/// The entry point of the index recursion below.
pub fn constant_infos_copy(cs: &Vec<ConstantInfo>) -> Vec<ConstantInfo> {
    constant_infos_copy_from(cs, 0, Vec::new())
}

/// con-leche: none — the index recursion behind `constant_infos_copy`
/// The accumulator is passed by value and returned.
pub fn constant_infos_copy_from(
    cs: &Vec<ConstantInfo>,
    i: usize,
    out: Vec<ConstantInfo>,
) -> Vec<ConstantInfo> {
    if i >= cs.len() {
        out
    } else {
        let mut out = out;
        out.push(constant_info_dup(&cs[i]));
        constant_infos_copy_from(cs, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:499-528 Declaration
/// A declaration presented to the checker.  `indDecl` carries the parameter
/// count the *stream declares* (con-leche task #228), checked by
/// `ind_params_ok`.
pub enum Declaration {
    AxiomDecl(ConstantVal),
    DefnDecl(ConstantVal, Expr, ReducibilityHint),
    ThmDecl(ConstantVal, Expr),
    OpaqueDecl(ConstantVal, Expr),
    BasisDecl(BasisKind),
    IndDecl(Vec<ConstantInfo>, u64),
}

/// con-leche: ConLeche/Kernel/Env.lean:533-535 Declaration.name
/// The name of a non-basis declaration (basis and inductive blocks install
/// several, so they answer `.anonymous`).
pub fn declaration_name(d: &Declaration) -> Name {
    match d {
        Declaration::AxiomDecl(v) => name::dup(&v.name),
        Declaration::DefnDecl(v, _, _) => name::dup(&v.name),
        Declaration::ThmDecl(v, _) => name::dup(&v.name),
        Declaration::OpaqueDecl(v, _) => name::dup(&v.name),
        Declaration::BasisDecl(_) => name::anonymous(),
        Declaration::IndDecl(_, _) => name::anonymous(),
    }
}

// ---------------------------------------------------------------------------
// The declared-parameter-count check (`Env.lean:550-588`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:550-553 Expr.piSortTeleLen?
/// The length of a syntactic Π-telescope ending in a `.sort`: `some n` when
/// the expression is `n` Π binders with a sort residual, `none` otherwise.
/// A spine walk — one child per step, never a tree.  The cited `.map (·+1)`
/// is a `match` (§3.4 forbids closures), and `n + 1` is checked `u64`
/// arithmetic (§3.3: an overflow is a Rust failure).
pub fn pi_sort_tele_len(e: &Expr) -> Option<u64> {
    match &e.0.kind {
        ExprKind::ForallE(_, body, _) => match pi_sort_tele_len(body) {
            Some(n) => Some(n + 1),
            None => None,
        },
        ExprKind::Sort(_) => Some(0),
        ExprKind::Bvar(_) => None,
        ExprKind::Fvar(_, _) => None,
        ExprKind::Const(_, _) => None,
        ExprKind::App(_, _) => None,
        ExprKind::Lam(_, _, _) => None,
        ExprKind::LetE(_, _, _) => None,
        ExprKind::Lit(_) => None,
        ExprKind::Proj(_, _, _) => None,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:581-588 indParamsOk
/// The stream's declared parameter count, checked as official checks it.
/// One-sided on purpose: `false` means official rejects.
pub fn ind_params_ok(n_p: u64, block: &Vec<ConstantInfo>) -> bool {
    ind_params_ok_from(n_p, block, 0)
}

/// con-leche: ConLeche/Kernel/Env.lean:581-588 indParamsOk
/// The cited `List.all`'s predicate, at one member: a former whose declared
/// type is a Π-telescope ending in a sort and shorter than `nP` is one
/// official cannot peel `nP` binders off; any other residual is left to the
/// install stages; a constructor must declare exactly `nP`.
pub fn ind_params_ok_one(n_p: u64, ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::IndInfo(cv_t, _) => match pi_sort_tele_len(&cv_t.ty) {
            Some(n) => n_p <= n,
            None => true,
        },
        ConstantInfo::CtorInfo(_, n_pc, _) => *n_pc == n_p,
        ConstantInfo::AxiomInfo(_) => true,
        ConstantInfo::DefnInfo(_, _, _) => true,
        ConstantInfo::ThmInfo(_, _) => true,
        ConstantInfo::RecInfo(_, _, _, _) => true,
        ConstantInfo::ProjInfo(_) => true,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:581-588 indParamsOk
/// The index recursion the cited `List.all` becomes (task #3's pattern).
pub fn ind_params_ok_from(n_p: u64, block: &Vec<ConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if ind_params_ok_one(n_p, &block[i]) {
        ind_params_ok_from(n_p, block, i + 1)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The reserved names (`Env.lean:596-602`)
// ---------------------------------------------------------------------------

/// con-leche: none — the `"proj"` string literal of `projFnName`
/// The code points of `"proj"` (cf. `level::is_proj_str`, the test side).
const PROJ_STR: [u32; 4] = [112, 114, 111, 106];

/// con-leche: none — the `"projTable"` string literal of `projTableName`
/// The code points of `"projTable"` (cf. `level::is_proj_table_str`).
const PROJ_TABLE_STR: [u32; 9] = [112, 114, 111, 106, 84, 97, 98, 108, 101];

/// con-leche: ConLeche/Kernel/Env.lean:596 projFnName
/// The public projection-*function* name for field `i` of structure `T`:
/// `(T.str "proj").num i`.
pub fn proj_fn_name(t: &Name, i: u64) -> Name {
    name::mk_num(
        name::mk_str(name::dup(t), core_types::code_points(&PROJ_STR)),
        i,
    )
}

/// con-leche: ConLeche/Kernel/Env.lean:602 projTableName
/// The reserved name of structure `T`'s projection table:
/// `(T.str "projTable").num 0`.
pub fn proj_table_name(t: &Name) -> Name {
    name::mk_num(
        name::mk_str(name::dup(t), core_types::code_points(&PROJ_TABLE_STR)),
        0,
    )
}

// ---------------------------------------------------------------------------
// `ConstantInfo`'s accessors (`Env.lean:606-620`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:606-609 ConstantInfo.toConstantVal
/// The common header of a stored constant.  A projection table is not a
/// term, so its header carries the closed dummy type `Sort 1`
/// (`.sort (.succ .zero)`) under the reserved name.
///
/// Deviation: Lean *shares* the stored record, Rust copies it
/// (`constant_val_dup`, a `Vec<Name>` spine).  The two accessors below
/// therefore do **not** go through this function, as the Lean's do: they
/// match directly, so a lookup never copies a level-parameter list.
pub fn to_constant_val(c: &ConstantInfo) -> ConstantVal {
    match c {
        ConstantInfo::AxiomInfo(v) => constant_val_dup(v),
        ConstantInfo::DefnInfo(v, _, _) => constant_val_dup(v),
        ConstantInfo::ThmInfo(v, _) => constant_val_dup(v),
        ConstantInfo::IndInfo(v, _) => constant_val_dup(v),
        ConstantInfo::CtorInfo(v, _, _) => constant_val_dup(v),
        ConstantInfo::RecInfo(v, _, _, _) => constant_val_dup(v),
        ConstantInfo::ProjInfo(tbl) => ConstantVal {
            name: proj_table_name(&tbl.struct_name),
            level_params: prop_when::names_copy(&tbl.level_params),
            ty: expr::sort(level::succ(level::zero())),
        },
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:611 ConstantInfo.name
/// `c.toConstantVal.name`, spelled as a direct match (see the deviation note
/// on `to_constant_val`).
pub fn constant_info_name(c: &ConstantInfo) -> Name {
    match c {
        ConstantInfo::AxiomInfo(v) => name::dup(&v.name),
        ConstantInfo::DefnInfo(v, _, _) => name::dup(&v.name),
        ConstantInfo::ThmInfo(v, _) => name::dup(&v.name),
        ConstantInfo::IndInfo(v, _) => name::dup(&v.name),
        ConstantInfo::CtorInfo(v, _, _) => name::dup(&v.name),
        ConstantInfo::RecInfo(v, _, _, _) => name::dup(&v.name),
        ConstantInfo::ProjInfo(tbl) => proj_table_name(&tbl.struct_name),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:616-618 ConstantInfo.isTowerEntry
/// A projection table: a table, not a term.
pub fn is_tower_entry(c: &ConstantInfo) -> bool {
    match c {
        ConstantInfo::ProjInfo(_) => true,
        ConstantInfo::AxiomInfo(_) => false,
        ConstantInfo::DefnInfo(_, _, _) => false,
        ConstantInfo::ThmInfo(_, _) => false,
        ConstantInfo::IndInfo(_, _) => false,
        ConstantInfo::CtorInfo(_, _, _) => false,
        ConstantInfo::RecInfo(_, _, _, _) => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:620 ConstantInfo.type
/// `c.toConstantVal.type`, spelled as a direct match (see `to_constant_val`).
pub fn constant_info_type(c: &ConstantInfo) -> Expr {
    match c {
        ConstantInfo::AxiomInfo(v) => expr::dup(&v.ty),
        ConstantInfo::DefnInfo(v, _, _) => expr::dup(&v.ty),
        ConstantInfo::ThmInfo(v, _) => expr::dup(&v.ty),
        ConstantInfo::IndInfo(v, _) => expr::dup(&v.ty),
        ConstantInfo::CtorInfo(v, _, _) => expr::dup(&v.ty),
        ConstantInfo::RecInfo(v, _, _, _) => expr::dup(&v.ty),
        ConstantInfo::ProjInfo(_) => expr::sort(level::succ(level::zero())),
    }
}

// ---------------------------------------------------------------------------
// The environment (`Env.lean:627-645`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:627-629 Env
/// The global environment: the constants accepted so far, **newest first**.
/// Names are unique (the checker rejects duplicates), so the order is
/// irrelevant for lookup; it is kept anyway, because `FEnv`'s installation
/// counters are positions counted from the *bottom* of this list
/// (`fenv::mk_fenv_go`).
pub struct Env {
    pub consts: Vec<ConstantInfo>,
}

/// con-leche: ConLeche/Kernel/Env.lean:627-629 Env
/// The record copy.
pub fn env_dup(e: &Env) -> Env {
    Env {
        consts: constant_infos_copy(&e.consts),
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:634 Env.empty
/// The empty environment; the starting point of every checker run.
pub fn empty() -> Env {
    Env { consts: Vec::new() }
}

/// con-leche: ConLeche/Kernel/Env.lean:636-637 Env.find?
/// `env.consts.find? (·.name == n)` — the linear search over the cited list,
/// in its order (newest first), so the newest binding of a name wins.
///
/// Deviation: Lean returns `Option ConstantInfo` by sharing the stored
/// record; Rust returns a borrow of it, since a copy would be `O(size)` per
/// lookup (task #9's "Lean's sharing costs a copy").
pub fn find<'a>(env: &'a Env, n: &Name) -> Option<&'a ConstantInfo> {
    find_from(&env.consts, 0, n)
}

/// con-leche: ConLeche/Kernel/Env.lean:636-637 Env.find?
/// The index recursion the cited `List.find?` becomes (task #3's pattern);
/// the predicate is inlined because §3.4 forbids closures.
pub fn find_from<'a>(cs: &'a Vec<ConstantInfo>, i: usize, n: &Name) -> Option<&'a ConstantInfo> {
    if i >= cs.len() {
        None
    } else if name::beq(&constant_info_name(&cs[i]), n) {
        Some(&cs[i])
    } else {
        find_from(cs, i + 1, n)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:642-645 Env.findProj?
/// The projection-table entry for field `i` of `T`: the structure's table
/// (`proj_table_name T`), viewed at field `i`; `none` beyond the table's
/// field count.
pub fn find_proj(env: &Env, t: &Name, i: u64) -> Option<ProjEntry> {
    match find(env, &proj_table_name(t)) {
        Some(ConstantInfo::ProjInfo(tbl)) => {
            if i < tbl.num_fields {
                Some(proj_table_entry(tbl, i))
            } else {
                None
            }
        }
        Some(_) => None,
        None => None,
    }
}

// ---------------------------------------------------------------------------
// The block's recursor suffix, decided on the tags (`Env.lean:666-675`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:666-668 ConstantInfo.isRecInfo
/// Is this member a recursor record?
pub fn is_rec_info(c: &ConstantInfo) -> bool {
    match c {
        ConstantInfo::RecInfo(_, _, _, _) => true,
        ConstantInfo::AxiomInfo(_) => false,
        ConstantInfo::DefnInfo(_, _, _) => false,
        ConstantInfo::ThmInfo(_, _) => false,
        ConstantInfo::IndInfo(_, _) => false,
        ConstantInfo::CtorInfo(_, _, _) => false,
        ConstantInfo::ProjInfo(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:671-675 recsFormSuffix
/// Do the recursors form a suffix of the block?  The tag pass — one pass, no
/// expression compared, which is the whole point of the cited function (the
/// derived `DecidableEq (List ConstantInfo)` compares DAG-shared towers as
/// trees and exhausts memory).
pub fn recs_form_suffix(block: &Vec<ConstantInfo>) -> bool {
    recs_form_suffix_from(block, 0)
}

/// con-leche: ConLeche/Kernel/Env.lean:671-675 recsFormSuffix
/// The index recursion the cited `List` recursion becomes; the inner
/// `rest.all ConstantInfo.isRecInfo` is `all_rec_info_from`.
pub fn recs_form_suffix_from(block: &Vec<ConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info_from(block, i + 1)
    } else {
        recs_form_suffix_from(block, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:671-675 recsFormSuffix
/// The cited `rest.all ConstantInfo.isRecInfo`, as an index recursion.
pub fn all_rec_info_from(block: &Vec<ConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info_from(block, i + 1)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use crate::env;
    use crate::env::BasisKind;
    use crate::env::CheckMode;
    use crate::env::ConstantInfo;
    use crate::env::ConstantVal;
    use crate::env::ReducibilityHint;
    use crate::expr;
    use crate::level;
    use crate::name;
    use crate::name::Name;
    use crate::prop_when;

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
    fn pi_sort_tele_len_counts_binders() {
        let s = expr::sort(level::zero());
        assert_eq!(env::pi_sort_tele_len(&s), Some(0));
        let m = expr::BinderMeta {
            pw: prop_when::never(),
        };
        let p1 = expr::forall_e(expr::dup(&s), expr::dup(&s), expr::binder_meta_dup(&m));
        assert_eq!(env::pi_sort_tele_len(&p1), Some(1));
        let p2 = expr::forall_e(expr::dup(&s), expr::dup(&p1), expr::binder_meta_dup(&m));
        assert_eq!(env::pi_sort_tele_len(&p2), Some(2));
        // a non-sort residual is `none` (a constant may still unfold to one)
        let c = expr::mk_const(nm("Foo"), Vec::new());
        let pc = expr::forall_e(expr::dup(&s), expr::dup(&c), expr::binder_meta_dup(&m));
        assert_eq!(env::pi_sort_tele_len(&c), None);
        assert_eq!(env::pi_sort_tele_len(&pc), None);
    }

    #[test]
    fn ind_params_ok_is_one_sided() {
        let s = expr::sort(level::zero());
        let m = expr::BinderMeta {
            pw: prop_when::never(),
        };
        let mut former = cv("T");
        former.ty = expr::forall_e(expr::dup(&s), expr::dup(&s), expr::binder_meta_dup(&m));
        let block = vec![
            ConstantInfo::IndInfo(former, env::ind_caps_default()),
            ConstantInfo::CtorInfo(cv("T.mk"), 1, 0),
        ];
        assert!(env::ind_params_ok(1, &block));
        // the former's telescope is one binder long: 2 parameters cannot be
        // peeled, and the constructor declares 1, not 2
        assert!(!env::ind_params_ok(2, &block));
        assert!(!env::ind_params_ok(0, &block));
        // a former with a non-sort residual is left to the install stages
        let mut opaque_former = cv("U");
        opaque_former.ty = expr::mk_const(nm("Foo"), Vec::new());
        let block2 = vec![ConstantInfo::IndInfo(opaque_former, env::ind_caps_default())];
        assert!(env::ind_params_ok(7, &block2));
    }

    #[test]
    fn reserved_names_are_distinct() {
        let t = nm("Prod");
        let f0 = env::proj_fn_name(&t, 0);
        let f1 = env::proj_fn_name(&t, 1);
        let tbl = env::proj_table_name(&t);
        assert!(!name::beq(&f0, &f1));
        assert!(!name::beq(&f0, &tbl));
        assert!(name::beq(&tbl, &env::proj_table_name(&t)));
        // both shapes are the reserved ones the front door rejects
        assert!(level::name_is_proj_fn_shape(&f0));
        assert!(level::name_is_proj_fn_shape(&tbl));
        assert!(!level::name_is_proj_fn_shape(&t));
    }

    #[test]
    fn env_find_is_newest_first() {
        let e = env::Env {
            consts: vec![
                ConstantInfo::AxiomInfo(cv("b")),
                ConstantInfo::AxiomInfo(cv("a")),
            ],
        };
        assert!(env::find(&e, &nm("a")).is_some());
        assert!(env::find(&e, &nm("b")).is_some());
        assert!(env::find(&e, &nm("c")).is_none());
        assert!(env::find(&env::empty(), &nm("a")).is_none());
        // the accessors agree with `to_constant_val`
        let ci = ConstantInfo::DefnInfo(cv("d"), expr::sort(level::zero()), ReducibilityHint::Abbrev);
        assert!(name::beq(
            &env::constant_info_name(&ci),
            &env::to_constant_val(&ci).name
        ));
        assert!(expr::beq(
            &env::constant_info_type(&ci),
            &env::to_constant_val(&ci).ty
        ));
        assert!(!env::is_tower_entry(&ci));
    }

    #[test]
    fn proj_table_entry_and_find_proj() {
        let t = nm("S");
        let s = expr::sort(level::zero());
        let tbl = env::ProjTable {
            struct_name: name::dup(&t),
            level_params: Vec::new(),
            num_params: 0,
            ctor: nm("S.mk"),
            num_fields: 2,
            struct_sort: level::zero(),
            bodies: vec![expr::bvar(7), expr::bvar(8)],
            guards: vec![level::zero(), level::succ(level::zero())],
            off: 1,
        };
        let e1 = env::proj_table_entry(&tbl, 1);
        assert_eq!(e1.idx, 1);
        assert_eq!(e1.off, 1);
        assert!(expr::beq(&e1.body, &expr::bvar(8)));
        assert!(level::beq(&e1.field_sort, &level::succ(level::zero())));
        // out of range: the `getD` defaults
        let e9 = env::proj_table_entry(&tbl, 9);
        assert!(expr::beq(&e9.body, &env::default_expr()));
        assert!(level::beq(&e9.field_sort, &level::zero()));
        // the environment lookup is keyed on `projTableName`, and is `none`
        // beyond `numFields`
        let e = env::Env {
            consts: vec![ConstantInfo::ProjInfo(tbl)],
        };
        assert!(env::find_proj(&e, &t, 0).is_some());
        assert!(env::find_proj(&e, &t, 2).is_none());
        assert!(env::find_proj(&e, &nm("T"), 0).is_none());
        // and the table's own header is the dummy `Sort 1` under the
        // reserved name
        let hdr = env::to_constant_val(&e.consts[0]);
        assert!(name::beq(&hdr.name, &env::proj_table_name(&t)));
        assert!(expr::beq(&hdr.ty, &expr::sort(level::succ(level::zero()))));
        assert!(env::is_tower_entry(&e.consts[0]));
        let _ = s;
    }

    #[test]
    fn recs_form_suffix_on_tags() {
        let rec = |n: &str| ConstantInfo::RecInfo(cv(n), 0, 0, Vec::new());
        let ind = |n: &str| ConstantInfo::IndInfo(cv(n), env::ind_caps_default());
        assert!(env::recs_form_suffix(&Vec::new()));
        assert!(env::recs_form_suffix(&vec![ind("A"), rec("A.rec")]));
        assert!(env::recs_form_suffix(&vec![rec("A.rec"), rec("B.rec")]));
        assert!(!env::recs_form_suffix(&vec![rec("A.rec"), ind("B")]));
        assert!(env::recs_form_suffix(&vec![ind("A"), ind("B")]));
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
        assert!(name::beq(
            &env::constant_info_name(&ci),
            &env::constant_info_name(&c2)
        ));
        match c2 {
            ConstantInfo::RecInfo(_, mi, rp, rules) => {
                assert_eq!((mi, rp), (3, 2));
                assert_eq!(rules.len(), 1);
                // the parse placeholders (task #10, surprise 2)
                assert_eq!(rules[0].ctor_params, 0);
                assert!(!rules[0].k && !rules[0].eta && !rules[0].params_blind);
                assert!(matches!(rules[0].fire, env::RecRuleFire::Inert));
                // `.inert` compares parameters
                assert!(env::rec_rule_compare_params(&rules[0]));
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
        let d = env::Declaration::BasisDecl(BasisKind::NatK);
        assert!(name::beq(&env::declaration_name(&d), &name::anonymous()));
        let d2 = env::Declaration::ThmDecl(cv("t"), expr::bvar(0));
        assert!(name::beq(&env::declaration_name(&d2), &nm("t")));
        let e = env::Env {
            consts: vec![ConstantInfo::AxiomInfo(cv("x"))],
        };
        assert_eq!(env::env_dup(&e).consts.len(), 1);
        assert!(matches!(
            env::basis_kind_dup(&BasisKind::QuotK),
            BasisKind::QuotK
        ));
        assert!(matches!(
            env::check_mode_dup(&CheckMode::Trusted),
            CheckMode::Trusted
        ));
    }
}
