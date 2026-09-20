//! `arena::inductives::ind_base` — P4d-1's checker helpers, borrowed.
//!
//! **This module is not one of the eleven, and every item in it is a
//! duplicate to be deleted when P4d-1's Rust lands.**
//!
//! Its twins are `proof/ConRon/Arena/{CheckerBase,Intern,StdAxioms}.lean`'s —
//! the Lean side had the same problem and solved it the same way.  The
//! inductive installs of `ConLeche/Kernel/Inductives/*` call two dozen
//! declarations that belong to `ConLeche/Kernel/{CheckerBase,Env,Level}.lean`,
//! i.e. to the SIBLING task (P4d-1: `arena::{checker_base, decl_check,
//! checker, canon, basis, std_axioms}`).  The two halves of P4d run at the
//! same time, so — per the coordinator's concurrency contract — the twins
//! those installs need are written here, cited to the same con-leche
//! declarations P4d-1 cites, in a module of their own so that nothing clashes
//! at merge.  DESIGN.md's task section carries the map; the call sites are
//! then a `sed` of `ind_base::` away.
//!
//! The Lean's own borrowed copy was `Arena/Inductives/Base.lean`, and task
//! #97f deleted it: its twenty-four declarations are now
//! `Arena/CheckerBase.lean`'s (`unwrapOr`, `nameNodup`, the two name-shape
//! readers, `allLevelParamsDefined`, `constsResolveFFast`, `fvarTypeDs`,
//! `openPisAtFvars`/`…FGo`/`…F`, `domsMatchAux`, `unresolvedConstsError`,
//! `checkConstantVal`, `checkTypedList`, `checkAnnotList`, `checkDefEqList`,
//! `isEqHead`, `eqHeadLevel`, `IFEnv.findCV?`, `checkProjShape`,
//! `checkProjRule`, `isRecInfo`, `recsFormSuffix`, `indParamsOk`) and
//! `Arena/Inductives/Modeled.lean`'s (`domsMatchRenamed`, `eqBasisStored` —
//! which live in `arena::inductives::modeled` here, as they do there).  **This
//! module mirrors that final Lean**, one function per declaration, so the
//! dedup is a move and not a rewrite.
//!
//! Three groups of items here are not `CheckerBase.lean`'s, and each is
//! borrowed from a different neighbour:
//!
//! * the `*_beq` family (`i_constant_info_beq` and its five helpers) is
//!   `arena::env`'s — `proof/ConRon/Arena/Env.lean` writes `deriving
//!   DecidableEq` on all seven records and the Rust of `env.rs` (task #97e)
//!   has the `*_dup`s but not the comparisons.  `eq_basis_stored` needs one,
//!   and so does the differential test;
//! * `ifenv_dup` / `i_env_dup` / `impl Dup for IConstantInfo` are `arena::env`'s
//!   too: Lean's value semantics copies a record for free and `checkIndRecs`
//!   uses `fe₂` four times, which is exactly where
//!   `con_ron_core::kernel::fenv::dup` is called on the tree-shaped side;
//! * `intern_expr` / `intern_cv` / `intern_caps` / `intern_levels_l` are
//!   `Arena/Intern.lean`'s converters, which turn a `con_ron_core` VALUE into
//!   handles.  They exist here for one caller: the pinned annotated `Eq` basis
//!   constant, the comparand of the modeled route's three "requires the pinned
//!   `Eq` basis" guards.
//!
//! **The one judgement call.**  `checkIndRecs` and `checkProjLookups` ask
//! `env.find? eqName = some eqA` — the stored `Eq` must BE the pinned basis
//! constant.  P4d-1's `arena::std_axioms` owns the arena's `eqA` (the Lean's
//! `Arena/StdAxioms.lean:136` is `internCI ConLeche.eqA`); until it lands,
//! `eq_basis_ci` INTERNS `con_ron_core`'s own value
//! (`kernel::basis_pins::eq_a`), which is the same value through the same
//! store, hence the same handle (`denoteE`/`denoteN` are injective, task
//! #97a).  Weakening the guard to "some `Eq` is stored" would make the arena
//! ACCEPT blocks con-leche rejects, which no placeholder may do, and failing
//! closed would decline every modelled recursor.
//!
//! Messages are `con_ron_core`'s own code-point constants with the
//! interpolation dropped, as task #97-P4c's table rules: §3.1 says a message
//! need not match a theorem, and matching *con-ron-core's* is what lets the
//! differential test compare error text.

use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{
    IConstantInfo, IConstantVal, IFEnv, IIndCaps, IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{
    fail, intern_e, intern_level, intern_levels, intern_n_node, intern_name, view, view_ls, AState,
};
use crate::arena::store::{ENodeView, NNodeView};
use con_ron_core::kernel::basis_names;
use con_ron_core::kernel::basis_pins;
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::{CheckMode, ConstantInfo, ConstantVal, IndCaps};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Expr, ExprView};
use con_ron_core::kernel::expr_ops::sub_nat;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap};

// ---------------------------------------------------------------------------
// The messages (con-ron-core's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'fuel exhausted: allLevelParamsDefined'`, as code points.
pub const M_FUEL_ALPD: [u32; 37] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 108, 108, 76,
    101, 118, 101, 108, 80, 97, 114, 97, 109, 115, 68, 101, 102, 105, 110, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'fuel exhausted: constsResolveF'`, as code points.
pub const M_FUEL_CRF: [u32; 30] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 111, 110, 115,
    116, 115, 82, 101, 115, 111, 108, 118, 101, 70,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'duplicate declaration'`, as code points.
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
    110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'reserved basis name'`, as code points.
pub const M_RESERVED_BASIS: [u32; 19] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'reserved projection name'`, as code points.
pub const M_RESERVED_PROJ: [u32; 24] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
    32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'duplicate universe parameters in declaration'`, as code points.
pub const M_DUP_UNIV: [u32; 44] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97,
    116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'loose bound variable in type'`, as code points.
pub const M_LOOSE_BVAR: [u32; 28] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101,
    32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'unexpected free variable in type'`, as code points.
pub const M_FREE_VAR: [u32; 32] = [
    117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105,
    97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'undeclared universe parameter in type'`, as code points.
pub const M_UNDECL_UNIV: [u32; 37] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'nested pin type mismatch'`, as code points.
pub const M_NESTED_TYPE: [u32; 24] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 116, 121, 112, 101, 32, 109, 105, 115,
    109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'nested pin arity mismatch'`, as code points.
pub const M_NESTED_ARITY: [u32; 25] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 114, 105, 116, 121, 32, 109, 105, 115,
    109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'nested pin annotation mismatch'`, as code points.
pub const M_NESTED_ANNOT: [u32; 30] = [
    110, 101, 115, 116, 101, 100, 32, 112, 105, 110, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111,
    110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'iota statement component mismatch'`, as code points.
pub const M_IOTA_COMP: [u32; 33] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111,
    110, 101, 110, 116, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'iota statement component arity'`, as code points.
pub const M_IOTA_COMP_ARITY: [u32; 30] = [
    105, 111, 116, 97, 32, 115, 116, 97, 116, 101, 109, 101, 110, 116, 32, 99, 111, 109, 112, 111,
    110, 101, 110, 116, 32, 97, 114, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection type telescope'`, as code points.
pub const M_PROJ_TY_TELE: [u32; 25] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection constructor telescope'`, as code points.
pub const M_PROJ_CTOR_TELE: [u32; 32] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection constructor residual arity'`, as code points.
pub const M_PROJ_RESID_ARITY: [u32; 37] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 97, 114, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection constructor residual head'`, as code points.
pub const M_PROJ_RESID_HEAD: [u32; 36] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116,
    111, 114, 32, 114, 101, 115, 105, 100, 117, 97, 108, 32, 104, 101, 97, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection rule telescope'`, as code points.
pub const M_PROJ_RULE_TELE: [u32; 25] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 116, 101, 108,
    101, 115, 99, 111, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection rule scoping'`, as code points.
pub const M_PROJ_RULE_SCOPE: [u32; 23] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 115, 99, 111, 112,
    105, 110, 103,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection rule wellformedness'`, as code points.
pub const M_PROJ_RULE_WF: [u32; 30] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 119, 101, 108,
    108, 102, 111, 114, 109, 101, 100, 110, 101, 115, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection rule body'`, as code points.
pub const M_PROJ_RULE_BODY: [u32; 20] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 98, 111, 100, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'projection rule domain mismatch'`, as code points.
pub const M_PROJ_RULE_DOMS: [u32; 31] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 114, 117, 108, 101, 32, 100, 111, 109, 97,
    105, 110, 32, 109, 105, 115, 109, 97, 116, 99, 104,
];

// ---------------------------------------------------------------------------
// `Option` unwrapping (`Arena/CheckerBase.lean:472-475`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:233-239 unwrapOr
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:472-475 unwrapOr` —
/// unwrap an optional value or fail with the given error.
pub fn unwrap_or<T>(o: Option<T>, err: CheckError) -> Result<T, CheckError> {
    match o {
        Some(a) => Ok(a),
        None => fail(err),
    }
}

// ---------------------------------------------------------------------------
// Level parameters (`Arena/CheckerBase.lean:149-232`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:151-153 nameNodup` — are
/// the names pairwise distinct?  Over handles a name comparison is a handle
/// comparison (`denoteN` is injective, task #97a).
pub fn nidx_nodup(ns: &Vec<NIdx>) -> bool {
    nidx_nodup_from(ns, 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:151-153 nameNodup` — the
/// cursor recursion behind `nidx_nodup`.
pub fn nidx_nodup_from(ns: &Vec<NIdx>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if nidx_contains_from(ns, i + 1, &ns[i]) {
        false
    } else {
        nidx_nodup_from(ns, i + 1)
    }
}

/// con-leche: none — `ns.contains n` over a `Vec<NIdx>` tail
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:153 nameNodup` — the
/// `!ns.contains n` of the cited clause, at a cursor rather than a tail.
pub fn nidx_contains_from(ns: &Vec<NIdx>, i: usize, n: &NIdx) -> bool {
    if i >= ns.len() {
        false
    } else if ns[i].eq2(n) {
        true
    } else {
        nidx_contains_from(ns, i + 1, n)
    }
}

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:197 allLevelParamsDefinedGo`
/// — the `memo[h]?` probe of the two node-keyed walks of this module.
pub fn bool_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:193-226 allLevelParamsDefinedGo`
/// — are all level parameters occurring in `e` among `params` (binder
/// prop-ness data included)?  con-leche's pure walk and its memoized twin are
/// one function here (task #97b's rule); the levels are READ BACK and
/// con-leche's own `Level.allParamsDefined` / `PropWhen.paramsDefined` decide
/// them (DESIGN.md §8.3 lesson 4), and the memo is con-leche's own per-call
/// table keyed by the node — `params` is fixed for the walk.
///
/// The twin probes the memo FIRST, before the `view`, and records EVERY
/// constructor: a shared leaf then costs one probe rather than one readback.
pub fn all_level_params_defined_go(
    st: &mut AState,
    ks: &Vec<con_ron_core::kernel::name::Name>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ALPD)))
    } else {
        match bool_probe(&memo, h) {
            Some(r) => Ok((r, memo)),
            None => match view(st, h) {
                Err(e) => Err(e),
                Ok(v) => match all_level_params_defined_node(st, ks, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, bool> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:199-225 allLevelParamsDefinedGo`
/// — the walk's arms, split off so that the `view`'s loans are dead at the
/// memo's join (task #97-P4c's extraction rule 5).
pub fn all_level_params_defined_node(
    st: &mut AState,
    ks: &Vec<con_ron_core::kernel::name::Name>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::BVar(_) => Ok((true, memo)),
        ENodeView::Lit(_) => Ok((true, memo)),
        ENodeView::Sort(u) => match crate::arena::monad::read_level(st, &u) {
            Err(e) => Err(e),
            Ok(l) => Ok((level::all_params_defined(ks, &l), memo)),
        },
        ENodeView::Const(_, us) => match crate::arena::monad::read_levels(st, &us) {
            Err(e) => Err(e),
            Ok(ls) => Ok((levels_all_params_defined(ks, &ls, 0), memo)),
        },
        ENodeView::FVar(_, t) => all_level_params_defined_go(st, ks, memo, fuel, &t),
        ENodeView::App(f, a) => match all_level_params_defined_go(st, ks, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((false, m)) => Ok((false, m)),
            Ok((true, m)) => all_level_params_defined_go(st, ks, m, fuel, &a),
        },
        ENodeView::Lam(t, b, m0) => {
            all_level_params_defined_binder(st, ks, memo, fuel, &t, &b, &m0)
        }
        ENodeView::ForallE(t, b, m0) => {
            all_level_params_defined_binder(st, ks, memo, fuel, &t, &b, &m0)
        }
        ENodeView::LetE(t, val, b) => match all_level_params_defined_go(st, ks, memo, fuel, &t) {
            Err(e) => Err(e),
            Ok((false, m)) => Ok((false, m)),
            Ok((true, m)) => match all_level_params_defined_go(st, ks, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((false, m2)) => Ok((false, m2)),
                Ok((true, m2)) => all_level_params_defined_go(st, ks, m2, fuel, &b),
            },
        },
        ENodeView::Proj(_, _, e) => all_level_params_defined_go(st, ks, memo, fuel, &e),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:213-217 allLevelParamsDefinedGo`
/// — the two binder arms, which the twin writes as one `|`-pattern: the
/// domain, the body, and the binder's own prop-ness datum.
pub fn all_level_params_defined_binder(
    st: &mut AState,
    ks: &Vec<con_ron_core::kernel::name::Name>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    t: &EIdx,
    b: &EIdx,
    m0: &BinderMeta,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match all_level_params_defined_go(st, ks, memo, fuel, t) {
        Err(e) => Err(e),
        Ok((false, m)) => Ok((false, m)),
        Ok((true, m)) => match all_level_params_defined_go(st, ks, m, fuel, b) {
            Err(e) => Err(e),
            Ok((b2, m2)) => Ok((b2 && prop_when::params_defined(ks, &m0.pw), m2)),
        },
    }
}

/// con-leche: none — `us.all (Level.allParamsDefined ks)` over a `Vec<Level>`
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:207 allLevelParamsDefinedGo`
/// — the cursor recursion behind the `const` arm's `List.all`.
pub fn levels_all_params_defined(
    ks: &Vec<con_ron_core::kernel::name::Name>,
    us: &Vec<Level>,
    i: usize,
) -> bool {
    if i >= us.len() {
        true
    } else if level::all_params_defined(ks, &us[i]) {
        levels_all_params_defined(ks, us, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:230-232 allLevelParamsDefined`
/// — the executed `allLevelParamsDefined` (one memoized DAG walk).
pub fn all_level_params_defined(
    st: &mut AState,
    params: &Vec<NIdx>,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match crate::arena::monad::read_names(st, params) {
        Err(er) => Err(er),
        Ok(ks) => match all_level_params_defined_go(st, &ks, HashMap::new(), CORE_WALK_FUEL, e) {
            Err(er) => Err(er),
            Ok(r) => Ok(r.0),
        },
    }
}

// ---------------------------------------------------------------------------
// The memoized resolution walk (`Arena/CheckerBase.lean:250-296`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:37-58 Expr.constsResolveF
/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:250-280 constsResolveFGo` —
/// the memoized resolution walk.  The leaf clauses are `arena::core`'s
/// `consts_resolve` at ONE node, exactly as con-leche's `…Go` calls the pure
/// walk at its four non-recursive constructors.  **P4d-1's; borrowed** (the
/// module note).
pub fn consts_resolve_f_go(
    st: &mut AState,
    fe: &IFEnv,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CRF)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => consts_resolve_leaf(st, fe, memo, h),
            Ok(ENodeView::Sort(_)) => consts_resolve_leaf(st, fe, memo, h),
            Ok(ENodeView::Lit(_)) => consts_resolve_leaf(st, fe, memo, h),
            Ok(ENodeView::Const(_, _)) => consts_resolve_leaf(st, fe, memo, h),
            Ok(v) => match bool_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match consts_resolve_f_node(st, fe, memo, fuel - 1, h, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => {
                        let mut m2: HashMap<EIdx, bool> = m;
                        m2.insert(h.dup2(), r);
                        Ok((r, m2))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:256-257 constsResolveFGo` —
/// the four non-recursive constructors, answered by the pure walk at one node.
pub fn consts_resolve_leaf(
    st: &mut AState,
    fe: &IFEnv,
    memo: HashMap<EIdx, bool>,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match core::consts_resolve(st, fe, CORE_WALK_FUEL, h) {
        Err(e) => Err(e),
        Ok(r) => Ok((r, memo)),
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:89-124 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:262-278 constsResolveFGo` —
/// the walk's compound arms, split off so that the `view`'s loans are dead at
/// the memo's join (extraction rule 5).
pub fn consts_resolve_f_node(
    st: &mut AState,
    fe: &IFEnv,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(_, ty) => consts_resolve_f_go(st, fe, memo, fuel, &ty),
        ENodeView::App(f, a) => match consts_resolve_f_go(st, fe, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((b1, m)) => match consts_resolve_f_go(st, fe, m, fuel, &a) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 && b2, m2)),
            },
        },
        ENodeView::Lam(ty, body, _) => match consts_resolve_f_go(st, fe, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match consts_resolve_f_go(st, fe, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 && b2, m2)),
            },
        },
        ENodeView::ForallE(ty, body, _) => match consts_resolve_f_go(st, fe, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match consts_resolve_f_go(st, fe, m, fuel, &body) {
                Err(e) => Err(e),
                Ok((b2, m2)) => Ok((b1 && b2, m2)),
            },
        },
        ENodeView::LetE(ty, val, body) => match consts_resolve_f_go(st, fe, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((b1, m)) => match consts_resolve_f_go(st, fe, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((b2, m2)) => match consts_resolve_f_go(st, fe, m2, fuel, &body) {
                    Err(e) => Err(e),
                    Ok((b3, m3)) => Ok((b1 && b2 && b3, m3)),
                },
            },
        },
        ENodeView::Proj(s, _, sub) => match consts_resolve_f_go(st, fe, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok((b, m)) => Ok((env::ifenv_find(fe, &s).is_some() && b, m)),
        },
        _ => consts_resolve_leaf(st, fe, memo, h),
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:197-199 Expr.constsResolveFFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:285-286 constsResolveFFast`
/// — the executed `constsResolve` (one memoized DAG walk), which is what every
/// front door below calls.  **P4d-1's; borrowed.**
pub fn consts_resolve_f_fast(st: &mut AState, fe: &IFEnv, e: &EIdx) -> Result<bool, CheckError> {
    match consts_resolve_f_go(st, fe, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: none — `xs.map Expr.fvarTypeD` over a list of handles
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:291-296 fvarTypeDs` —
/// DESIGN.md §3.4 forbids the closure `List.map` takes.  **P4d-1's;
/// borrowed.**
pub fn fvar_type_ds(st: &AState, fvs: &Vec<EIdx>) -> Result<Vec<EIdx>, CheckError> {
    fvar_type_ds_from(st, fvs, 0, Vec::new())
}

/// con-leche: none — `xs.map Expr.fvarTypeD` over a list of handles
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:291-296 fvarTypeDs` — the
/// cursor recursion behind `fvar_type_ds`.
pub fn fvar_type_ds_from(
    st: &AState,
    fvs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= fvs.len() {
        Ok(out)
    } else {
        match expr_ops::fvar_type_d(st, &fvs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut o: Vec<EIdx> = out;
                o.push(t);
                fvar_type_ds_from(st, fvs, i + 1, o)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Telescopes opened at free variables (`Arena/CheckerBase.lean:375-413`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:130-140 openPisAtFvars
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:375-389 openPisAtFvars`
/// — open the first `n` `∀`-binders at fresh free variables `0..n-1` (each
/// fvar's type is the binder domain, instantiated with the earlier fvars).
pub fn open_pis_at_fvars(
    st: &mut AState,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => match intern_e(st, ENodeView::FVar(i, dom)) {
                Err(e) => Err(e),
                Ok(fv) => match expr_ops::instantiate1_fast(st, CORE_WALK_FUEL, &body, &fv, 0) {
                    Err(e) => Err(e),
                    Ok(b) => match open_pis_at_fvars(st, n - 1, &b, i + 1) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some(p)) => Ok(Some((expr_ops::cons_eidx(&fv, &p.0), p.1))),
                    },
                },
            },
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:153-167 openPisAtFvarsFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:391-405 openPisAtFvarsFGo`
/// — the core of the one-pass opening: `acc` holds the already-created fvars,
/// innermost binder first.
pub fn open_pis_at_fvars_f_go(
    st: &mut AState,
    acc: &Vec<EIdx>,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        match expr_ops::instantiate_list_fast(st, CORE_WALK_FUEL, h, acc, 0) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some((Vec::new(), r))),
        }
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => {
                match expr_ops::instantiate_list_fast(st, CORE_WALK_FUEL, &dom, acc, 0) {
                    Err(e) => Err(e),
                    Ok(d) => match intern_e(st, ENodeView::FVar(i, d)) {
                        Err(e) => Err(e),
                        Ok(fv) => {
                            let acc2: Vec<EIdx> = expr_ops::cons_eidx(&fv, acc);
                            match open_pis_at_fvars_f_go(st, &acc2, n - 1, &body, i + 1) {
                                Err(e) => Err(e),
                                Ok(None) => Ok(None),
                                Ok(Some(p)) => Ok(Some((expr_ops::cons_eidx(&fv, &p.0), p.1))),
                            }
                        }
                    },
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:169-176 openPisAtFvarsF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:407-413 openPisAtFvarsF`
/// — one-pass `openPisAtFvars`; the fallback covers telescopes whose binders
/// only appear after substitution.
pub fn open_pis_at_fvars_f(
    st: &mut AState,
    n: u64,
    e: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    let acc: Vec<EIdx> = Vec::new();
    match open_pis_at_fvars_f_go(st, &acc, n, e, i) {
        Err(er) => Err(er),
        Ok(Some(r)) => Ok(Some(r)),
        Ok(None) => open_pis_at_fvars(st, n, e, i),
    }
}

// ---------------------------------------------------------------------------
// Binder-domain comparisons (`Arena/CheckerBase.lean:365-373`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// con-leche: ConLeche/Kernel/CheckerBase.lean:142-151 domsMatchAuxA
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:365-373 domsMatchAux` —
/// compare binder domains at offsets `o₁`/`o₂` for `n` positions, at the
/// IDENTITY view.  con-leche's `List` version is quadratic on a wide telescope
/// and its `Array` twin is what the checker runs, so the twin is the array one
/// — and over a `Vec` there is nothing left to distinguish.  Over handles a
/// domain comparison is a handle comparison, so this is PURE.
pub fn doms_match_aux(
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
) -> bool {
    doms_match_aux_from(bs1, bs2, o1, o2, n, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:121-128 domsMatchAux
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:366-369 domsMatchAux` — the
/// `(List.range n).all` of the cited function as a cursor recursion.
pub fn doms_match_aux_from(
    bs1: &Vec<(EIdx, BinderMeta)>,
    bs2: &Vec<(EIdx, BinderMeta)>,
    o1: u64,
    o2: u64,
    n: u64,
    i: u64,
) -> bool {
    if i >= n {
        true
    } else {
        let j1: u64 = o1 + i;
        let j2: u64 = o2 + i;
        if j1 >= bs1.len() as u64 || j2 >= bs2.len() as u64 {
            false
        } else if bs1[j1 as usize].0.eq2(&bs2[j2 as usize].0) {
            doms_match_aux_from(bs1, bs2, o1, o2, n, i + 1)
        } else {
            false
        }
    }
}

// ---------------------------------------------------------------------------
// The name shapes, read off the HANDLE (`Arena/CheckerBase.lean:151-172`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:218-221 Name.isModelSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:157-161 NIdx.isModelSuffix`
/// — is this a `_model`-suffixed name (the shape of model companions)?  One
/// `viewN`, no readback.
pub fn nidx_is_model_suffix(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    match crate::arena::monad::view_n(st, n) {
        Err(e) => Err(e),
        Ok(NNodeView::Str(_, s)) => {
            Ok(con_ron_core::kernel::name::str_eq(&s, &code_points(&MODEL)))
        }
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:166-174 NIdx.isProjFnShape`
/// — is this shaped like an installed projection function's name (`(T.proj).i`)
/// or a projection table's (`(T.projTable).0`)?  Both shapes are reserved for
/// the checker's own installs.  Two `viewN`s, no readback.
pub fn nidx_is_proj_fn_shape(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    const PROJ: [u32; 4] = [112, 114, 111, 106];
    const TBL: [u32; 9] = [112, 114, 111, 106, 84, 97, 98, 108, 101];
    match crate::arena::monad::view_n(st, n) {
        Err(e) => Err(e),
        Ok(NNodeView::Num(p, _)) => match crate::arena::monad::view_n(st, &p) {
            Err(e) => Err(e),
            Ok(NNodeView::Str(_, s)) => {
                Ok(con_ron_core::kernel::name::str_eq(&s, &code_points(&PROJ))
                    || con_ron_core::kernel::name::str_eq(&s, &code_points(&TBL)))
            }
            Ok(_) => Ok(false),
        },
        Ok(_) => Ok(false),
    }
}

// ---------------------------------------------------------------------------
// The declaration front door (`Arena/CheckerBase.lean:315-353`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:71-91 unresolvedConstsError
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:315-319 unresolvedConstsError`
/// — **the verdict at a term whose constants do not all resolve**: a term that
/// mentions `sorryAx` DECLINES, anything else REJECTS as an unknown constant.
/// The cited `where_ : String` only names the slot in the message, and §3.1
/// says messages need not match, so the port takes no such argument — which is
/// `con_ron_core::kernel::checker_base::unresolved_consts_error`'s own choice.
pub fn unresolved_consts_error(st: &mut AState, e: &EIdx) -> Result<CheckError, CheckError> {
    match core::pin(st, &basis_names::sorry_ax_name()) {
        Err(er) => Err(er),
        Ok(sa) => match super::struct_parts::mentions_const(st, &sa, e) {
            Err(er) => Err(er),
            Ok(true) => Ok(core_types::not_implemented(code_points(&core::M_SORRY))),
            Ok(false) => Ok(core_types::invalid(code_points(&core::M_UNKNOWN_CONST))),
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:332-353 checkConstantVal`
/// — checks common to all declarations: fresh name, well-formed universe
/// parameters, and a type that is a type and mentions only declared
/// parameters.  Returns the constant with its type **annotated**.
///
/// The twin's `if … then fail` sequence is an `else if` chain here, which is
/// the same control flow: in `do`-notation a `fail` throws, so the next test
/// runs only when the previous one did not fire.
pub fn check_constant_val(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    if env::ifenv_find(fe, &cv.name).is_some() {
        fail(core_types::invalid(code_points(&M_DUP_DECL)))
    } else {
        match core::reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(reserved) => {
                if env::nidx_vec_contains(&reserved, &cv.name) {
                    fail(core_types::invalid(code_points(&M_RESERVED_BASIS)))
                } else {
                    match nidx_is_proj_fn_shape(st, &cv.name) {
                        Err(e) => Err(e),
                        Ok(true) => fail(core_types::invalid(code_points(&M_RESERVED_PROJ))),
                        Ok(false) => {
                            if !nidx_nodup(&cv.level_params) {
                                fail(core_types::invalid(code_points(&M_DUP_UNIV)))
                            } else {
                                check_constant_val_scoped(st, mode, fe, cv)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:342-346 checkConstantVal`
/// — the scoping guards on the DECLARED type, then the annotation.
pub fn check_constant_val_scoped(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<IConstantVal, CheckError> {
    match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, &cv.ty) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_LOOSE_BVAR))),
        Ok(true) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &cv.ty) {
            Err(e) => Err(e),
            Ok(true) => fail(core_types::invalid(code_points(&M_FREE_VAR))),
            Ok(false) => match core::annotate_core(st, mode, fe, core::CHECK_FUEL, 0, &cv.ty) {
                Err(e) => Err(e),
                Ok(ty) => check_constant_val_after_annot(st, mode, fe, cv, ty),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:95-119 checkConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:347-353 checkConstantVal`
/// — the tail past the annotation: the level-parameter and resolution guards
/// on the ANNOTATED type, the type's own sort, and the record update
/// `{ cv with type := type }`.
pub fn check_constant_val_after_annot(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
    ty: EIdx,
) -> Result<IConstantVal, CheckError> {
    match all_level_params_defined(st, &cv.level_params, &ty) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::invalid(code_points(&M_UNDECL_UNIV))),
        Ok(true) => match consts_resolve_f_fast(st, fe, &ty) {
            Err(e) => Err(e),
            Ok(false) => match unresolved_consts_error(st, &ty) {
                Err(e) => Err(e),
                Ok(er) => fail(er),
            },
            Ok(true) => match core::infer_type_core(st, mode, fe, core::CHECK_FUEL, 0, &ty) {
                Err(e) => Err(e),
                Ok(stype) => {
                    match core::ensure_sort_core(st, mode, fe, core::CHECK_FUEL, 0, &stype) {
                        Err(e) => Err(e),
                        Ok(_u) => Ok(IConstantVal {
                            name: cv.name.dup2(),
                            level_params: env::nidx_vec_dup(&cv.level_params),
                            ty,
                        }),
                    }
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The list checks (`Arena/CheckerBase.lean:416-470`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:416-424 checkTypedList`
/// — check each expression's inferred type against the corresponding expected
/// type (definitionally); throws on a length mismatch.
pub fn check_typed_list(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ts: &Vec<EIdx>,
) -> Result<(), CheckError> {
    if xs.len() != ts.len() {
        fail(core_types::not_implemented(code_points(&M_NESTED_ARITY)))
    } else {
        check_typed_list_from(st, mode, fe, depth, xs, ts, 0)
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:178-190 checkTypedList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:418-423 checkTypedList`
/// — the cursor recursion behind `check_typed_list`.
pub fn check_typed_list_from(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ts: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() {
        Ok(())
    } else {
        let a: EIdx = xs[i].dup2();
        match core::infer_type_core(st, mode, fe, core::CHECK_FUEL, depth, &a) {
            Err(e) => Err(e),
            Ok(ty) => {
                let t: EIdx = ts[i].dup2();
                match core::is_def_eq_core(st, mode, fe, core::CHECK_FUEL, depth, &ty, &t) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::not_implemented(code_points(&M_NESTED_TYPE))),
                    Ok(true) => check_typed_list_from(st, mode, fe, depth, xs, ts, i + 1),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:429-438 checkAnnotList`
/// — check that each expression is a fixed point of the annotation pass in the
/// given context.
pub fn check_annot_list(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
) -> Result<(), CheckError> {
    check_annot_list_from(st, mode, fe, depth, xs, 0)
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:192-206 checkAnnotList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:432-438 checkAnnotList`
/// — the cursor recursion behind `check_annot_list`.
pub fn check_annot_list_from(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() {
        Ok(())
    } else {
        let a: EIdx = xs[i].dup2();
        match core::annotate_core(st, mode, fe, core::CHECK_FUEL, depth, &a) {
            Err(e) => Err(e),
            Ok(a_a) => {
                if a_a.eq2(&a) {
                    check_annot_list_from(st, mode, fe, depth, xs, i + 1)
                } else {
                    fail(core_types::not_implemented(code_points(&M_NESTED_ANNOT)))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:461-470 checkDefEqList`
/// — pairwise definitional-equality check of two spines (throws on any
/// mismatch, including a length difference).
pub fn check_def_eq_list(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
) -> Result<(), CheckError> {
    if xs.len() != ys.len() {
        fail(core_types::not_implemented(code_points(&M_IOTA_COMP_ARITY)))
    } else {
        check_def_eq_list_from(st, mode, fe, depth, xs, ys, 0)
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:222-231 checkDefEqList
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:464-469 checkDefEqList`
/// — the cursor recursion behind `check_def_eq_list`.
pub fn check_def_eq_list_from(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= xs.len() {
        Ok(())
    } else {
        let a: EIdx = xs[i].dup2();
        let b: EIdx = ys[i].dup2();
        match core::is_def_eq_core(st, mode, fe, core::CHECK_FUEL, depth, &a, &b) {
            Err(e) => Err(e),
            Ok(false) => fail(core_types::not_implemented(code_points(&M_IOTA_COMP))),
            Ok(true) => check_def_eq_list_from(st, mode, fe, depth, xs, ys, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// The pinned equality former (`Arena/CheckerBase.lean:440-459`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:208-211 isEqHead
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:440-448 isEqHead` — is
/// the expression the pinned equality former at one level?
pub fn is_eq_head(st: &mut AState, h: &EIdx) -> Result<bool, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(c, us)) => match core::pin(st, &basis_names::eq_name()) {
            Err(e) => Err(e),
            Ok(en) => {
                if c.eq2(&en) {
                    match view_ls(st, &us) {
                        Err(e) => Err(e),
                        Ok(ls) => Ok(ls.len() == 1),
                    }
                } else {
                    Ok(false)
                }
            }
        },
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:213-220 eqHeadLevel
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:450-459 eqHeadLevel` —
/// the level an equality head carries.  Off shape it is `.zero`, which
/// `isEqHead` has already rejected wherever the result is used.
pub fn eq_head_level(st: &mut AState, h: &EIdx) -> Result<LIdx, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(_, us)) => match view_ls(st, &us) {
            Err(e) => Err(e),
            Ok(ls) => {
                if ls.len() == 1 {
                    Ok(ls[0].dup2())
                } else {
                    core::zero_level(st)
                }
            }
        },
        Ok(_) => core::zero_level(st),
    }
}

// ---------------------------------------------------------------------------
// Reading a stored constant (`Arena/CheckerBase.lean:480-485`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:241-247 Env.findCV?
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:480-485 IFEnv.findCV?` — the
/// stored constant under `n`, as an `IConstantVal`, if any.  The stored record
/// is COPIED before the state is taken mutably (task #97-P4c's row for
/// `IConstantInfo` read out of `fe.find?`).
pub fn find_cv(st: &mut AState, fe: &IFEnv, n: &NIdx) -> Result<Option<IConstantVal>, CheckError> {
    let found: Option<IConstantInfo> = match env::ifenv_find(fe, n) {
        Some(ci) => Some(env::i_constant_info_dup(ci)),
        None => None,
    };
    match found {
        Some(ci) => match env::i_constant_info_to_constant_val(&mut st.store, &ci) {
            Err(e) => Err(e),
            Ok(cv) => Ok(Some(cv)),
        },
        None => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// The projection function's shape and rule (`Arena/CheckerBase.lean:496-543`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:257-272 checkProjShape
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:496-509 checkProjShape`
/// — the projection type's parameter telescope is *syntactically* the
/// constructor's, and the constructor's residual is the family applied to
/// exactly the parameters.
pub fn check_proj_shape(
    st: &mut AState,
    pty: &EIdx,
    ctor_ty: &EIdx,
    n_p: u64,
    n_f: u64,
) -> Result<(), CheckError> {
    match expr_ops::strip_pis(st, n_p, pty) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_TY_TELE))),
        Ok(Some(_)) => match expr_ops::strip_pis(st, n_p + n_f, ctor_ty) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_CTOR_TELE))),
            Ok(Some(q)) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &q.1) {
                Err(e) => Err(e),
                Ok(args) => {
                    if args.len() as u64 != n_p {
                        fail(core_types::not_implemented(code_points(
                            &M_PROJ_RESID_ARITY,
                        )))
                    } else {
                        match expr_ops::get_app_fn(st, CORE_WALK_FUEL, &q.1) {
                            Err(e) => Err(e),
                            Ok(fna) => match view(st, &fna) {
                                Err(e) => Err(e),
                                Ok(ENodeView::Const(_, _)) => Ok(()),
                                Ok(_) => fail(core_types::not_implemented(code_points(
                                    &M_PROJ_RESID_HEAD,
                                ))),
                            },
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:511-543 checkProjRule`
/// — stage 3 of the projection install: the reduction rule — λ over the
/// constructor telescope returning field `i`, annotated; its λ-domains stay
/// the constructor's.  Split at the twin's own `let`-boundaries, three ways.
pub fn check_proj_rule(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    i: u64,
) -> Result<EIdx, CheckError> {
    match intern_e(st, ENodeView::BVar(sub_nat(sub_nat(n_f, 1), i))) {
        Err(e) => Err(e),
        Ok(b) => match expr_ops::pis_to_lams(st, n_p + n_f, &cvj.ty, &b) {
            Err(e) => Err(e),
            Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_RULE_TELE))),
            Ok(Some(rhs)) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &rhs) {
                Err(e) => Err(e),
                Ok(hf) => match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, &rhs) {
                    Err(e) => Err(e),
                    Ok(lb) => {
                        if !(!hf && lb) {
                            fail(core_types::not_implemented(code_points(&M_PROJ_RULE_SCOPE)))
                        } else {
                            match core::annotate_core(st, mode, fe, core::CHECK_FUEL, 0, &rhs) {
                                Err(e) => Err(e),
                                Ok(rhs_a) => check_proj_rule_wf(
                                    st, mode, fe, pty, cvj, lps, n_p, n_f, &b, rhs_a,
                                ),
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:519-529 checkProjRule`
/// — the annotated right-hand side's well-formedness, its λ-telescope, its
/// body and its domains against the constructor's.  **All four conjuncts of
/// the well-formedness test run**, as the twin's `do` does: Lean lifts every
/// `(← e)` out of the `unless`, and three of the four write a memo.
pub fn check_proj_rule_wf(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_f: u64,
    b: &EIdx,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match all_level_params_defined(st, lps, &rhs_a) {
        Err(e) => Err(e),
        Ok(w1) => match consts_resolve_f_fast(st, fe, &rhs_a) {
            Err(e) => Err(e),
            Ok(w2) => match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, &rhs_a) {
                Err(e) => Err(e),
                Ok(w3) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, &rhs_a) {
                    Err(e) => Err(e),
                    Ok(w4) => {
                        if !(w1 && w2 && w3 && !w4) {
                            fail(core_types::not_implemented(code_points(&M_PROJ_RULE_WF)))
                        } else {
                            check_proj_rule_shape(st, mode, fe, pty, cvj, n_p, n_f, b, rhs_a)
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:523-529 checkProjRule`
/// — the rule's λ-telescope, its body and the syntactic domain match against
/// the constructor's Π-telescope.
pub fn check_proj_rule_shape(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    b: &EIdx,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match expr_ops::strip_lams(st, n_p + n_f, &rhs_a) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_RULE_TELE))),
        Ok(Some(rq)) => {
            if !rq.1.eq2(b) {
                fail(core_types::not_implemented(code_points(&M_PROJ_RULE_BODY)))
            } else {
                match expr_ops::strip_pis(st, n_p + n_f, &cvj.ty) {
                    Err(e) => Err(e),
                    Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_CTOR_TELE))),
                    Ok(Some(cq)) => {
                        if !doms_match_aux(&rq.0, &cq.0, 0, 0, n_p + n_f) {
                            fail(core_types::not_implemented(code_points(&M_PROJ_RULE_DOMS)))
                        } else {
                            check_proj_rule_certs(st, mode, fe, pty, cvj, n_p, n_f, rhs_a)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:530-543 checkProjRule`
/// — the frame walks and the definitional parameter/domain pins (con-leche's
/// task #58), then the rule's own type inference.
pub fn check_proj_rule_certs(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    pty: &EIdx,
    cvj: &IConstantVal,
    n_p: u64,
    n_f: u64,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match open_pis_at_fvars_f(st, n_p, pty, 0) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_TY_TELE))),
        Ok(Some(pq)) => {
            let fvs_p: Vec<EIdx> = pq.0;
            match expr_ops::inst_pis_at_f(st, CORE_WALK_FUEL, &fvs_p, &cvj.ty) {
                Err(e) => Err(e),
                Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_CTOR_TELE))),
                Ok(Some(cq)) => match fvar_type_ds(st, &fvs_p) {
                    Err(e) => Err(e),
                    Ok(pdoms) => match check_def_eq_list(st, mode, fe, n_p + n_f, &pdoms, &cq.0) {
                        Err(e) => Err(e),
                        Ok(()) => match open_pis_at_fvars_f(st, n_f, &cq.1, n_p) {
                            Err(e) => Err(e),
                            Ok(None) => {
                                fail(core_types::not_implemented(code_points(&M_PROJ_CTOR_TELE)))
                            }
                            Ok(Some(xq)) => {
                                let all: Vec<EIdx> = core::append_eidx(fvs_p, &xq.0);
                                check_proj_rule_lams(st, mode, fe, n_p, n_f, &all, rhs_a)
                            }
                        },
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:274-311 checkProjRule
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:538-543 checkProjRule`
/// — the rule's λ-domains against the opened frame, and the rule's type.
pub fn check_proj_rule_lams(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    n_p: u64,
    n_f: u64,
    all: &Vec<EIdx>,
    rhs_a: EIdx,
) -> Result<EIdx, CheckError> {
    match expr_ops::inst_lams_at_f(st, CORE_WALK_FUEL, all, &rhs_a) {
        Err(e) => Err(e),
        Ok(None) => fail(core_types::not_implemented(code_points(&M_PROJ_RULE_TELE))),
        Ok(Some(lq)) => match fvar_type_ds(st, all) {
            Err(e) => Err(e),
            Ok(ldoms) => match check_def_eq_list(st, mode, fe, n_p + n_f, &ldoms, &lq.0) {
                Err(e) => Err(e),
                Ok(()) => match core::infer_type_core(st, mode, fe, core::CHECK_FUEL, 0, &rhs_a) {
                    Err(e) => Err(e),
                    Ok(_rhs_ty) => Ok(rhs_a),
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The block's partition and its declared parameter count
// (`Arena/CheckerBase.lean:545-580`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:716-719 ConstantInfo.isRecInfo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:554-556 isRecInfo` — is
/// this member a recursor record?
pub fn is_rec_info(ci: &IConstantInfo) -> bool {
    match ci {
        IConstantInfo::RecInfo(_, _, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:560-564 recsFormSuffix`
/// — do the recursors form a suffix of the block?  The tag pass.
pub fn recs_form_suffix(block: &Vec<IConstantInfo>) -> bool {
    recs_form_suffix_from(block, 0)
}

/// con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:560-564 recsFormSuffix`
/// — the cursor recursion behind `recs_form_suffix`.
pub fn recs_form_suffix_from(block: &Vec<IConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info_from(block, i + 1)
    } else {
        recs_form_suffix_from(block, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:721-727 recsFormSuffix
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:563 recsFormSuffix` —
/// the `rest.all isRecInfo` of the cited clause.
pub fn all_rec_info_from(block: &Vec<IConstantInfo>, i: usize) -> bool {
    if i >= block.len() {
        true
    } else if is_rec_info(&block[i]) {
        all_rec_info_from(block, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:569-580 indParamsOk` —
/// **the stream's declared parameter count, checked as official checks it**
/// (con-leche's task #228).  Both halves are one-sided on purpose: `false`
/// means official rejects.
pub fn ind_params_ok(
    st: &mut AState,
    n_p: u64,
    block: &Vec<IConstantInfo>,
) -> Result<bool, CheckError> {
    ind_params_ok_from(st, n_p, block, 0)
}

/// con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:569-580 indParamsOk` —
/// the cursor recursion behind `ind_params_ok`.
pub fn ind_params_ok_from(
    st: &mut AState,
    n_p: u64,
    block: &Vec<IConstantInfo>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= block.len() {
        Ok(true)
    } else {
        match ind_params_ok_at(st, n_p, &block[i]) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => ind_params_ok_from(st, n_p, block, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:588-622 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:572-579 indParamsOk` —
/// one member's half of the test: a type former must be able to peel `nP`
/// binders, a constructor must declare exactly `nP`, anything else passes.
pub fn ind_params_ok_at(st: &mut AState, n_p: u64, ci: &IConstantInfo) -> Result<bool, CheckError> {
    match ci {
        IConstantInfo::IndInfo(cv_t, _) => {
            let ty: EIdx = cv_t.ty.dup2();
            match env::pi_sort_tele_len(&st.store, CORE_WALK_FUEL, &ty) {
                Err(e) => Err(e),
                Ok(Some(n)) => Ok(n_p <= n),
                Ok(None) => Ok(true),
            }
        }
        IConstantInfo::CtorInfo(_, n_pc, _) => Ok(*n_pc == n_p),
        _ => Ok(true),
    }
}

// ---------------------------------------------------------------------------
// The structural comparisons `arena::env` will own (`Env.lean`'s `deriving
// DecidableEq` on all seven records)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:73-77 IConstantVal` — the cited
/// `deriving DecidableEq`.  **`arena::env`'s at merge** (the module note).
pub fn i_constant_val_beq(a: &IConstantVal, b: &IConstantVal) -> bool {
    a.name.eq2(&b.name) && core::nidx_vec_beq(&a.level_params, &b.level_params) && a.ty.eq2(&b.ty)
}

/// con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire
/// Lean twin: `proof/ConRon/Arena/Env.lean:84-88 IRecRuleFire` — the cited
/// `deriving DecidableEq`.  **`arena::env`'s at merge.**
pub fn i_rec_rule_fire_beq(a: &IRecRuleFire, b: &IRecRuleFire) -> bool {
    match (a, b) {
        (IRecRuleFire::Inert, IRecRuleFire::Inert) => true,
        (IRecRuleFire::Plain, IRecRuleFire::Plain) => true,
        (IRecRuleFire::Nested(l1, p1), IRecRuleFire::Nested(l2, p2)) => {
            lidx_vec_beq(l1, l2) && eidx_vec_beq(p1, p2)
        }
        _ => false,
    }
}

/// con-leche: none — `==` on `List LIdx`, elementwise
/// Lean twin: `proof/ConRon/Arena/Env.lean:84-88 IRecRuleFire` — handles, so
/// `==` is word equality (exactness, task #97a's `denoteL_inj`).
pub fn lidx_vec_beq(a: &Vec<LIdx>, b: &Vec<LIdx>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        lidx_vec_beq_from(a, b, 0)
    }
}

/// con-leche: none — `==` on `List LIdx`, elementwise
/// Lean twin: `proof/ConRon/Arena/Env.lean:84-88 IRecRuleFire` — the cursor
/// recursion behind `lidx_vec_beq`.
pub fn lidx_vec_beq_from(a: &Vec<LIdx>, b: &Vec<LIdx>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i].eq2(&b[i]) {
        lidx_vec_beq_from(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `==` on `List EIdx`, elementwise
/// Lean twin: `proof/ConRon/Arena/Env.lean:84-88 IRecRuleFire`.
pub fn eidx_vec_beq(a: &Vec<EIdx>, b: &Vec<EIdx>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        expr_ops::eidx_prefix_beq(a, b, 0)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:94-103 IRecRule` — the cited
/// `deriving DecidableEq`.  **`arena::env`'s at merge.**
pub fn i_rec_rule_beq(a: &IRecRule, b: &IRecRule) -> bool {
    a.ctor.eq2(&b.ctor)
        && a.nfields == b.nfields
        && a.ctor_params == b.ctor_params
        && i_rec_rule_fire_beq(&a.fire, &b.fire)
        && a.rhs.eq2(&b.rhs)
        && a.k == b.k
        && a.eta == b.eta
        && a.params_blind == b.params_blind
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:94-103 IRecRule` — `==` on a rule
/// list.
pub fn i_rec_rules_beq(a: &Vec<IRecRule>, b: &Vec<IRecRule>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        i_rec_rules_beq_from(a, b, 0)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:94-103 IRecRule` — the cursor
/// recursion behind `i_rec_rules_beq`.
pub fn i_rec_rules_beq_from(a: &Vec<IRecRule>, b: &Vec<IRecRule>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if i_rec_rule_beq(&a[i], &b[i]) {
        i_rec_rules_beq_from(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps
/// Lean twin: `proof/ConRon/Arena/Env.lean:117-131 IIndCaps` — the cited
/// `deriving DecidableEq`.  **`arena::env`'s at merge.**
pub fn i_ind_caps_beq(a: &IIndCaps, b: &IIndCaps) -> bool {
    a.eta == b.eta
        && a.eta_ctor.eq2(&b.eta_ctor)
        && a.eta_params == b.eta_params
        && a.eta_fields == b.eta_fields
        && a.unitlike == b.unitlike
        && a.unit_params == b.unit_params
        && a.rule_k == b.rule_k
        && prop_when::beq(&a.sort_z, &b.sort_z)
}

/// con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable
/// Lean twin: `proof/ConRon/Arena/Env.lean:137-155 IProjTable` — the cited
/// `deriving DecidableEq`.  **`arena::env`'s at merge.**
pub fn i_proj_table_beq(a: &IProjTable, b: &IProjTable) -> bool {
    a.struct_name.eq2(&b.struct_name)
        && a.table_name.eq2(&b.table_name)
        && core::nidx_vec_beq(&a.level_params, &b.level_params)
        && a.num_params == b.num_params
        && a.ctor.eq2(&b.ctor)
        && a.num_fields == b.num_fields
        && a.struct_sort.eq2(&b.struct_sort)
        && eidx_vec_beq(&a.bodies, &b.bodies)
        && lidx_vec_beq(&a.guards, &b.guards)
        && a.off == b.off
}

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: `proof/ConRon/Arena/Env.lean:183-191 IConstantInfo` — the cited
/// `deriving DecidableEq`, constructor for constructor.  **`arena::env`'s at
/// merge**; `eq_basis_stored` and the differential test are its two callers.
pub fn i_constant_info_beq(a: &IConstantInfo, b: &IConstantInfo) -> bool {
    match (a, b) {
        (IConstantInfo::AxiomInfo(x), IConstantInfo::AxiomInfo(y)) => i_constant_val_beq(x, y),
        (IConstantInfo::DefnInfo(x, v1, h1), IConstantInfo::DefnInfo(y, v2, h2)) => {
            i_constant_val_beq(x, y)
                && v1.eq2(v2)
                && con_ron_core::kernel::env::reducibility_hint_beq(h1, h2)
        }
        (IConstantInfo::ThmInfo(x, v1), IConstantInfo::ThmInfo(y, v2)) => {
            i_constant_val_beq(x, y) && v1.eq2(v2)
        }
        (IConstantInfo::IndInfo(x, c1), IConstantInfo::IndInfo(y, c2)) => {
            i_constant_val_beq(x, y) && i_ind_caps_beq(c1, c2)
        }
        (IConstantInfo::CtorInfo(x, p1, f1), IConstantInfo::CtorInfo(y, p2, f2)) => {
            i_constant_val_beq(x, y) && p1 == p2 && f1 == f2
        }
        (IConstantInfo::RecInfo(x, m1, r1, rl1), IConstantInfo::RecInfo(y, m2, r2, rl2)) => {
            i_constant_val_beq(x, y) && m1 == m2 && r1 == r2 && i_rec_rules_beq(rl1, rl2)
        }
        (IConstantInfo::ProjInfo(t1), IConstantInfo::ProjInfo(t2)) => i_proj_table_beq(t1, t2),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// The pinned `Eq` basis constant (`Arena/{Intern,StdAxioms}.lean`)
// ---------------------------------------------------------------------------

/// con-leche: none — intern a con-leche `Level` list
/// Lean twin: `proof/ConRon/Arena/Intern.lean:48 internExpr` —
/// `internLevelList` of `arena::monad` under the name the interning of a basis
/// constant wants.
pub fn intern_levels_l(st: &mut AState, us: &Vec<Level>) -> Result<Vec<LIdx>, CheckError> {
    crate::arena::monad::intern_level_list(st, us)
}

/// con-leche: none — intern a con-leche `Expr` into the store
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean internExpr` —
/// the arena's terms come from the parser, which builds them node by node; a
/// basis PIN is a `ConstantInfo` VALUE, so it needs this one converter.
pub fn intern_expr(st: &mut AState, e: &Expr) -> Result<EIdx, CheckError> {
    match expr::view(e) {
        ExprView::Bvar(i) => intern_e(st, ENodeView::BVar(*i)),
        ExprView::Fvar(i, ty) => match intern_expr(st, ty) {
            Err(er) => Err(er),
            Ok(t) => intern_e(st, ENodeView::FVar(*i, t)),
        },
        ExprView::Sort(u) => match intern_level(st, u) {
            Err(er) => Err(er),
            Ok(hu) => intern_e(st, ENodeView::Sort(hu)),
        },
        ExprView::Const(n, us) => match intern_name(st, n) {
            Err(er) => Err(er),
            Ok(hn) => match intern_levels(st, us) {
                Err(er) => Err(er),
                Ok(hus) => intern_e(st, ENodeView::Const(hn, hus)),
            },
        },
        ExprView::App(f, a) => match intern_expr(st, f) {
            Err(er) => Err(er),
            Ok(hf) => match intern_expr(st, a) {
                Err(er) => Err(er),
                Ok(ha) => intern_e(st, ENodeView::App(hf, ha)),
            },
        },
        ExprView::Lam(ty, b, m) => match intern_expr(st, ty) {
            Err(er) => Err(er),
            Ok(ht) => match intern_expr(st, b) {
                Err(er) => Err(er),
                Ok(hb) => intern_e(st, ENodeView::Lam(ht, hb, expr::binder_meta_dup(m))),
            },
        },
        ExprView::ForallE(ty, b, m) => match intern_expr(st, ty) {
            Err(er) => Err(er),
            Ok(ht) => match intern_expr(st, b) {
                Err(er) => Err(er),
                Ok(hb) => intern_e(st, ENodeView::ForallE(ht, hb, expr::binder_meta_dup(m))),
            },
        },
        ExprView::LetE(ty, v, b) => match intern_expr(st, ty) {
            Err(er) => Err(er),
            Ok(ht) => match intern_expr(st, v) {
                Err(er) => Err(er),
                Ok(hv) => match intern_expr(st, b) {
                    Err(er) => Err(er),
                    Ok(hb) => intern_e(st, ENodeView::LetE(ht, hv, hb)),
                },
            },
        },
        ExprView::Lit(l) => intern_e(st, ENodeView::Lit(expr::literal_dup(l))),
        ExprView::Proj(n, i, sub) => match intern_name(st, n) {
            Err(er) => Err(er),
            Ok(hn) => match intern_expr(st, sub) {
                Err(er) => Err(er),
                Ok(hs) => intern_e(st, ENodeView::Proj(hn, *i, hs)),
            },
        },
    }
}

/// con-leche: none — `cv.levelParams.mapM internName` over a `Vec<Name>`
/// Lean twin: `proof/ConRon/Arena/Intern.lean:55-57 internCV` — the
/// cursor recursion the `mapM` becomes.
pub fn intern_names(
    st: &mut AState,
    ns: &Vec<con_ron_core::kernel::name::Name>,
    i: usize,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if i >= ns.len() {
        Ok(out)
    } else {
        match intern_name(st, &ns[i]) {
            Err(e) => Err(e),
            Ok(h) => {
                let mut o: Vec<NIdx> = out;
                o.push(h);
                intern_names(st, ns, i + 1, o)
            }
        }
    }
}

/// con-leche: none — intern a con-leche `ConstantVal`
/// Lean twin: `proof/ConRon/Arena/Intern.lean:55-57 internCV`.
pub fn intern_cv(st: &mut AState, cv: &ConstantVal) -> Result<IConstantVal, CheckError> {
    match intern_name(st, &cv.name) {
        Err(e) => Err(e),
        Ok(name) => match intern_names(st, &cv.level_params, 0, Vec::new()) {
            Err(e) => Err(e),
            Ok(level_params) => match intern_expr(st, &cv.ty) {
                Err(e) => Err(e),
                Ok(ty) => Ok(IConstantVal {
                    name,
                    level_params,
                    ty,
                }),
            },
        },
    }
}

/// con-leche: none — intern a con-leche `IndCaps`
/// Lean twin: `proof/ConRon/Arena/Intern.lean:59-62 internCI`.
pub fn intern_caps(st: &mut AState, c: &IndCaps) -> Result<IIndCaps, CheckError> {
    match intern_name(st, &c.eta_ctor) {
        Err(e) => Err(e),
        Ok(eta_ctor) => Ok(IIndCaps {
            eta: c.eta,
            eta_ctor,
            eta_params: c.eta_params,
            eta_fields: c.eta_fields,
            unitlike: c.unitlike,
            unit_params: c.unit_params,
            rule_k: c.rule_k,
            sort_z: prop_when::dup(&c.sort_z),
        }),
    }
}

/// con-leche: ConLeche/Kernel/BasisA.lean:29-48 _
/// Lean twin: `proof/ConRon/Arena/StdAxioms.lean:136 eqA` — the
/// pinned annotated `Eq` type former, interned.  P4d-1's `arena::basis` owns
/// this; until it lands, interning `con_ron_core`'s own value is the only
/// spelling that makes the guard say what con-leche's says (the module note).
pub fn eq_basis_ci(st: &mut AState) -> Result<IConstantInfo, CheckError> {
    let ci: ConstantInfo = basis_pins::eq_a();
    match ci {
        ConstantInfo::IndInfo(cv, caps) => match intern_cv(st, &cv) {
            Err(e) => Err(e),
            Ok(icv) => match intern_caps(st, &caps) {
                Err(e) => Err(e),
                Ok(icaps) => Ok(IConstantInfo::IndInfo(icv, icaps)),
            },
        },
        _ => fail(core_types::internal(code_points(&M_RESERVED_BASIS))),
    }
}

/// con-leche: none — `(n.str s)` at a fixed suffix, interned
/// Lean twin: `proof/ConRon/Arena/Inductives/Modeled.lean:89 blockRenameTable`
/// — `.str n "_model"`, the one name suffix every modeled-route lookup builds.
/// Here rather than in `arena::inductives::modeled` because `Base.lean` is
/// where the shared name helpers of the borrowed layer sit.
pub fn model_name(st: &mut AState, n: &NIdx) -> Result<NIdx, CheckError> {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    intern_n_node(st, NNodeView::Str(n.dup2(), code_points(&MODEL)))
}

/// con-leche: none — `LsIdx` of an interned level list
/// Lean twin: `proof/ConRon/Arena/Monad.lean internLsNode` — the level list a
/// `const` node carries, from a `Vec<LIdx>` the installs already hold.
pub fn intern_ls(st: &mut AState, us: &Vec<LIdx>) -> Result<LsIdx, CheckError> {
    crate::arena::monad::intern_ls_node(st, env::lidx_vec_dup(us))
}

// ---------------------------------------------------------------------------
// The environment copy `arena::env` will own (Lean's value semantics)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: `proof/ConRon/Arena/Env.lean:183-191 IConstantInfo` — the
/// dictionary `ron::HashMap::dup` needs to copy an `IFEnv`'s index.
/// **`arena::env`'s at merge** (the module note).
impl Dup for IConstantInfo {
    /// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
    fn dup2(&self) -> IConstantInfo {
        env::i_constant_info_dup(self)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:677-679 Env
/// Lean twin: `proof/ConRon/Arena/Env.lean:280-282 IEnv` — the environment
/// copy Lean's value semantics gives for free.  **`arena::env`'s at merge.**
pub fn i_env_dup(e: &env::IEnv) -> env::IEnv {
    env::IEnv {
        consts: env::i_constant_infos_dup(&e.consts),
    }
}

/// con-leche: ConLeche/Kernel/FEnv.lean:29-49 FEnv
/// Lean twin: `proof/ConRon/Arena/Env.lean:309-312 IFEnv` — the indexed
/// environment's copy: the constants, the index and the visibility bound.
/// `con_ron_core::kernel::fenv::dup` is the same `O(size)` operation at the
/// same call site (`checkIndRecs`, which uses `fe₂` four times), and the
/// reason is the same: a Lean record is a value.  **`arena::env`'s at merge.**
pub fn ifenv_dup(fe: &IFEnv) -> IFEnv {
    IFEnv {
        env: i_env_dup(&fe.env),
        idx: fe.idx.dup(),
        visible_below: fe.visible_below,
    }
}
