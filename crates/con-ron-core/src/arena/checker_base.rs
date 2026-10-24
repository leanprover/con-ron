//! `arena::checker_base` — the declaration checker's common ground.
//!
//! The Rust twin of `proof/ConRon/Arena/CheckerBase.lean`, which is
//! con-leche's `Kernel/CheckerBase.lean`: the core entry-point record, the
//! common per-declaration constant check, and the strategy-independent helpers
//! the install paths share.
//!
//! ## The three systematic deviations, and the one the port adds
//!
//! 1. **`env : Env` is `fe : IFEnv`** — `arena::core`'s deviation 1.  con-leche
//!    carries each of these functions twice, once reading the linear
//!    association list and once the index (`DeclCheck.lean`'s `…F` mirrors);
//!    the arena has ONE environment type, so each pair collapses into one twin
//!    carrying a `con-leche:` line per collapsed declaration.
//! 2. **`CheckerOps` is not a record here at all.**  DESIGN.md §8.2 is explicit
//!    that it is "a program seam at HEAD, not a proof seam"; §3.4 forbids a
//!    record of function values, and `con_ron_core::kernel::checker_base` drops
//!    the `ops` binder for exactly that reason.  Neither side has the record:
//!    every body below calls `arena::core`'s fueled entry points by name, as
//!    the Lean twin's do.
//! 3. **A `g : Nat → Expr → Expr` argument is not a function value.**
//!    `domsMatchAux` is called at the identity everywhere in this module, so
//!    the twin here is the identity one and it is PURE: over handles a domain
//!    comparison is a handle comparison.
//!
//! The port's own:
//!
//! 4. **`mentionsConst` is here, not in `arena::inductives`.**  The Lean twin
//!    puts it in `Arena/Inductives/StructParts.lean`, which sits *below*
//!    `CheckerBase.lean` in the Lean import order; the Rust module graph has
//!    `arena::inductives` *above* this module (it calls `check_ind_decl`), so
//!    the walk is spelled here, at its one caller.  Task #97d's own "IndBase
//!    duplication" note is the Lean-side record of the same seam.

use crate::arena::core::{
    consts_resolve, ensure_sort_core, infer_type_core, reserved_basis_names, str_lit_supported,
    CHECK_FUEL, CORE_WALK_FUEL, M_SORRY, M_STR, M_UNKNOWN_CONST,
};
use crate::arena::core_state::take_walk_memo;
use crate::arena::env::{
    ifenv_find, IConstantInfo,
    IConstantVal, IFEnv,
};
use crate::arena::expr_ops::{
    cons_eidx, fvar_type_d, has_fvar_fast,
    instantiate1_fast, instantiate_list_fast, loose_bvars_bounded_fast,
};
use crate::arena::handle::{EIdx, NIdx, ETAG_FORALL_E};
use crate::arena::monad::{
    AState, fail, fail_dangling_e, intern_e_fvar, read_level, read_levels, read_names, view, view_bind,
};
use crate::arena::store::ENodeView;
use crate::arena::pins::pin_sorry_ax;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::expr::Literal;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines (con-ron-core's own spellings, so
// that a differential test can compare error text; §3.1 — a message need not
// match a theorem — and the twin's interpolated names are dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate declaration"`, as code points.
pub const M_DUP_DECL: [u32; 21] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111,
    110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"reserved basis name"`, as code points.
pub const M_RESERVED_BASIS: [u32; 19] = [
    114, 101, 115, 101, 114, 118, 101, 100, 32, 98, 97, 115, 105, 115, 32, 110, 97, 109, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"duplicate universe parameters in declaration"`, as code points.
pub const M_DUP_UNIV: [u32; 44] = [
    100, 117, 112, 108, 105, 99, 97, 116, 101, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112,
    97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 105, 110, 32, 100, 101, 99, 108, 97, 114, 97,
    116, 105, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"loose bound variable in type"`, as code points.
pub const M_LOOSE_TYPE: [u32; 28] = [
    108, 111, 111, 115, 101, 32, 98, 111, 117, 110, 100, 32, 118, 97, 114, 105, 97, 98, 108, 101,
    32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unexpected free variable in type"`, as code points.
pub const M_FVAR_TYPE: [u32; 32] = [
    117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105,
    97, 98, 108, 101, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"undeclared universe parameter in type"`, as code points.
pub const M_UNDECL_TYPE: [u32; 37] = [
    117, 110, 100, 101, 99, 108, 97, 114, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
    112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 105, 110, 32, 116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: allLevelParamsDefined"`, as code points.
pub const M_FUEL_ALPD: [u32; 37] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 108, 108, 76,
    101, 118, 101, 108, 80, 97, 114, 97, 109, 115, 68, 101, 102, 105, 110, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: constsResolveF"`, as code points.
pub const M_FUEL_CRF: [u32; 30] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 111, 110, 115,
    116, 115, 82, 101, 115, 111, 108, 118, 101, 70,
];


// ---------------------------------------------------------------------------
// Name-shape tests (`CheckerBase.lean:141-172`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:211-214 Name.nodup
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:35-40 nameNodup` — no
/// duplicates in a list of name HANDLES.  A name comparison is a handle
/// comparison (DESIGN.md §8.3: `denoteN` is injective).
pub fn name_nodup(ns: &Vec<NIdx>) -> bool {
    name_nodup_from(ns, 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:211-214 Name.nodup
/// The cited `List` recursion as an index recursion over the tail `ns[i..]`.
pub fn name_nodup_from(ns: &Vec<NIdx>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if nidx_contains_from(ns, i + 1, &ns[i]) {
        false
    } else {
        name_nodup_from(ns, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:211-214 Name.nodup
/// The cited `ns.contains n` over the tail.
pub fn nidx_contains_from(ns: &Vec<NIdx>, i: usize, n: &NIdx) -> bool {
    if i >= ns.len() {
        false
    } else if ns[i].eq2(n) {
        true
    } else {
        nidx_contains_from(ns, i + 1, n)
    }
}

// ---------------------------------------------------------------------------
// Level parameters, defined (`CheckerBase.lean:174-232`)
// ---------------------------------------------------------------------------

/// con-leche: none — probe a `EIdx ↦ Bool` walk memo (task #97-P4c's extraction rule 5)
/// A `HashMap::get` match that produces a value is its own function; never
/// inlined.
pub fn memo_b_get(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:233-249 Expr.allLevelParamsDefined
/// con-leche: ConLeche/Kernel/Level.lean:280-313 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:56-91
/// allLevelParamsDefinedGo` — the memoized walk.  `params` are transient names
/// (DESIGN.md §8.3's lesson 4: a level algorithm runs on trees, so the
/// parameter list is read back once at the entry); the memo is keyed on the
/// node, which is what makes a shared subterm cost one probe.  It is threaded
/// as a `&mut` where the twin threads it as an argument and a result.
pub fn all_level_params_defined_go(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ALPD)))
    } else {
        match memo_b_get(memo, h) {
            Some(r) => Ok(r),
            None => match all_level_params_defined_node(pers, st, params, memo, fuel - 1, h) {
                Err(e) => Err(e),
                Ok(r) => {
                    memo.insert(h.dup2(), r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:280-313 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:56-91
/// allLevelParamsDefinedGo` — the arms, past the probe.
pub fn all_level_params_defined_node(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::BVar(_)) => Ok(true),
        Ok(ENodeView::Lit(_)) => Ok(true),
        Ok(ENodeView::Sort(u)) => match read_level(pers, st, &u) {
            Err(e) => Err(e),
            Ok(l) => Ok(level::all_params_defined(params, &l)),
        },
        Ok(ENodeView::Const(_, us)) => match read_levels(pers, st, &us) {
            Err(e) => Err(e),
            Ok(ls) => Ok(all_params_defined_list(params, &ls, 0)),
        },
        Ok(ENodeView::FVar(_, t)) => all_level_params_defined_go(pers, st, params, memo, fuel, &t),
        Ok(ENodeView::App(f, a)) => match all_level_params_defined_go(pers, st, params, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok(b1) => {
                if b1 {
                    all_level_params_defined_go(pers, st, params, memo, fuel, &a)
                } else {
                    Ok(false)
                }
            }
        },
        Ok(ENodeView::Lam(t, b)) => {
            all_level_params_defined_binder(pers, st, params, memo, fuel, &t, &b)
        }
        Ok(ENodeView::ForallE(t, b)) => {
            all_level_params_defined_binder(pers, st, params, memo, fuel, &t, &b)
        }
        Ok(ENodeView::LetE(t, v, b)) => {
            match all_level_params_defined_go(pers, st, params, memo, fuel, &t) {
                Err(e) => Err(e),
                Ok(b1) => {
                    if !b1 {
                        Ok(false)
                    } else {
                        match all_level_params_defined_go(pers, st, params, memo, fuel, &v) {
                            Err(e) => Err(e),
                            Ok(b2) => {
                                if !b2 {
                                    Ok(false)
                                } else {
                                    all_level_params_defined_go(pers, st, params, memo, fuel, &b)
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(ENodeView::Proj(_, _, e)) => all_level_params_defined_go(pers, st, params, memo, fuel, &e),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:280-313 Expr.allLevelParamsDefinedGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:56-91
/// allLevelParamsDefinedGo` — the twin's `.lam` and `.forallE` clauses, which
/// are one shape (the domain, then the body).
pub fn all_level_params_defined_binder(
    pers: &PersTier,
    st: &AState,
    params: &Vec<Name>,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    t: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match all_level_params_defined_go(pers, st, params, memo, fuel, t) {
        Err(e) => Err(e),
        Ok(b1) => {
            if !b1 {
                Ok(false)
            } else {
                match all_level_params_defined_go(pers, st, params, memo, fuel, b) {
                    Err(e) => Err(e),
                    Ok(b2) => Ok(b2),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:280-313 Expr.allLevelParamsDefinedGo
/// The `.const` clause's `ls.all (Level.allParamsDefined params)`, as an index
/// recursion (§3.4 forbids the closure `List.all` takes).
pub fn all_params_defined_list(params: &Vec<Name>, ls: &Vec<Level>, i: usize) -> bool {
    if i >= ls.len() {
        true
    } else if level::all_params_defined(params, &ls[i]) {
        all_params_defined_list(params, ls, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:386-388 Expr.allLevelParamsDefinedFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:93-98 allLevelParamsDefined`
/// — the executed `allLevelParamsDefined`: one memoized DAG walk, at the
/// parameter list read back once.
pub fn all_level_params_defined(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match read_names(pers, st, lps) {
        Err(err) => Err(err),
        Ok(ks) => {
            let mut memo: HashMap<EIdx, bool> = take_walk_memo(&mut st.memos.lp_def_c);
            let r = all_level_params_defined_go(pers, st, &ks, &mut memo, CORE_WALK_FUEL, e);
            st.memos.lp_def_c = memo;
            r
        }
    }
}

// ---------------------------------------------------------------------------
// `constsResolve`, memoized (`CheckerBase.lean:234-286`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/DeclCheck.lean:30-51 Expr.constsResolveF
/// con-leche: ConLeche/Kernel/DeclCheck.lean:82-117 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:111-149 constsResolveFGo` —
/// the memoized walk.  The four LEAF clauses are `arena::core`'s
/// `consts_resolve` at one node, exactly as con-leche's `…Go` calls the pure
/// walk at its four non-recursive constructors; everything else probes.
///
/// **Not the pure walk.**  Every declaration front door asks this of a stream
/// term, and on a DAG-shared type the pure walk unfolds the DAG (con-leche's
/// task #210 Part B, `tests/e2e/tower_struct.ndjson`; task #97d met the same
/// thing on eight fixtures and it is what made them time out).
pub fn consts_resolve_f_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CRF)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Sort(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Lit(_)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(ENodeView::Const(_, _)) => consts_resolve(pers, vis, st, fe, CORE_WALK_FUEL, h),
            Ok(v) => match memo_b_get(memo, h) {
                Some(r) => Ok(r),
                None => match consts_resolve_f_node(pers, vis, st, fe, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        memo.insert(h.dup2(), r);
                        Ok(r)
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:82-117 Expr.constsResolveFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:111-149 constsResolveFGo` —
/// the six memoized arms, past the probe.  The `.proj` arm's `fe.find? s` is
/// the structure's own resolution, as the twin has it.
pub fn consts_resolve_f_node(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<bool, CheckError> {
    match v {
        ENodeView::FVar(_, ty) => consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &ty),
        ENodeView::App(f, a) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &f, &a),
        ENodeView::Lam(ty, body) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &body),
        ENodeView::ForallE(ty, body) => consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &body),
        ENodeView::LetE(ty, val, body) => {
            match consts_resolve_f_two(pers, vis, st, fe, memo, fuel, &ty, &val) {
                Err(e) => Err(e),
                Ok(b12) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &body) {
                    Err(e) => Err(e),
                    Ok(b3) => Ok(b12 && b3),
                },
            }
        }
        ENodeView::Proj(s, _, sub) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, &sub) {
            Err(e) => Err(e),
            Ok(b) => Ok(ifenv_find(vis, fe, &s).is_some() && b),
        },
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:82-117 Expr.constsResolveFGo
/// The twin's `(b₁ && b₂, memo)` of the two-child arms.  **Both children are
/// walked**, as the twin walks them: the conjunction is not short-circuited,
/// because the memo the second walk fills is part of the state.
pub fn consts_resolve_f_two(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, a) {
        Err(e) => Err(e),
        Ok(b1) => match consts_resolve_f_go(pers, vis, st, fe, memo, fuel, b) {
            Err(e) => Err(e),
            Ok(b2) => Ok(b1 && b2),
        },
    }
}

/// con-leche: ConLeche/Kernel/DeclCheck.lean:190-192 Expr.constsResolveFFast
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:151-155 constsResolveFFast`
/// — the executed `constsResolve` (one memoized DAG walk), which is what every
/// front door below calls.
pub fn consts_resolve_f_fast(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    let mut memo: HashMap<EIdx, bool> = take_walk_memo(&mut st.memos.crf_c);
    let r = consts_resolve_f_go(pers, vis, st, fe, &mut memo, CORE_WALK_FUEL, e);
    st.memos.crf_c = memo;
    r
}

/// con-leche: none — `xs.map Expr.fvarTypeD` over a list of handles
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:157-165 fvarTypeDs` — §3.4
/// forbids the closure `List.map` takes, and its rule for a `List` recursion
/// is a helper.
pub fn fvar_type_ds(
    pers: &PersTier,
    st: &AState,
    hs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= hs.len() {
        Ok(out)
    } else {
        match fvar_type_d(pers, st, &hs[i]) {
            Err(e) => Err(e),
            Ok(t) => {
                let mut out2 = out;
                out2.push(t);
                fvar_type_ds(pers, st, hs, i + 1, out2)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `mentionsConst` (module note 5)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:46-66 unresolvedConstsError
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:176-186 unresolvedConstsError`
/// — **the verdict at a term whose constants do not all resolve.**  A term that
/// mentions `sorryAx` DECLINES (the axiom is tolerated as a declaration and
/// installs nothing, so a use of it is a positively detected unsupported
/// feature); anything else is an unknown constant and REJECTS.  Monadic here
/// because the walk reads the store; the twin's `where_ : String` argument only
/// names the slot in the message, and §3.1 drops the interpolation.
pub fn unresolved_consts_error(
    pers: &PersTier,
    st: &mut AState,
    e: &EIdx,
) -> Result<CheckError, CheckError>  {
    match pin_sorry_ax(st) {
        Err(err) => Err(err),
        Ok(sa) => match crate::arena::inductives::struct_parts::mentions_const(pers, st, &sa, e) {
            Err(err) => Err(err),
            Ok(r) => {
                if r {
                    Ok(CheckError::NotImplemented(code_points(&M_SORRY)))
                } else {
                    Ok(CheckError::Invalid(code_points(&M_UNKNOWN_CONST)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:68-90 Expr.hasStrLitGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:188-221 hasStrLitGo` — does
/// the term contain a string literal?  A memoized walk (error path only), the
/// memo keyed by the node; con-leche's visited-set returns `false` at a
/// revisit, which is the answer the first visit already gave unless it found
/// one — and then the walk has returned `true` already.
pub fn has_str_lit_go(
    pers: &PersTier,
    st: &AState,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CRF)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Lit(Literal::StrVal(_))) => Ok(true),
            Ok(ENodeView::BVar(_)) => Ok(false),
            Ok(ENodeView::Sort(_)) => Ok(false),
            Ok(ENodeView::Const(_, _)) => Ok(false),
            Ok(ENodeView::Lit(_)) => Ok(false),
            Ok(v) => match memo_b_get(memo, h) {
                Some(_) => Ok(false),
                None => {
                    memo.insert(h.dup2(), false);
                    has_str_lit_node(pers, st, memo, fuel - 1, v)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:68-90 Expr.hasStrLitGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:188-221 hasStrLitGo` — the
/// walk's arms past the visit, each child in order, stopping at the first
/// string literal.
pub fn has_str_lit_node(
    pers: &PersTier,
    st: &AState,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<bool, CheckError> {
    match v {
        ENodeView::FVar(_, ty) => has_str_lit_go(pers, st, memo, fuel, &ty),
        ENodeView::App(f, a) => has_str_lit_two(pers, st, memo, fuel, &f, &a),
        ENodeView::Lam(t, b) => has_str_lit_two(pers, st, memo, fuel, &t, &b),
        ENodeView::ForallE(t, b) => has_str_lit_two(pers, st, memo, fuel, &t, &b),
        ENodeView::LetE(t, v2, b) => match has_str_lit_two(pers, st, memo, fuel, &t, &v2) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => has_str_lit_go(pers, st, memo, fuel, &b),
        },
        ENodeView::Proj(_, _, x) => has_str_lit_go(pers, st, memo, fuel, &x),
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:68-90 Expr.hasStrLitGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:188-221 hasStrLitGo` — two
/// children, the second only if the first had none.
pub fn has_str_lit_two(
    pers: &PersTier,
    st: &AState,
    memo: &mut HashMap<EIdx, bool>,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match has_str_lit_go(pers, st, memo, fuel, a) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => has_str_lit_go(pers, st, memo, fuel, b),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:92-98 unresolvedConstsErrorL
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:223-235 unresolvedConstsErrorL`
/// — `unresolved_consts_error` with a string-literal guard ahead of it: a
/// string literal is DECLINED here, before resolution, when the String support
/// declarations are not yet present (con-leche task #342 L-CK: the guard the
/// annotate pass used to run).  `str_ok` is the caller's `strLitSupported`.
pub fn unresolved_consts_error_l(
    pers: &PersTier,
    st: &mut AState,
    str_ok: bool,
    e: &EIdx,
) -> Result<CheckError, CheckError> {
    let lit: Result<bool, CheckError> = if str_ok {
        Ok(false)
    } else {
        let mut memo: HashMap<EIdx, bool> = HashMap::new();
        has_str_lit_go(pers, st, &mut memo, CORE_WALK_FUEL, e)
    };
    match lit {
        Err(err) => Err(err),
        Ok(true) => Ok(CheckError::NotImplemented(code_points(&M_STR))),
        Ok(false) => unresolved_consts_error(pers, st, e),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:92-98 unresolvedConstsErrorL
/// con-leche: ConLeche/Kernel/DeclCheck.lean:361-379 checkConstantValF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:223-235 unresolvedConstsErrorL`
/// — the failing arm every front door spells: `throw (unresolvedConstsErrorL
/// (strLitSupportedF fe) where_ e)`, the support test read first, as Lean
/// evaluates the argument.
pub fn unresolved_consts_fail<T>(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<T, CheckError> {
    match str_lit_supported(pers, vis, st, fe) {
        Err(err) => Err(err),
        Ok(ok) => match unresolved_consts_error_l(pers, st, ok, e) {
            Err(err) => Err(err),
            Ok(err) => fail(err),
        },
    }
}

// ---------------------------------------------------------------------------
// The per-declaration constant check (`CheckerBase.lean:321-354`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:102-121 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:361-379 checkConstantValF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:239-265 checkConstantVal` —
/// checks common to all declarations: fresh name, no reserved name,
/// well-formed universe parameters, and a type that
/// is a type and mentions only declared parameters.  **Returns nothing**
/// (con-leche task #342 S5C): the constant is stored as declared.
///
/// The twin reads the name back for four of the six messages (DESIGN.md §8.3's
/// "readback happens only for the environment index's error text"); the port
/// drops the interpolation, so the readbacks go with it.
pub fn check_constant_val(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    match check_constant_val_guards(pers, vis, st, fe, cv) {
        Err(e) => Err(e),
        Ok(()) => match install_header_tail(pers, vis, st, fe, cv) {
            Err(e) => Err(e),
            Ok(()) => match infer_type_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &cv.ty) {
                Err(e) => Err(e),
                Ok(stype) => match ensure_sort_core(pers, vis, st, mode, fe, CHECK_FUEL, 0, &stype) {
                    Err(e) => Err(e),
                    Ok(_u) => Ok(()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:102-121 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:361-379 checkConstantValF
/// con-leche: ConLeche/Kernel/CheckerSplit.lean:63-79 installHeader
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:239-265 checkConstantVal` —
/// the five SYNTACTIC guards on the header, in the twin's order.  Shared with
/// `arena::checker_split::install_header`, which the twin writes out clause for
/// clause a second time (as con-leche does).
pub fn check_constant_val_guards(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    if ifenv_find(vis, fe, &cv.name).is_some() {
        fail(CheckError::Invalid(code_points(&M_DUP_DECL)))
    } else {
        match reserved_basis_names(st) {
            Err(e) => Err(e),
            Ok(rs) => {
                if nidx_contains_from(&rs, 0, &cv.name) {
                    fail(CheckError::Invalid(code_points(&M_RESERVED_BASIS)))
                } else {
                    check_constant_val_guards_rest(pers, st, cv)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:102-121 checkConstantVal
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:239-265 checkConstantVal` —
/// the three guards past the reserved-name test.
pub fn check_constant_val_guards_rest(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    if !name_nodup(&cv.level_params) {
        fail(CheckError::Invalid(code_points(&M_DUP_UNIV)))
    } else {
        match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, &cv.ty) {
            Err(e) => Err(e),
            Ok(b) => {
                if !b {
                    fail(CheckError::Invalid(code_points(&M_LOOSE_TYPE)))
                } else {
                    match has_fvar_fast(pers, st, CORE_WALK_FUEL, &cv.ty) {
                        Err(e) => Err(e),
                        Ok(f) => {
                            if f {
                                fail(CheckError::Invalid(code_points(&M_FVAR_TYPE)))
                            } else {
                                Ok(())
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:102-121 checkConstantVal
/// con-leche: ConLeche/Kernel/DeclCheck.lean:361-379 checkConstantValF
/// con-leche: ConLeche/Kernel/CheckerSplit.lean:63-79 installHeader
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:239-265 checkConstantVal`
/// (and `CheckerSplit.lean installHeader`, which spells it a second time) —
/// the two guards on the declared type: its universe parameters are declared,
/// and its constants resolve (else `unresolvedConstsErrorL`'s verdict).  This
/// is exactly the install half's tail, so the two twins share it here where
/// the Lean writes it twice.  Task #119: was `install_constant_val_tail`, on
/// the annotated type, returning the annotated header.
pub fn install_header_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<(), CheckError> {
    match all_level_params_defined(pers, st, &cv.level_params, &cv.ty) {
        Err(e) => Err(e),
        Ok(d) => {
            if !d {
                fail(CheckError::Invalid(code_points(&M_UNDECL_TYPE)))
            } else {
                match consts_resolve_f_fast(pers, vis, st, fe, &cv.ty) {
                    Err(e) => Err(e),
                    Ok(r) => {
                        if !r {
                            unresolved_consts_fail(pers, vis, st, fe, &cv.ty)
                        } else {
                            Ok(())
                        }
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The strategy-independent helpers (`CheckerBase.lean:356-543`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CheckerBase.lean:123-133 openPisAtFvars
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:269-285 openPisAtFvars` —
/// open the first `n` `∀`-binders at fresh free variables `0..n-1` (each
/// fvar's type is the binder domain, instantiated with the earlier fvars).
/// Structural on `n`, so no fuel of its own.
pub fn open_pis_at_fvars(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body)) => match intern_e_fvar(pers, st, i, dom) {
                    Err(e) => Err(e),
                    Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                        Err(e) => Err(e),
                        Ok(b) => match open_pis_at_fvars(pers, st, n - 1, &b, i + 1) {
                            Err(e) => Err(e),
                            Ok(Some((fvs, e2))) => Ok(Some((cons_eidx(&fv, &fvs), e2))),
                            Ok(None) => Ok(None),
                        },
                    },
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:135-149 openPisAtFvarsFGo
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:287-304 openPisAtFvarsFGo` —
/// core of `openPisAtFvarsF`: `acc` holds the already-created fvars — the list
/// `instantiate_list` takes at cursor 0, in PUSH order on an OWNED vector
/// (task #97-P6-15).  One `instantiateList` pass per domain instead of one
/// whole-telescope `instantiate1` pass per binder.  The list this function
/// RETURNS is a different one and keeps its cons: it is built on the way out.
pub fn open_pis_at_fvars_f_go(
    pers: &PersTier,
    st: &mut AState,
    acc: Vec<EIdx>,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, h, &acc, 0) {
            Err(e) => Err(e),
            Ok(b) => Ok(Some((Vec::new(), b))),
        }
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((dom, body)) => {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, &acc, 0) {
                        Err(e) => Err(e),
                        Ok(d) => match intern_e_fvar(pers, st, i, d) {
                            Err(e) => Err(e),
                            Ok(fv) => {
                                let mut acc2: Vec<EIdx> = acc;
                                acc2.push(fv.dup2());
                                match open_pis_at_fvars_f_go(pers, st, acc2, n - 1, &body, i + 1) {
                                    Err(e) => Err(e),
                                    Ok(Some((fvs, e2))) => Ok(Some((cons_eidx(&fv, &fvs), e2))),
                                    Ok(None) => Ok(None),
                                }
                            }
                        },
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:151-158 openPisAtFvarsF
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:306-313 openPisAtFvarsF` —
/// one-pass `openPisAtFvars` (the fallback covers telescopes whose binders only
/// appear after substitution).  **The executed one.**
pub fn open_pis_at_fvars_f(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    e: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    match open_pis_at_fvars_f_go(pers, st, Vec::new(), n, e, i) {
        Err(err) => Err(err),
        Ok(Some(r)) => Ok(Some(r)),
        Ok(None) => open_pis_at_fvars(pers, st, n, e, i),
    }
}

/// con-leche: ConLeche/Kernel/CheckerBase.lean:203-209 unwrapOr
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:315-320 unwrapOr` — unwrap
/// an optional value or fail with the given error.
pub fn unwrap_or<T>(o: Option<T>, err: CheckError) -> Result<T, CheckError> {
    match o {
        Some(a) => Ok(a),
        None => Err(err),
    }
}

// ---------------------------------------------------------------------------
// The block's partition and its declared parameter count
// (`CheckerBase.lean:545-579` of the twin)
//
// Three `ConLeche/Kernel/Env.lean` declarations, placed at their only readers —
// the `.indDecl` arm and the modeled install — exactly as the six `Level.lean`
// declarations above are.  Task #97d-2 wrote them in
// `Arena/Inductives/Base.lean` under the concurrency contract; task #97f's
// dedup deleted that file and brought them here, and the Rust follows.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:465-499 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:327-340 indParamsOk` —
/// **the stream's declared parameter count, checked as official checks it**
/// (con-leche's task #228).  Both halves are one-sided on purpose: `false`
/// means official rejects.
pub fn ind_params_ok(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    block: &Vec<IConstantInfo>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= block.len() {
        Ok(true)
    } else {
        match ind_params_ok_at(pers, st, n_p, &block[i]) {
            Err(e) => Err(e),
            Ok(ok) => {
                if ok {
                    ind_params_ok(pers, st, n_p, block, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:465-499 indParamsOk
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:327-340 indParamsOk` — one
/// member's test: a type former's Π-telescope is at least `nP` long, a
/// constructor's own parameter count is exactly `nP`, and everything else
/// passes.
pub fn ind_params_ok_at(
    pers: &PersTier,
    st: &mut AState,
    n_p: u64,
    ci: &IConstantInfo,
) -> Result<bool, CheckError>  {
    match ci {
        IConstantInfo::IndInfo(cv_t, _) => {
            match crate::arena::env::pi_sort_tele_len(pers, &st.store, CORE_WALK_FUEL, &cv_t.ty) {
                Err(e) => Err(e),
                Ok(Some(n)) => Ok(n_p <= n),
                Ok(None) => Ok(true),
            }
        }
        IConstantInfo::CtorInfo(_, n_pc, _) => Ok(*n_pc == n_p),
        _ => Ok(true),
    }
}
