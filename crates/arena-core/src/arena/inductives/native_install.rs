//! `arena::inductives::native_install` — the fixpoint route's install.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/NativeInstall.lean`, which
//! is `ConLeche/Kernel/Inductives/NativeInstall.lean` whole over handles: the
//! capability record, official's `is_rec`, the re-check of the field kinds on
//! the opened annotated constructors, the generated recursor and its rules, the
//! projection table at a structure-like block, and the two-pass install.
//!
//! ## The twin's deviations
//!
//! * **The `…F` twins collapse into these** (task #97c's deviation 1), and
//!   with them the `StructWalkers` record every `F` function takes — the
//!   arena's `consts_resolve_f_fast` and `struct_proj_bodies` ARE the memoised
//!   walks that record exists to substitute.  The `F` names live on in
//!   `arena::inductives::native_install_f`.
//! * **`nativeCapsAt` is `arena::inductives::sum_install`'s**, because
//!   `checkSumInd` calls it where con-leche passes it in as a closure.
//! * **`NativePass` is not generic** in the environment representation:
//!   con-leche parameterises it because it has two (`Env` and `FEnv`); the
//!   arena has one.
//! * **`mentionsFvar` collapses its pure walk, its memoized walk and its entry
//!   into one twin**, as `arena::inductives::struct_parts` does for
//!   `hasLooseBVarB` and `mentionsConst`.  Its memo is keyed by the node alone
//!   — `q` is fixed for the walk — and con-leche's own note says why there is
//!   no derived-word cutoff to put in front of it: `fvarB` stops at an `fvar`
//!   leaf while the walk descends into the leaf's TYPE ANNOTATION.
//!
//! The two messages of `checkNative`'s own guards are
//! `con_ron_core::kernel::inductives::inductives_c`'s, because that is the
//! executed driver the differential test compares against; the rest are
//! `native_install`'s.

use super::native_parts;
use super::native_parts::{NativeParts, RecFieldKind};
use super::struct_install;
use super::struct_parts;
use super::sum_install;
use super::sum_parts;
use crate::arena::canon;
use crate::arena::checker_base;
use crate::arena::core;
use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env;
use crate::arena::env::{IConstantInfo, IConstantVal, IFEnv, IIndCaps};
use crate::arena::expr_ops;
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{fail, intern_e, intern_n_node, read_level, view, AState};
use crate::arena::store::{ENodeView, NNodeView};
use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::level;
use con_ron_core::kernel::prop_when;
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap};

// ---------------------------------------------------------------------------
// The messages (con-ron-core's own, interpolation dropped)
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `'fuel exhausted: mentionsFvar'`, as code points.
pub const M_FUEL_MENTIONS_FVAR: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 109, 101, 110, 116,
    105, 111, 110, 115, 70, 118, 97, 114,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor rule     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_RULE: [u32; 30] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 114, 117, 108, 101, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor rule scoping     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_RULE_SCOPE: [u32; 38] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 114, 117, 108, 101, 32, 115, 99, 111, 112, 105, 110, 103, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: the block's recursor is not T.rec           `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_NAME: [u32; 56] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 98, 108, 111, 99,
    107, 39, 115, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 105, 115, 32, 110, 111, 116, 32,
    84, 46, 114, 101, 99, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: level parameters are not the generated ones     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_LPS: [u32; 60] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 108, 101, 118, 101, 108, 32, 112, 97,
    114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101,
    32, 103, 101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 115, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: the record is not the generated one     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_PIN: [u32; 52] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 114, 101, 99, 111,
    114, 100, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110, 101, 114, 97,
    116, 101, 100, 32, 111, 110, 101, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor type     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_TY: [u32; 30] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 116, 121, 112, 101, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor type scoping     `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_TYSC: [u32; 38] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 116, 121, 112, 101, 32, 115, 99, 111, 112, 105, 110, 103, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor type is not the generated one  `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_REC_DEFEQ: [u32; 52] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103, 101, 110,
    101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: constructor telescope        `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_KIND_TELE: [u32; 41] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 99, 111, 110, 115, 116, 114, 117, 99,
    116, 111, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: non positive or non valid occurrence                    `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_KIND_NEG: [u32; 68] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 110, 111, 110, 32, 112, 111, 115, 105,
    116, 105, 118, 101, 32, 111, 114, 32, 110, 111, 110, 32, 118, 97, 108, 105, 100, 32, 111, 99,
    99, 117, 114, 114, 101, 110, 99, 101, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32,
    32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: a nested occurrence of the block  `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_KIND_NEST: [u32; 46] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 97, 32, 110, 101, 115, 116, 101, 100,
    32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 116, 104, 101, 32, 98,
    108, 111, 99, 107, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: large eliminator on a multi-ctor inductive        `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_TAIL_ELIM: [u32; 62] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 108, 97, 114, 103, 101, 32, 101, 108,
    105, 109, 105, 110, 97, 116, 111, 114, 32, 111, 110, 32, 97, 32, 109, 117, 108, 116, 105, 45,
    99, 116, 111, 114, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 32, 32, 32, 32, 32, 32,
    32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: type former telescope      `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_TAIL_TELE: [u32; 39] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 121, 112, 101, 32, 102, 111, 114,
    109, 101, 114, 32, 116, 101, 108, 101, 115, 99, 111, 112, 101, 32, 32, 32, 32, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: field kinds  `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_TAIL_KINDS: [u32; 25] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 102, 105, 101, 108, 100, 32, 107, 105,
    110, 100, 115, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: recursor rules are not the generated ones  `, as code points — `con_ron_core::kernel::inductives::native_install`'s own, so the differential test can compare error text.
pub const M_TAIL_RULES: [u32; 55] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 114, 101, 99, 117, 114, 115, 111, 114,
    32, 114, 117, 108, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 116, 104, 101, 32, 103,
    101, 110, 101, 114, 97, 116, 101, 100, 32, 111, 110, 101, 115, 32, 32,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: duplicate constructor`, as code points — `con_ron_core::kernel::inductives::inductives_c`'s own, so the differential test can compare error text.
pub const M_NAT_DUP: [u32; 33] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 100, 117, 112, 108, 105, 99, 97, 116,
    101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `direct rec: the capability record did not settle         `, as code points — `con_ron_core::kernel::inductives::inductives_c`'s own, so the differential test can compare error text.
pub const M_NAT_SETTLE: [u32; 57] = [
    100, 105, 114, 101, 99, 116, 32, 114, 101, 99, 58, 32, 116, 104, 101, 32, 99, 97, 112, 97, 98,
    105, 108, 105, 116, 121, 32, 114, 101, 99, 111, 114, 100, 32, 100, 105, 100, 32, 110, 111, 116,
    32, 115, 101, 116, 116, 108, 101, 32, 32, 32, 32, 32, 32, 32, 32, 32,
];

// ---------------------------------------------------------------------------
// The capability record (`NativeInstall.lean:37-60` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:42-43 nativeIsRec`
/// — official's `is_rec` off the classified kinds: some field is recursive or
/// reflexive.
pub fn native_is_rec(kinds: &Vec<Vec<RecFieldKind>>) -> bool {
    native_is_rec_from(kinds, 0)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:42-43 nativeIsRec`
/// — the cursor recursion behind `native_is_rec`.
pub fn native_is_rec_from(kinds: &Vec<Vec<RecFieldKind>>, i: usize) -> bool {
    if i >= kinds.len() {
        false
    } else if kinds_any_rec(&kinds[i], 0) {
        true
    } else {
        native_is_rec_from(kinds, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:100-103 nativeIsRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:43 nativeIsRec`
/// — the inner `ks.any` of the cited clause.
pub fn kinds_any_rec(ks: &Vec<RecFieldKind>, i: usize) -> bool {
    if i >= ks.len() {
        false
    } else if native_parts::rec_field_kind_beq(&ks[i], &RecFieldKind::Recursive)
        || native_parts::rec_field_kind_beq(&ks[i], &RecFieldKind::Reflexive)
    {
        true
    } else {
        kinds_any_rec(ks, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:105-108 nativeCaps
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:47-48 nativeCaps`
/// — the block's capability record at its classified kinds.
pub fn native_caps(st: &mut AState, p: &NativeParts) -> Result<IIndCaps, CheckError> {
    sum_install::native_caps_at(st, &p.shape, native_is_rec(&p.kinds))
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:53-60 nativeRawRec`
/// — **the syntactic reading of `is_rec`** (con-leche's task #268): does the
/// block occur in some declared field domain of some constructor?
pub fn native_raw_rec(st: &mut AState, p: &NativeParts) -> Result<bool, CheckError> {
    if p.shape.ctors.len() != 1 {
        Ok(false)
    } else {
        let n_f: u64 = p.shape.ctors[0].1;
        let cty: EIdx = p.shape.ctors[0].0.ty.dup2();
        let t: NIdx = p.shape.cv_t.name.dup2();
        match expr_ops::strip_pis(st, p.shape.n_p + n_f, &cty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(q)) => any_dom_mentions(st, &t, &q.0, p.shape.n_p as usize),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:110-128 nativeRawRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:58 nativeRawRec`
/// — the `(cbs.drop p.nP).anyM` of the cited clause.
pub fn any_dom_mentions(
    st: &mut AState,
    t: &NIdx,
    cbs: &Vec<(EIdx, con_ron_core::kernel::expr::BinderMeta)>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= cbs.len() {
        Ok(false)
    } else {
        let d: EIdx = cbs[i].0.dup2();
        match struct_parts::mentions_const(st, t, &d) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => any_dom_mentions(st, t, cbs, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// `mentionsFvar` (`NativeInstall.lean:62-116` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:84 mentionsFvarGo`
/// — the `memo[h]?` probe of the `mentionsFvar` walk.
pub fn mf_probe(memo: &HashMap<EIdx, bool>, k: &EIdx) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:214-219 Expr.mentionsFvarIns
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:66-68 mentionsFvarIns`
/// — record one answer for `e` in the memo the walk hands back.
pub fn mentions_fvar_ins(e: &EIdx, r: (bool, HashMap<EIdx, bool>)) -> (bool, HashMap<EIdx, bool>) {
    let mut memo: HashMap<EIdx, bool> = r.1;
    memo.insert(e.dup2(), r.0);
    (r.0, memo)
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:139-141 Expr.mentionsFvar
/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:74-111 mentionsFvarGo`
/// — does the variable `q` occur as a leaf of `e` (annotations included, as
/// `fvarLeaves` walks them)?  con-leche's per-call memo, keyed by the node.
pub fn mentions_fvar_go(
    st: &mut AState,
    q: u64,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_MENTIONS_FVAR)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((false, memo)),
            Ok(ENodeView::Sort(_)) => Ok((false, memo)),
            Ok(ENodeView::Const(_, _)) => Ok((false, memo)),
            Ok(ENodeView::Lit(_)) => Ok((false, memo)),
            Ok(v) => match mf_probe(&memo, h) {
                Some(r) => Ok((r, memo)),
                None => match mentions_fvar_node(st, q, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(mentions_fvar_ins(h, r)),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:221-257 Expr.mentionsFvarGo
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:87-110 mentionsFvarGo`
/// — the walk's compound arms, split off so that the `view`'s loans are dead at
/// the memo's join (task #97-P4c's extraction rule 5).
pub fn mentions_fvar_node(
    st: &mut AState,
    q: u64,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(idx, ty) => {
            if idx == q {
                Ok((true, memo))
            } else {
                mentions_fvar_go(st, q, memo, fuel, &ty)
            }
        }
        ENodeView::App(f, a) => match mentions_fvar_go(st, q, memo, fuel, &f) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => mentions_fvar_go(st, q, m, fuel, &a),
        },
        ENodeView::Lam(ty, b, _) => match mentions_fvar_go(st, q, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => mentions_fvar_go(st, q, m, fuel, &b),
        },
        ENodeView::ForallE(ty, b, _) => match mentions_fvar_go(st, q, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => mentions_fvar_go(st, q, m, fuel, &b),
        },
        ENodeView::LetE(t, val, b) => match mentions_fvar_go(st, q, memo, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => match mentions_fvar_go(st, q, m, fuel, &val) {
                Err(e) => Err(e),
                Ok((true, m2)) => Ok((true, m2)),
                Ok((false, m2)) => mentions_fvar_go(st, q, m2, fuel, &b),
            },
        },
        ENodeView::Proj(_, _, sub) => mentions_fvar_go(st, q, memo, fuel, &sub),
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:379-381 Expr.mentionsFvarFast
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:115-116 mentionsFvar`
/// — the executed `mentionsFvar` (one memoized DAG walk).
pub fn mentions_fvar(st: &mut AState, q: u64, e: &EIdx) -> Result<bool, CheckError> {
    match mentions_fvar_go(st, q, HashMap::new(), CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

// ---------------------------------------------------------------------------
// The field kinds, re-checked on the opened constructors
// (`NativeInstall.lean:118-190` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:22-59 nativeOpenedOkF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:124-175 nativeOpenedOk`
/// — the kinds the recogniser computed, re-checked on the annotated
/// constructor type OPENED at variables, in the form the model reads.
#[allow(clippy::too_many_arguments)]
pub fn native_opened_ok(
    st: &mut AState,
    fe0: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    cty: &EIdx,
    n_f: u64,
    ks: &Vec<RecFieldKind>,
) -> Result<bool, CheckError> {
    match checker_base::open_pis_at_fvars_f(st, n_p, cty, 0) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some(pq)) => match checker_base::open_pis_at_fvars_f(st, n_f, &pq.1, n_p) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(xq)) => match struct_parts::param_levels(st, lps) {
                Err(e) => Err(e),
                Ok(us) => match intern_e(st, ENodeView::Const(t.dup2(), us)) {
                    Err(e) => Err(e),
                    Ok(hd) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, &xq.1) {
                        Err(e) => Err(e),
                        Ok(xargs) => {
                            let idx: Vec<EIdx> = core::drop_eidx(&xargs, n_p as usize);
                            match sum_install::idx_args_resolve(st, fe0, &idx, 0) {
                                Err(e) => Err(e),
                                Ok(false) => Ok(false),
                                Ok(true) => native_fields_at(
                                    st, fe0, n_p, n_idx, n_f, ks, &pq.0, &xq.0, &xq.1, &hd, 0,
                                ),
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:137-175 nativeOpenedOk`
/// — the `(List.range nF).allM` of the cited clause, as a counted recursion:
/// one field, at its recognised kind.
#[allow(clippy::too_many_arguments)]
pub fn native_fields_at(
    st: &mut AState,
    fe0: &IFEnv,
    n_p: u64,
    n_idx: u64,
    n_f: u64,
    ks: &Vec<RecFieldKind>,
    fvs_p: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
    hd: &EIdx,
    i: u64,
) -> Result<bool, CheckError> {
    if i >= n_f {
        Ok(true)
    } else if (i as usize) >= x_fvs.len() {
        Ok(false)
    } else {
        let x: EIdx = x_fvs[i as usize].dup2();
        match native_parts::kind_get_d(ks, i) {
            RecFieldKind::Ordinary => match expr_ops::fvar_type_d(st, &x) {
                Err(e) => Err(e),
                Ok(xt) => match checker_base::consts_resolve_f_fast(st, fe0, &xt) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => native_fields_at(
                        st,
                        fe0,
                        n_p,
                        n_idx,
                        n_f,
                        ks,
                        fvs_p,
                        x_fvs,
                        xrest,
                        hd,
                        i + 1,
                    ),
                },
            },
            RecFieldKind::Recursive => {
                match native_field_recursive(st, fe0, n_p, n_idx, fvs_p, x_fvs, xrest, hd, i) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => native_fields_at(
                        st,
                        fe0,
                        n_p,
                        n_idx,
                        n_f,
                        ks,
                        fvs_p,
                        x_fvs,
                        xrest,
                        hd,
                        i + 1,
                    ),
                }
            }
            RecFieldKind::Reflexive => {
                match native_field_reflexive(st, fe0, n_p, n_idx, fvs_p, x_fvs, xrest, hd, i) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => native_fields_at(
                        st,
                        fe0,
                        n_p,
                        n_idx,
                        n_f,
                        ks,
                        fvs_p,
                        x_fvs,
                        xrest,
                        hd,
                        i + 1,
                    ),
                }
            }
            _ => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:140-152 nativeOpenedOk`
/// — a FINITARY recursive field: its annotation is the family at the opened
/// parameters, its indices resolve before the block, and no later field or the
/// residual mentions it.
#[allow(clippy::too_many_arguments)]
pub fn native_field_recursive(
    st: &mut AState,
    fe0: &IFEnv,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
    hd: &EIdx,
    i: u64,
) -> Result<bool, CheckError> {
    let x: EIdx = x_fvs[i as usize].dup2();
    match expr_ops::fvar_type_d(st, &x) {
        Err(e) => Err(e),
        Ok(xt) => match native_fam_app_ok(st, fe0, n_p, n_idx, fvs_p, &xt, hd) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => native_field_unused_later(st, n_p, x_fvs, xrest, i),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:153-174 nativeOpenedOk`
/// — a REFLEXIVE field: its own telescope is opened at the field's depth
/// (con-leche's task #202), its domains resolve before the block, its residual
/// is the family, and no later field or the residual mentions it.
#[allow(clippy::too_many_arguments)]
pub fn native_field_reflexive(
    st: &mut AState,
    fe0: &IFEnv,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<EIdx>,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
    hd: &EIdx,
    i: u64,
) -> Result<bool, CheckError> {
    let x: EIdx = x_fvs[i as usize].dup2();
    match expr_ops::fvar_type_d(st, &x) {
        Err(e) => Err(e),
        Ok(xt) => match native_parts::pi_binders(st, CORE_WALK_FUEL, &xt, Vec::new()) {
            Err(e) => Err(e),
            Ok(tq) => {
                let m: u64 = tq.0.len() as u64;
                match checker_base::open_pis_at_fvars_f(st, m, &xt, n_p + i) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(false),
                    Ok(Some(aq)) => {
                        if aq.0.len() == 0 {
                            Ok(false)
                        } else {
                            match sum_install::field_doms_resolve(st, fe0, &aq.0, 0) {
                                Err(e) => Err(e),
                                Ok(false) => Ok(false),
                                Ok(true) => {
                                    match native_fam_app_ok(st, fe0, n_p, n_idx, fvs_p, &aq.1, hd) {
                                        Err(e) => Err(e),
                                        Ok(false) => Ok(false),
                                        Ok(true) => {
                                            native_field_unused_later(st, n_p, x_fvs, xrest, i)
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:142-148 nativeOpenedOk`
/// — the shared residual test: the family at the opened parameter variables
/// with `nIdx` index arguments, all of which resolve before the block.
#[allow(clippy::too_many_arguments)]
pub fn native_fam_app_ok(
    st: &mut AState,
    fe0: &IFEnv,
    n_p: u64,
    n_idx: u64,
    fvs_p: &Vec<EIdx>,
    body: &EIdx,
    hd: &EIdx,
) -> Result<bool, CheckError> {
    match expr_ops::get_app_fn(st, CORE_WALK_FUEL, body) {
        Err(e) => Err(e),
        Ok(fna) => match expr_ops::get_app_args(st, CORE_WALK_FUEL, body) {
            Err(e) => Err(e),
            Ok(args) => {
                let pre: Vec<EIdx> = expr_ops::take_eidx(&args, n_p as usize);
                if !(fna.eq2(hd)
                    && canon::eidx_vec_beq(&pre, fvs_p, 0)
                    && args.len() as u64 == n_p + n_idx)
                {
                    Ok(false)
                } else {
                    let idx: Vec<EIdx> = core::drop_eidx(&args, n_p as usize);
                    sum_install::idx_args_resolve(st, fe0, &idx, 0)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:149-152 nativeOpenedOk`
/// — no LATER field's annotation and not the residual mentions this field's
/// variable.
pub fn native_field_unused_later(
    st: &mut AState,
    n_p: u64,
    x_fvs: &Vec<EIdx>,
    xrest: &EIdx,
    i: u64,
) -> Result<bool, CheckError> {
    match later_mentions(st, n_p + i, x_fvs, (i + 1) as usize) {
        Err(e) => Err(e),
        Ok(true) => Ok(false),
        Ok(false) => match mentions_fvar(st, n_p + i, xrest) {
            Err(e) => Err(e),
            Ok(r) => Ok(!r),
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:388-433 nativeOpenedOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:149-150 nativeOpenedOk`
/// — the `(xFvs.drop (i + 1)).anyM` of the cited clause.
pub fn later_mentions(
    st: &mut AState,
    q: u64,
    x_fvs: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= x_fvs.len() {
        Ok(false)
    } else {
        let y: EIdx = x_fvs[i].dup2();
        match expr_ops::fvar_type_d(st, &y) {
            Err(e) => Err(e),
            Ok(yt) => match mentions_fvar(st, q, &yt) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => later_mentions(st, q, x_fvs, i + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:61-69 nativeFieldsOkF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:181-190 nativeFieldsOk`
/// — the kinds, re-checked on every annotated constructor, one kind list per
/// constructor, one kind per field.
#[allow(clippy::too_many_arguments)]
pub fn native_fields_ok(
    st: &mut AState,
    fe0: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
) -> Result<bool, CheckError> {
    if ctors_a.len() != kinds.len() {
        Ok(false)
    } else {
        native_fields_ok_from(st, fe0, t, lps, n_p, n_idx, ctors_a, kinds, 0)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:435-445 nativeFieldsOk
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:185-190 nativeFieldsOk`
/// — the cursor recursion behind `native_fields_ok`.
#[allow(clippy::too_many_arguments)]
pub fn native_fields_ok_from(
    st: &mut AState,
    fe0: &IFEnv,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(IConstantVal, u64)>,
    kinds: &Vec<Vec<RecFieldKind>>,
    j: usize,
) -> Result<bool, CheckError> {
    if j >= ctors_a.len() {
        Ok(true)
    } else if kinds[j].len() as u64 != ctors_a[j].1 {
        Ok(false)
    } else {
        let cty: EIdx = ctors_a[j].0.ty.dup2();
        match native_opened_ok(st, fe0, t, lps, n_p, n_idx, &cty, ctors_a[j].1, &kinds[j]) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => native_fields_ok_from(st, fe0, t, lps, n_p, n_idx, ctors_a, kinds, j + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// The recursor (`NativeInstall.lean:192-268` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:71-85 checkNativeRulesF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:198-212 checkNativeRules`
/// — the generated rules for constructors `j, j+1, …` (`k` of them), each
/// scoped at the environment holding the recursor's constant.  Lean conses on
/// the way out; the port pushes on the way in.
#[allow(clippy::too_many_arguments)]
pub fn check_native_rules(
    st: &mut AState,
    fe_r: &IFEnv,
    rlps: &Vec<NIdx>,
    t: &NIdx,
    lps: &Vec<NIdx>,
    elim: &NIdx,
    large: bool,
    n_p: u64,
    n_idx: u64,
    tty: &EIdx,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    rec_c: &NIdx,
    rlvls: &LsIdx,
    k: u64,
    j: u64,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if k == 0 {
        Ok(out)
    } else {
        match native_parts::struct_rec_rhs_r(
            st, t, lps, elim, large, n_p, n_idx, tty, ctors, rec_c, rlvls, j,
        ) {
            Err(e) => Err(e),
            Ok(o) => {
                match checker_base::unwrap_or(o, core_types::internal(code_points(&M_REC_RULE))) {
                    Err(e) => Err(e),
                    Ok(rhs) => match native_rule_scoped(st, fe_r, rlps, &rhs) {
                        Err(e) => Err(e),
                        Ok(false) => fail(core_types::internal(code_points(&M_REC_RULE_SCOPE))),
                        Ok(true) => {
                            let mut o2: Vec<EIdx> = out;
                            o2.push(rhs);
                            check_native_rules(
                                st,
                                fe_r,
                                rlps,
                                t,
                                lps,
                                elim,
                                large,
                                n_p,
                                n_idx,
                                tty,
                                ctors,
                                rec_c,
                                rlvls,
                                k - 1,
                                j + 1,
                                o2,
                            )
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:447-463 checkNativeRules
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:206-209 checkNativeRules`
/// — one generated rule's scoping: level-closed, resolving, `bvar`-closed and
/// fvar-free.  **All four conjuncts run**, as the twin's `unless` does.
pub fn native_rule_scoped(
    st: &mut AState,
    fe_r: &IFEnv,
    rlps: &Vec<NIdx>,
    rhs: &EIdx,
) -> Result<bool, CheckError> {
    match checker_base::all_level_params_defined(st, rlps, rhs) {
        Err(e) => Err(e),
        Ok(w1) => match checker_base::consts_resolve_f_fast(st, fe_r, rhs) {
            Err(e) => Err(e),
            Ok(w2) => match expr_ops::loose_bvars_bounded_fast(st, CORE_WALK_FUEL, 0, rhs) {
                Err(e) => Err(e),
                Ok(w3) => match expr_ops::has_fvar_fast(st, CORE_WALK_FUEL, rhs) {
                    Err(e) => Err(e),
                    Ok(w4) => Ok(w1 && w2 && w3 && !w4),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:87-115 checkNativeRecF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:219-252 checkNativeRec`
/// — stage 3: the recursor, generated and compared — the generated type has
/// the inductive-hypothesis binders in each minor; the generated rules are
/// scoped at the environment holding the recursor's constant.
pub fn check_native_rec(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &NativeParts,
    cv_ta: &IConstantVal,
    ctors_a: &Vec<(IConstantVal, u64)>,
) -> Result<(IConstantVal, Vec<EIdx>), CheckError> {
    const REC: [u32; 3] = [114, 101, 99];
    let t: NIdx = p.shape.cv_t.name.dup2();
    match intern_n_node(st, NNodeView::Str(t.dup2(), code_points(&REC))) {
        Err(e) => Err(e),
        Ok(rec_name) => {
            if !p.shape.cv_r.name.eq2(&rec_name) {
                fail(core_types::invalid(code_points(&M_REC_NAME)))
            } else if !native_parts::native_rec_lps_ok(&p.shape) {
                fail(core_types::invalid(code_points(&M_REC_LPS)))
            } else if !p.rec_pinned {
                fail(core_types::invalid(code_points(&M_REC_PIN)))
            } else {
                match checker_base::check_constant_val(st, mode, fe, &p.shape.cv_r) {
                    Err(e) => Err(e),
                    Ok(cv_ri) => check_native_rec_ty(st, mode, fe, p, cv_ta, ctors_a, &cv_ri.ty),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:232-252 checkNativeRec`
/// — the generated type, its scoping, its own sort, the definitional pin
/// against the stream's, and the generated rules.
#[allow(clippy::too_many_arguments)]
pub fn check_native_rec_ty(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &NativeParts,
    cv_ta: &IConstantVal,
    ctors_a: &Vec<(IConstantVal, u64)>,
    stream_ty: &EIdx,
) -> Result<(IConstantVal, Vec<EIdx>), CheckError> {
    let t: NIdx = p.shape.cv_t.name.dup2();
    let lps: Vec<NIdx> = env::nidx_vec_dup(&p.shape.cv_t.level_params);
    let ctors: Vec<(NIdx, u64, EIdx, Vec<u64>)> =
        native_parts::native_ctors4(ctors_a, &p.kinds, 0, Vec::new());
    match native_parts::struct_rec_ty_r(
        st,
        &t,
        &lps,
        &p.shape.elim,
        p.shape.large,
        p.shape.n_p,
        p.shape.n_idx,
        &cv_ta.ty,
        &ctors,
    ) {
        Err(e) => Err(e),
        Ok(o) => match checker_base::unwrap_or(o, core_types::internal(code_points(&M_REC_TY))) {
            Err(e) => Err(e),
            Ok(rec_ty) => match native_rule_scoped(st, fe, &p.shape.cv_r.level_params, &rec_ty) {
                Err(e) => Err(e),
                Ok(false) => fail(core_types::internal(code_points(&M_REC_TYSC))),
                Ok(true) => {
                    check_native_rec_defeq(st, mode, fe, p, cv_ta, &ctors, stream_ty, rec_ty)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:242-252 checkNativeRec`
/// — the generated type's own sort, the definitional pin, and the rules at the
/// environment holding the recursor's constant.
#[allow(clippy::too_many_arguments)]
pub fn check_native_rec_defeq(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p: &NativeParts,
    cv_ta: &IConstantVal,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    stream_ty: &EIdx,
    rec_ty: EIdx,
) -> Result<(IConstantVal, Vec<EIdx>), CheckError> {
    match core::infer_type_core(st, mode, fe, core::CHECK_FUEL, 0, &rec_ty) {
        Err(e) => Err(e),
        Ok(sty) => match core::ensure_sort_core(st, mode, fe, core::CHECK_FUEL, 0, &sty) {
            Err(e) => Err(e),
            Ok(_u) => {
                match core::is_def_eq_core(st, mode, fe, core::CHECK_FUEL, 0, stream_ty, &rec_ty) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_REC_DEFEQ))),
                    Ok(true) => check_native_rec_rules(st, fe, p, cv_ta, ctors, rec_ty),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:465-502 checkNativeRec
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:247-252 checkNativeRec`
/// — the recursor's constant, provisioned rule-less, and the generated rules
/// at it.
#[allow(clippy::too_many_arguments)]
pub fn check_native_rec_rules(
    st: &mut AState,
    fe: &IFEnv,
    p: &NativeParts,
    cv_ta: &IConstantVal,
    ctors: &Vec<(NIdx, u64, EIdx, Vec<u64>)>,
    rec_ty: EIdx,
) -> Result<(IConstantVal, Vec<EIdx>), CheckError> {
    let cv_ra = IConstantVal {
        name: p.shape.cv_r.name.dup2(),
        level_params: env::nidx_vec_dup(&p.shape.cv_r.level_params),
        ty: rec_ty,
    };
    let stored = IConstantInfo::RecInfo(
        env::i_constant_val_dup(&cv_ra),
        sum_parts::major_idx(&p.shape),
        sum_parts::rule_prefix(&p.shape),
        Vec::new(),
    );
    let fe_r: IFEnv = env::ifenv_push(env::ifenv_dup(fe), stored);
    match struct_parts::param_levels(st, &p.shape.cv_r.level_params) {
        Err(e) => Err(e),
        Ok(rlvls) => {
            let t: NIdx = p.shape.cv_t.name.dup2();
            let lps: Vec<NIdx> = env::nidx_vec_dup(&p.shape.cv_t.level_params);
            match check_native_rules(
                st,
                &fe_r,
                &p.shape.cv_r.level_params,
                &t,
                &lps,
                &p.shape.elim,
                p.shape.large,
                p.shape.n_p,
                p.shape.n_idx,
                &cv_ta.ty,
                ctors,
                &p.shape.cv_r.name,
                &rlvls,
                ctors.len() as u64,
                0,
                Vec::new(),
            ) {
                Err(e) => Err(e),
                Ok(rhss) => Ok((cv_ra, rhss)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:504-519 checkNativeTable
/// con-leche: ConLeche/Kernel/Inductives/NativeInstallF.lean:117-126 checkNativeTableF
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:259-268 checkNativeTable`
/// — stage 4: **the projection table** at a STRUCTURE-LIKE block — one
/// constructor, no index — at the tagged tower's projection offset `1`;
/// nothing at any other block.
pub fn check_native_table(
    st: &mut AState,
    p: &NativeParts,
    ctors_a: &Vec<(IConstantVal, u64)>,
    sortss: &Vec<Vec<LIdx>>,
    fe: IFEnv,
) -> Result<IFEnv, CheckError> {
    if ctors_a.len() != 1 || sortss.len() != 1 || p.shape.n_idx != 0 {
        Ok(fe)
    } else {
        let cty: EIdx = ctors_a[0].0.ty.dup2();
        let n_f: u64 = ctors_a[0].1;
        match struct_parts::struct_proj_guards(st, &cty, p.shape.n_p, n_f, &sortss[0]) {
            Err(e) => Err(e),
            Ok(guards) => struct_install::check_struct_proj_table(
                st,
                &p.shape.cv_t.name,
                &ctors_a[0].0.name,
                &p.shape.cv_t.level_params,
                p.shape.n_p,
                n_f,
                &p.shape.res_sort,
                guards,
                1,
                &ctors_a[0].0,
                fe,
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// The two-pass install (`NativeInstall.lean:270-382` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:521-537 NativePass
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:275-285 NativePass`
/// — **what one pass over the former and the constructors yields**
/// (con-leche's task #268).  Not generic in the environment: the arena has one.
pub struct NativePass {
    /// the environment holding the former, at the record the pass ran at
    pub env1: IFEnv,
    /// the annotated former
    pub cv_ta: IConstantVal,
    /// the completed record: the sort read, the kinds classified
    pub p: NativeParts,
    /// the annotated (normalised) constructors
    pub ctors_a: Vec<(IConstantVal, u64)>,
    /// the fields' sorts, one list per constructor
    pub sortss: Vec<Vec<LIdx>>,
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:291-300 recCtorKindsAll`
/// — `ctorsA.mapM (recCtorKinds T lps nP nIdx)` at the `Option` monad, spelled
/// as an explicit recursion because the twin of `recCtorKinds` is monadic in
/// `AM` and optional in its result.
#[allow(clippy::too_many_arguments)]
pub fn rec_ctor_kinds_all(
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(IConstantVal, u64)>,
    i: usize,
    out: Vec<Vec<RecFieldKind>>,
) -> Result<Option<Vec<Vec<RecFieldKind>>>, CheckError> {
    if i >= ctors_a.len() {
        Ok(Some(out))
    } else {
        match native_parts::rec_ctor_kinds(st, t, lps, n_p, n_idx, &ctors_a[i]) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(ks)) => {
                let mut o: Vec<Vec<RecFieldKind>> = out;
                o.push(ks);
                rec_ctor_kinds_all(st, t, lps, n_p, n_idx, ctors_a, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:306-314 classifyFixKinds`
/// — **the fields' kinds, classified at install** (con-leche's task #210 Part
/// D) on the stored constructors: a non-positive or non-valid occurrence is
/// INVALID, a nested occurrence a positive decline.
pub fn classify_fix_kinds(
    st: &mut AState,
    t: &NIdx,
    lps: &Vec<NIdx>,
    n_p: u64,
    n_idx: u64,
    ctors_a: &Vec<(IConstantVal, u64)>,
) -> Result<Vec<Vec<RecFieldKind>>, CheckError> {
    match rec_ctor_kinds_all(st, t, lps, n_p, n_idx, ctors_a, 0, Vec::new()) {
        Err(e) => Err(e),
        Ok(o) => {
            match checker_base::unwrap_or(o, core_types::not_implemented(code_points(&M_KIND_TELE)))
            {
                Err(e) => Err(e),
                Ok(kinds) => {
                    if kindss_any(&kinds, &RecFieldKind::Negative, 0) {
                        fail(core_types::invalid(code_points(&M_KIND_NEG)))
                    } else if kindss_any(&kinds, &RecFieldKind::Unsupported, 0) {
                        fail(core_types::not_implemented(code_points(&M_KIND_NEST)))
                    } else {
                        Ok(kinds)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:310-313 classifyFixKinds`
/// — `kinds.any (fun ks => ks.any (· == k))`, as a cursor recursion.
pub fn kindss_any(kinds: &Vec<Vec<RecFieldKind>>, k: &RecFieldKind, i: usize) -> bool {
    if i >= kinds.len() {
        false
    } else if kinds_any(&kinds[i], k, 0) {
        true
    } else {
        kindss_any(kinds, k, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:539-554 classifyFixKinds
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:310 classifyFixKinds`
/// — the inner `ks.any (· == k)`.
pub fn kinds_any(ks: &Vec<RecFieldKind>, k: &RecFieldKind, i: usize) -> bool {
    if i >= ks.len() {
        false
    } else if native_parts::rec_field_kind_beq(&ks[i], k) {
        true
    } else {
        kinds_any(ks, k, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:320-329 checkNativePass`
/// — **one pass over the former and the constructors** (con-leche's task #268)
/// at a given `is_rec` verdict.  The last component says whether the
/// classification confirms the verdict the pass ran at.
pub fn check_native_pass(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p0: &NativeParts,
    is_rec: bool,
) -> Result<(NativePass, bool), CheckError> {
    match sum_install::check_sum_ind(st, mode, env::ifenv_dup(fe), &p0.shape, is_rec) {
        Err(e) => Err(e),
        Ok(q) => {
            let fe1: IFEnv = q.0;
            let cv_ta: IConstantVal = q.1;
            let p1: sum_parts::InductiveShape = q.2;
            let p_c: NativeParts = native_parts::complete(p0, p1);
            match sum_install::check_sum_ctors(
                st,
                mode,
                &fe1,
                &fe1,
                &p_c.shape.cv_t.name,
                &p_c.shape.cv_t.level_params,
                p_c.shape.n_p,
                p_c.shape.n_idx,
                &p_c.shape.res_sort,
                p_c.shape.is_prop,
                p_c.shape.large,
                &cv_ta,
                &p_c.shape.ctors,
                0,
                Vec::new(),
                Vec::new(),
            ) {
                Err(e) => Err(e),
                Ok(cq) => check_native_pass_kinds(st, fe1, cv_ta, p_c, cq.0, cq.1, is_rec),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:556-574 checkNativePass
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:326-329 checkNativePass`
/// — the classification, the completed record and the settled test.
#[allow(clippy::too_many_arguments)]
pub fn check_native_pass_kinds(
    st: &mut AState,
    fe1: IFEnv,
    cv_ta: IConstantVal,
    p_c: NativeParts,
    ctors_a: Vec<(IConstantVal, u64)>,
    sortss: Vec<Vec<LIdx>>,
    is_rec: bool,
) -> Result<(NativePass, bool), CheckError> {
    let t: NIdx = p_c.shape.cv_t.name.dup2();
    let lps: Vec<NIdx> = env::nidx_vec_dup(&p_c.shape.cv_t.level_params);
    match classify_fix_kinds(st, &t, &lps, p_c.shape.n_p, p_c.shape.n_idx, &ctors_a) {
        Err(e) => Err(e),
        Ok(kinds) => {
            let p: NativeParts = native_parts::with_kinds(p_c, kinds);
            match native_caps(st, &p) {
                Err(e) => Err(e),
                Ok(a) => match sum_install::native_caps_at(st, &p.shape, is_rec) {
                    Err(e) => Err(e),
                    Ok(b) => {
                        let settled: bool = canon::i_ind_caps_beq(&a, &b);
                        Ok((
                            NativePass {
                                env1: fe1,
                                cv_ta,
                                p,
                                ctors_a,
                                sortss,
                            },
                            settled,
                        ))
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:336-361 checkNativeTail`
/// — **the install after the pass** (con-leche's task #268): the elimination
/// restriction, the index binders' sorts, the kinds re-checked, the stream's
/// rules against the generated ones, the constructors consed, the recursor
/// with its rules, and — at a structure-like block — the projection table.
pub fn check_native_tail(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    q: NativePass,
) -> Result<IFEnv, CheckError> {
    match read_level(st, &q.p.shape.res_sort) {
        Err(e) => Err(e),
        Ok(rs) => {
            let never_zero: bool = level::is_never_zero(&rs);
            if q.p.shape.large && !never_zero && q.p.shape.ctors.len() >= 2 {
                fail(core_types::invalid(code_points(&M_TAIL_ELIM)))
            } else {
                check_native_tail_sorts(st, mode, fe, q)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:344-351 checkNativeTail`
/// — the index binders' universes, exposed for the model's index-tuple
/// universe, and the kinds re-checked on the stored (normalised) constructors.
pub fn check_native_tail_sorts(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    q: NativePass,
) -> Result<IFEnv, CheckError> {
    match checker_base::open_pis_at_fvars_f(st, q.p.shape.n_p + q.p.shape.n_idx, &q.cv_ta.ty, 0) {
        Err(e) => Err(e),
        Ok(o) => {
            match checker_base::unwrap_or(o, core_types::internal(code_points(&M_TAIL_TELE))) {
                Err(e) => Err(e),
                Ok(tq) => {
                    let idx_fvs: Vec<EIdx> = core::drop_eidx(&tq.0, q.p.shape.n_p as usize);
                    let none: Vec<EIdx> = Vec::new();
                    match sum_install::check_struct_field_sorts_i(
                        st,
                        mode,
                        &q.env1,
                        true,
                        false,
                        &q.p.shape.res_sort,
                        q.p.shape.n_p,
                        &idx_fvs,
                        &none,
                        q.p.shape.n_idx,
                    ) {
                        Err(e) => Err(e),
                        Ok(_isorts) => check_native_tail_kinds(st, mode, fe, q),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:349-361 checkNativeTail`
/// — the kinds re-checked, the stream's rules against the generated ones, and
/// the install.
pub fn check_native_tail_kinds(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    q: NativePass,
) -> Result<IFEnv, CheckError> {
    let t: NIdx = q.p.shape.cv_t.name.dup2();
    let lps: Vec<NIdx> = env::nidx_vec_dup(&q.p.shape.cv_t.level_params);
    match native_fields_ok(
        st,
        fe,
        &t,
        &lps,
        q.p.shape.n_p,
        q.p.shape.n_idx,
        &q.ctors_a,
        &q.p.kinds,
    ) {
        Err(e) => Err(e),
        Ok(false) => fail(core_types::internal(code_points(&M_TAIL_KINDS))),
        Ok(true) => match struct_parts::param_levels(st, &q.p.shape.cv_r.level_params) {
            Err(e) => Err(e),
            Ok(rlvls) => {
                let pw = prop_when::never();
                match native_parts::native_rules_ok(
                    st,
                    &q.p.shape.cv_r.name,
                    &rlvls,
                    &pw,
                    q.p.shape.n_p,
                    q.p.shape.ctors.len() as u64,
                    &q.ctors_a,
                    &q.p.kinds,
                    &q.p.shape.rhss,
                    &q.p.shape.cv_r.ty,
                ) {
                    Err(e) => Err(e),
                    Ok(false) => fail(core_types::invalid(code_points(&M_TAIL_RULES))),
                    Ok(true) => check_native_tail_install(st, mode, q),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:576-611 checkNativeTail
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:357-361 checkNativeTail`
/// — the constructors consed, the recursor with its rules, and the projection
/// table.
pub fn check_native_tail_install(
    st: &mut AState,
    mode: &CheckMode,
    q: NativePass,
) -> Result<IFEnv, CheckError> {
    let fe2: IFEnv = sum_install::cons_sum_ctors(q.p.shape.n_p, &q.ctors_a, 0, q.env1);
    match check_native_rec(st, mode, &fe2, &q.p, &q.cv_ta, &q.ctors_a) {
        Err(e) => Err(e),
        Ok(rq) => {
            let cv_ra: IConstantVal = rq.0;
            let rhss: Vec<EIdx> = rq.1;
            match sum_install::sum_rules(
                st,
                &fe2,
                &cv_ra.name,
                q.p.shape.n_p,
                sum_parts::major_idx(&q.p.shape),
                sum_parts::rule_prefix(&q.p.shape),
                &cv_ra.ty,
                &q.ctors_a,
                &rhss,
                0,
                Vec::new(),
            ) {
                Err(e) => Err(e),
                Ok(rules) => {
                    let stored = IConstantInfo::RecInfo(
                        env::i_constant_val_dup(&cv_ra),
                        sum_parts::major_idx(&q.p.shape),
                        sum_parts::rule_prefix(&q.p.shape),
                        rules,
                    );
                    let fe3: IFEnv = env::ifenv_push(fe2, stored);
                    check_native_table(st, &q.p, &q.ctors_a, &q.sortss, fe3)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:367-380 checkNative`
/// — check and install a **direct recursive block**: the distinct names, the
/// pass over the former and the constructors — again where the record's
/// syntactic reading overshot — and the install after it.
pub fn check_native(
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    p0: &NativeParts,
) -> Result<IFEnv, CheckError> {
    if !ctor_names_nodup(&p0.shape.ctors, 0) {
        fail(core_types::invalid(code_points(&M_NAT_DUP)))
    } else {
        match native_raw_rec(st, p0) {
            Err(e) => Err(e),
            Ok(raw) => match check_native_pass(st, mode, fe, p0, raw) {
                Err(e) => Err(e),
                Ok(q) => {
                    if q.1 {
                        check_native_tail(st, mode, fe, q.0)
                    } else {
                        let again: bool = native_is_rec(&q.0.p.kinds);
                        match check_native_pass(st, mode, fe, p0, again) {
                            Err(e) => Err(e),
                            Ok(q2) => {
                                if q2.1 {
                                    check_native_tail(st, mode, fe, q2.0)
                                } else {
                                    fail(core_types::internal(code_points(&M_NAT_SETTLE)))
                                }
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:368 checkNative`
/// — `(p₀.ctors.map (·.1.name)).Nodup`, as a cursor recursion over handles.
pub fn ctor_names_nodup(ctors: &Vec<(IConstantVal, u64)>, i: usize) -> bool {
    if i >= ctors.len() {
        true
    } else if ctor_name_seen(ctors, i + 1, &ctors[i].0.name) {
        false
    } else {
        ctor_names_nodup(ctors, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Inductives/NativeInstall.lean:613-640 checkNative
/// Lean twin: `proof/ConRon/Arena/Inductives/NativeInstall.lean:368 checkNative`
/// — the inner scan of `ctor_names_nodup`.
pub fn ctor_name_seen(ctors: &Vec<(IConstantVal, u64)>, i: usize, n: &NIdx) -> bool {
    if i >= ctors.len() {
        false
    } else if ctors[i].0.name.eq2(n) {
        true
    } else {
        ctor_name_seen(ctors, i + 1, n)
    }
}
