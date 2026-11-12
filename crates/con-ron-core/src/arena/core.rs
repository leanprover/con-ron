//! `arena::core` — the checker core of (C), over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Core.lean`, which is
//! `ConLeche/Kernel/Core.lean` clause for clause over handles: the five bodies
//! (`whnf_core`, `whnf`, `infer`, `infer_io`, `defeq`; task #119 deleted the
//! sixth, `annotate`, with con-leche's task #342), the
//! helpers they call, the knot that ties them at fuel,
//! `ConLeche/Kernel/TypeChecker.lean`'s seven fueled entry points, and the
//! per-declaration bracket.
//!
//! ## The six systematic deviations are the twin's
//!
//! They are written out at the top of `Core.lean` and summarised in
//! DESIGN.md's task #97c section; nothing here adds to them.  In one line
//! each: `env : Env` is `fe : &IFEnv` (one environment type, so every
//! `…Of`/`…F` pair of con-leche declarations collapses into one twin); every
//! structural match on a term is a `view` and every walk takes an explicit
//! fuel; reserved names are INTERNED and compared by handle; levels are read
//! back and only the VERDICT is cached; there is ONE knot, the memoized one;
//! and the memo probes are inline in the knot's slots, so the bodies stay
//! pure of memo logic.
//!
//! ## The two deviations this module adds, both forced by §3.4
//!
//! 1. **`r : CoreFnsA` is `(lane, fuel)`.**  The twin's knot is a *record of
//!    functions* passed to every body; §3.4 forbids closures, and a record of
//!    function fields is what `con_ron_core::cached::core_c` already refuses
//!    to port ("§3.1 ties the knot with a mutually recursive block of plain
//!    functions, so there is no record whose `infer` field can be rebound").
//!    So the knot is six plain mutually recursive functions — `knot_whnf_core`
//!    and its five siblings — and the *identity of the record* is the one
//!    thing a body still has to be told, because the arena has two knots:
//!    `coreKnot` (LANE_FULL, memoized) and `coreKnotIO` (LANE_IO,
//!    `arena::core_io`, no memo; con-leche's gated knot `coreKnotGated` went
//!    with the modeled route).  It is told as a `lane: u32`, threaded
//!    beside `mode` through every function whose twin takes `r`.  That is
//!    defunctionalization of the twin's one higher-order argument, and it is
//!    the same move §3.4 asks for at `kernel::expr_ops::rename_consts`'
//!    `f : Name → Name` (its `NameToName` bound).  The official kernel's
//!    `m_eager_reduce` flag travels the same way, `eager: bool` right after
//!    `mode`: con-leche's `coreKnot mode eager` captures it in the record, and
//!    with no record every body that reaches a slot passes it on.
//!
//!    `CoreFnsA.ioView` — `{ r with infer := r.inferIO }`, the *one* place
//!    the record is rebound — is the extra `io: bool` of `infer_body_io`,
//!    exactly as `con_ron_core::cached::core_c::infer_at_i` spells it ("this
//!    function *is* the `ioView` substitution in the port").  No other body
//!    or helper calls `r.infer`, so no other one carries it.
//! 2. **The loops' steps RETURN their continuation** (task #119, con-leche
//!    task #342 R2).  con-leche's `whnfCoreStep`/`whnfStep` return a
//!    `WhnfStep` (`.done e` / `.cont e`) to a loop that iterates in constant
//!    stack; the port's `whnf_core_loop` and `whnf_loop` are real `loop`s
//!    (`// lint: allow`, DESIGN.md §3.4) over `WhnfStep`, because Rust has no
//!    guaranteed tail call and a recursive loop would grow the native stack per
//!    step — the very overflow R2 removed.  (The two lazy-delta loops,
//!    `lazyDeltaReduction` and `lazyDeltaProjReduction`, recurse on their
//!    budget directly and so do their ports.)
//!
//! `coreKnot`'s `wrap : CoreFnsA → CoreFnsA` parameter is dropped: `pureFnsA`
//! is `coreKnot mode fe id` and `id` is its only instantiation in the whole
//! twin.
//!
//! ## Three smaller shapes worth naming
//!
//! * **`defeqBody` and `lazyDeltaStep` are several functions here**
//!   (`defeq_body` → `defeq_unreduced` → `defeq_after_whnf` → `defeq_after_lazy`;
//!   `lazy_delta_step` → `lazy_delta_side`/`lazy_delta_both` →
//!   `lazy_delta_one`/`lazy_delta_unfold_both`): inlined, each would nest
//!   twenty deep.  Every cited clause is still in the twin's order; the split
//!   points are the twin's own `let`- and `match`-boundaries, and a mirrored
//!   pair of arms (the two one-sided δ branches) is one function with a
//!   `flipped` flag.
//! * **The twin's `match ← view a, ← view b` is `match (va, vb)`**, arm for
//!   arm in the twin's order, with `defeqStuck`'s two `(lit, app)` arms merged
//!   into one (`defeq_str_app`) that dispatches on the literal's kind — the
//!   scrutinee pair is fixed, so merging two arms that differ only in the
//!   side the literal is on changes nothing.
//! * **Messages are `con_ron_core`'s**, code point for code point, with the
//!   twin's interpolation dropped (DESIGN.md §3.1: message strings need not
//!   match a theorem, and matching the *shipping port's* is what lets the
//!   differential test compare whole outcomes including error text).

use crate::arena::core_state::{
    eidx_pair, lidx_pair,
    lsidx_pair, nls_key, nnls_key, EIdxPair, LIdxPair, LsIdxPair, ModeMemos, NLsKey, NNLsKey,
};
use crate::arena::env;
use crate::arena::env::{
    IConstantInfo, IConstantVal, IFEnv, IIndCaps, IProjEntry, IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::expr_ops::{
    abstract1_fast, abstract_range_fast, cons_eidx, get_app_args, get_app_fn,
    has_fvar_fast, instantiate1_fast, instantiate_list_fast, inst_lp_fast, inst_spine, binder_pair,
    leaf_guard, loose_bvars_bounded_fast, mk_app_n, mk_app_n_from, pi_result,
    snoc_eidx_of,
    take_eidx, take_eidx_n, wscoped_b_fast,
};
use crate::arena::handle::{
    EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR, ETAG_LAM,
    ETAG_LET_E,
    ETAG_LIT, ETAG_PROJ, ETAG_SORT,
};
use crate::arena::monad::{
    AState, fail, fail_dangling_e, fail_dangling_ls, intern_e_app, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_fvar, intern_e_lam, intern_e_let_e, intern_e_lit, intern_e_proj, intern_e_sort, intern_l_node, intern_level, intern_ls_node, read_level_m, read_levels_m, read_name_m, read_names_m, view, view_app, view_bind, view_bvar, view_const, view_const_name, view_lit, view_ls, view_ls_len, view_sort,
};
use crate::arena::prop_read::{is_proof_fast, not_proof_fast, peel_pis};
use crate::arena::store::{ENodeView, LNodeView};
use crate::arena::pins::{pin_and, pin_and_intro, pin_reserved, pin_bool, pin_bool_false, pin_bool_true, pin_char, pin_eager_reduce, pin_char_of_nat, pin_empty_levels, pin_list, pin_list_cons, pin_list_nil, pin_nat, pin_nat_add, pin_nat_beq, pin_nat_ble, pin_nat_div, pin_nat_gcd, pin_nat_land, pin_nat_lor, pin_nat_mod, pin_nat_mul, pin_nat_pow, pin_nat_pred, pin_nat_shift_left, pin_nat_shift_right, pin_nat_sub, pin_nat_succ, pin_nat_xor, pin_nat_zero, pin_sorry_ax, pin_sort_one, pin_string, pin_string_of_list, pin_zero_level, max_nat_size};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::{verified_checks, CheckMode, ReducibilityHint};
use crate::kernel::expr;
use crate::kernel::expr::Literal;
use crate::kernel::expr_ops::sub_nat;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::arena::expr_ops;
use crate::arena::monad::{eidx_nat_key, EIdxNat};
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::nat;
use crate::ron::nat::Nat;
use std::vec::Vec;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: getAppSpine"`, as code points.
pub const M_FUEL_WHNF_SPINE: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 103, 101,
    116, 65, 112, 112, 83, 112, 105, 110, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `resource limit: fuel exhausted: level comparison`, as code points.
pub const M_FUEL_LEVEL_CMP: [u32; 48] = [
    114, 101, 115, 111, 117, 114, 99, 101, 32, 108, 105, 109, 105, 116, 58, 32, 102, 117, 101, 108,
    32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 101, 118, 101, 108, 32, 99, 111,
    109, 112, 97, 114, 105, 115, 111, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: constsResolve"`, as code points.
pub const M_FUEL_CONSTS_RESOLVE: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 111,
    110, 115, 116, 115, 82, 101, 115, 111, 108, 118, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: substConst0"`, as code points.
pub const M_FUEL_SUBST_CONST0: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 115, 117,
    98, 115, 116, 67, 111, 110, 115, 116, 48
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: substConstAll"`, as code points.
pub const M_FUEL_SUBST_CONST_ALL: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 115, 117,
    98, 115, 116, 67, 111, 110, 115, 116, 65, 108, 108
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"use of the sorryAx axiom"`, as code points.
pub const M_SORRY: [u32; 24] = [
    117, 115, 101, 32, 111, 102, 32, 116, 104, 101, 32, 115, 111, 114, 114, 121, 65, 120,
    32, 97, 120, 105, 111, 109
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"unknown constant"`, as code points.
pub const M_UNKNOWN_CONST: [u32; 16] = [
    117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"native Nat computation on literals"`, as code points.
pub const M_NATIVE_NAT: [u32; 34] = [
    110, 97, 116, 105, 118, 101, 32, 78, 97, 116, 32, 99, 111, 109, 112, 117, 116, 97, 116,
    105, 111, 110, 32, 111, 110, 32, 108, 105, 116, 101, 114, 97, 108, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"whnf beyond the supported fragment"`, as code points.
pub const M_BVAR_WHNF: [u32; 34] = [
    119, 104, 110, 102, 32, 98, 101, 121, 111, 110, 100, 32, 116, 104, 101, 32, 115, 117,
    112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109, 101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: whnfCore loop"`, as code points.
pub const M_FUEL_WHNF_CORE_LOOP: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104, 110,
    102, 67, 111, 114, 101, 32, 108, 111, 111, 112,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: whnf loop"`, as code points.
pub const M_FUEL_WHNF_LOOP: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
    110, 102, 32, 108, 111, 111, 112
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"expected a sort"`, as code points.
pub const M_SORT: [u32; 15] = [
    101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"application type mismatch"`, as code points.
pub const M_APP_MISMATCH: [u32; 25] = [
    97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 109,
    105, 115, 109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"function expected"`, as code points.
pub const M_FN: [u32; 17] = [
    102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"incorrect number of universe levels"`, as code points.
pub const M_LEVELS: [u32; 35] = [
    105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
    102, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"inferType beyond the supported fragment"`, as code points.
pub const M_BVAR_INFER: [u32; 39] = [
    105, 110, 102, 101, 114, 84, 121, 112, 101, 32, 98, 101, 121, 111, 110, 100, 32, 116,
    104, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109,
    101, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection without a native entry"`, as code points.
pub const M_NOENTRY: [u32; 33] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 119, 105, 116, 104, 111, 117, 116,
    32, 97, 32, 110, 97, 116, 105, 118, 101, 32, 101, 110, 116, 114, 121
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection from a structure whose type reaches no sort"`, as code points.
pub const M_PROJ_NO_SORT: [u32; 54] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32, 115,
    116, 114, 117, 99, 116, 117, 114, 101, 32, 119, 104, 111, 115, 101, 32, 116, 121, 112, 101,
    32, 114, 101, 97, 99, 104, 101, 115, 32, 110, 111, 32, 115, 111, 114, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection from a propositional structure must be a proposition"`, as code points.
pub const M_PROP: [u32; 63] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32,
    112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 115, 116, 114, 117,
    99, 116, 117, 114, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 32, 112, 114, 111,
    112, 111, 115, 105, 116, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: defeq loop"`, as code points.
pub const M_FUEL_DEFEQ_LOOP: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101,
    102, 101, 113, 32, 108, 111, 111, 112
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: lazy delta projection loop"`, as code points.
pub const M_FUEL_PROJ_LOOP: [u32; 42] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 97, 122, 121, 32, 100, 101, 108, 116, 97, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 108, 111, 111, 112
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"free variable out of scope"`, as code points.
pub const M_FVAR: [u32; 26] = [
    102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 111, 117, 116, 32,
    111, 102, 32, 115, 99, 111, 112, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"Nat literal without the Nat basis declarations"`, as code points.
pub const M_NAT: [u32; 46] = [
    78, 97, 116, 32, 108, 105, 116, 101, 114, 97, 108, 32, 119, 105, 116, 104, 111, 117,
    116, 32, 116, 104, 101, 32, 78, 97, 116, 32, 98, 97, 115, 105, 115, 32, 100, 101, 99,
    108, 97, 114, 97, 116, 105, 111, 110, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"string literals before the String support declarations"`, as code points.
pub const M_STR: [u32; 54] = [
    115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 98, 101,
    102, 111, 114, 101, 32, 116, 104, 101, 32, 83, 116, 114, 105, 110, 103, 32, 115, 117,
    112, 112, 111, 114, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115
];

/// con-leche: ConLeche/Cached/StateC.lean:165-168 natNumeralTooBig
/// The port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3):
/// `"the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size"`, as code points.
pub const M_NAT_NUMERAL_TOO_BIG: [u32; 101] = [
    116, 104, 101, 32, 107, 101, 114, 110, 101, 108, 32, 114, 101, 102, 117, 115, 101, 100,
    32, 97, 32, 96, 78, 97, 116, 96, 32, 110, 117, 109, 101, 114, 97, 108, 32, 98,
    101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 115, 105, 122, 101, 32, 101, 120,
    99, 101, 101, 100, 115, 32, 116, 104, 101, 32, 109, 97, 120, 105, 109, 117, 109, 59,
    32, 114, 97, 105, 115, 101, 32, 105, 116, 32, 119, 105, 116, 104, 32, 45, 45, 109,
    97, 120, 45, 110, 97, 116, 45, 115, 105, 122, 101
];

/// con-leche: ConLeche/Cached/StateC.lean:170-173 natCountTooBig
/// The port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3):
/// `"the kernel refused to evaluate `Nat.pow` because its second argument does not fit in a 32-bit unsigned integer"`, as code points.
pub const M_NAT_POW_COUNT: [u32; 110] = [
    116, 104, 101, 32, 107, 101, 114, 110, 101, 108, 32, 114, 101, 102, 117, 115, 101, 100,
    32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 96, 78, 97, 116, 46,
    112, 111, 119, 96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 115,
    101, 99, 111, 110, 100, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 100, 111, 101,
    115, 32, 110, 111, 116, 32, 102, 105, 116, 32, 105, 110, 32, 97, 32, 51, 50, 45,
    98, 105, 116, 32, 117, 110, 115, 105, 103, 110, 101, 100, 32, 105, 110, 116, 101, 103,
    101, 114
];

/// con-leche: ConLeche/Cached/StateC.lean:170-173 natCountTooBig
/// The port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3):
/// `"the kernel refused to evaluate `Nat.shiftLeft` because its second argument does not fit in a 32-bit unsigned integer"`, as code points.
pub const M_NAT_SHIFT_COUNT: [u32; 116] = [
    116, 104, 101, 32, 107, 101, 114, 110, 101, 108, 32, 114, 101, 102, 117, 115, 101, 100,
    32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 96, 78, 97, 116, 46,
    115, 104, 105, 102, 116, 76, 101, 102, 116, 96, 32, 98, 101, 99, 97, 117, 115, 101,
    32, 105, 116, 115, 32, 115, 101, 99, 111, 110, 100, 32, 97, 114, 103, 117, 109, 101,
    110, 116, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 102, 105, 116, 32, 105, 110,
    32, 97, 32, 51, 50, 45, 98, 105, 116, 32, 117, 110, 115, 105, 103, 110, 101, 100,
    32, 105, 110, 116, 101, 103, 101, 114
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; raise it with --max-nat-size"`, as code points.
pub const M_NAT_POW_TOO_BIG: [u32; 127] = [
    116, 104, 101, 32, 107, 101, 114, 110, 101, 108, 32, 114, 101, 102, 117, 115, 101, 100,
    32, 116, 111, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 96, 78, 97, 116, 46,
    112, 111, 119, 96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 32, 114,
    101, 115, 117, 108, 116, 32, 119, 111, 117, 108, 100, 32, 101, 120, 99, 101, 101, 100,
    32, 116, 104, 101, 32, 109, 97, 120, 105, 109, 117, 109, 32, 110, 117, 109, 101, 114,
    97, 108, 32, 115, 105, 122, 101, 59, 32, 114, 97, 105, 115, 101, 32, 105, 116, 32,
    119, 105, 116, 104, 32, 45, 45, 109, 97, 120, 45, 110, 97, 116, 45, 115, 105, 122,
    101
];


/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"let value type mismatch"`, as code points.
pub const M_LET_VALUE: [u32; 23] = [
    108, 101, 116, 32, 118, 97, 108, 117, 101, 32, 116, 121, 112, 101, 32, 109, 105, 115,
    109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"invalid projection: the node names another structure"`, as code points.
pub const M_OTHER_STRUCT: [u32; 52] = [
    105, 110, 118, 97, 108, 105, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
    58, 32, 116, 104, 101, 32, 110, 111, 100, 101, 32, 110, 97, 109, 101, 115, 32, 97, 110,
    111, 116, 104, 101, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection parameter mismatch"`, as code points.
pub const M_PARAMS: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 112, 97, 114, 97, 109, 101, 116,
    101, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection index out of range"`, as code points.
pub const M_RANGE: [u32; 29] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 110, 100, 101, 120, 32, 111,
    117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `projection on an indexed structure-like type`, as code points.
pub const M_INDEXED_PROJ: [u32; 44] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 110, 32, 97, 110, 32, 105, 110, 100,
    101, 120, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 45, 108, 105, 107, 101, 32,
    116, 121, 112, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `invalid projection: not a structure-like type, or no such field`, as code points.
pub const M_INVALID_PROJ: [u32; 63] = [
    105, 110, 118, 97, 108, 105, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 58, 32,
    110, 111, 116, 32, 97, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 45, 108, 105, 107, 101,
    32, 116, 121, 112, 101, 44, 32, 111, 114, 32, 110, 111, 32, 115, 117, 99, 104, 32, 102, 105,
    101, 108, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: whnfCore"`, as code points.
pub const M_FUEL_WHNF_CORE: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
    110, 102, 67, 111, 114, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: whnf"`, as code points.
pub const M_FUEL_WHNF: [u32; 20] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
    110, 102
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: infer"`, as code points.
pub const M_FUEL_INFER: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110,
    102, 101, 114
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: defeq"`, as code points.
pub const M_FUEL_DEFEQ: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101,
    102, 101, 113
];

// ---------------------------------------------------------------------------
// The lanes: the twin's `r : CoreFnsA`, defunctionalized (the module note)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — **the
/// executed knot**: the memoized one, `pureFnsA`'s.
pub const LANE_FULL: u32 = 0;

/// con-leche: ConLeche/Kernel/CoreIO.lean:44-66 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — the io knot
/// (the leaf lane): `infer` and `inferIO` are `inferBodyIO` tied to this knot,
/// unmemoized; every other slot is the full knot's.
pub const LANE_IO: u32 = 2;

// ---------------------------------------------------------------------------
// Fuel for the store walks (`Core.lean:74-86`)
// ---------------------------------------------------------------------------

/// con-leche: none — the fuel every store walk in this module runs at
/// Lean twin: `proof/ConRon/Arena/Core.lean:89-91 coreWalkFuel`.  DESIGN.md §8.4
/// asks for fuel as an explicit `Nat`; the walks below are over the handle
/// DAG, so any bound above the store's node count is unreachable.
/// `4 000 000 000` is above the representable expression-node count (per
/// tier, 2^30 `app` nodes and 2^26 of each of the nine other constructors;
/// two tiers: 3 355 443 200) and below `2^63`, so it is one machine word.
pub const CORE_WALK_FUEL: u64 = 4000000000;

// ---------------------------------------------------------------------------
// Reserved names, interned (`Core.lean:88-130`)
// ---------------------------------------------------------------------------

/// con-leche: none — the empty universe-argument list, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:112-114 emptyLevels` — `us ==
/// emptyLevels` is con-leche's pattern `.const _ []`.
///
/// **Task #97-P6-4a: read off `arena::pins`, not interned.**  The twin's
/// `internLs []` and this read hand back the same handle, because
/// `intern_reserved_pins` interned exactly this node at startup and `intern` is
/// idempotent on a hash-consed store.  `&AState`, not `&mut`: the state is
/// only read, which is what lets the callers below keep their borrow.
pub fn empty_levels(st: &AState) -> Result<LsIdx, CheckError> {
    pin_empty_levels(st)
}

/// con-leche: none — the level `0`, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:116-118 zeroLevel` — the comparand of
/// every `Level.isEquiv u .zero` in this module.  Task #97-P6-4a: the pin.
pub fn zero_level(st: &AState) -> Result<LIdx, CheckError> {
    pin_zero_level(st)
}

/// con-leche: none — the expression `Sort 1`, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:120-122 sortOne` — the pinned type
/// of `Nat`, `String`, `Char` and `Bool`.  Task #97-P6-4a: the pin, which
/// saves three interns (the level `0`, its successor and the `sort` node) on
/// every call.
pub fn sort_one(st: &AState) -> Result<EIdx, CheckError> {
    pin_sort_one(st)
}

/// con-leche: none — a level-monomorphic constant `.const n []`, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:124-128 constE`.
pub fn const_e(pers: &PersTier, st: &mut AState, n: &NIdx) -> Result<EIdx, CheckError> {
    match empty_levels(st) {
        Err(e) => Err(e),
        Ok(us) => intern_e_const(pers, st, n.dup2(), us),
    }
}

// ---------------------------------------------------------------------------
// The level verdicts, cached (`Core.lean:132-176`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:164-169 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:136-153 lvlEq?` — the verdict probe, as
/// its own function over a *shared* state borrow (task #97-P4a's rule, and
/// `con_ron_core::cached::core_c::whnf_core_probe`'s reason): the table's
/// borrow ends with the lookup, so the miss branch can take the state mutably
/// again.  Inlined, Aeneas cannot join the two arms' loan contexts ("Could
/// not match the contexts", `interp/Interp.ml:617`).
pub fn lvl_eq_probe(st: &AState, k: &LIdxPair) -> Option<bool> {
    match st.caches.lvl_eq_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:164-169 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:136-153 lvlEq?` — `Level.isEquiv`
/// at two level HANDLES, with the verdict cached on the pair.  `None` is
/// con-leche's fuel exhaustion and is never cached.  The twin's
/// detach-before-update (lesson 14) has no Rust counterpart: `&mut` IS the
/// unique reference the detaching manufactures.
pub fn lvl_eq(
    pers: &PersTier,
    st: &mut AState,
    u: &LIdx,
    v: &LIdx,
) -> Result<Option<bool>, CheckError>  {
    let k: LIdxPair = lidx_pair(u, v);
    match lvl_eq_probe(st, &k) {
        Some(r) => Ok(Some(r)),
        None => match read_level_m(pers, st, u) {
            Err(e) => Err(e),
            Ok(lu) => match read_level_m(pers, st, v) {
                Err(e) => Err(e),
                Ok(lv) => match level::is_equiv(&lu, &lv) {
                    Some(r) => {
                        lvl_eq_set(st, k, r);
                        Ok(Some(r))
                    }
                    None => Ok(None),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:164-169 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:136-153 lvlEq?` — the record half
/// of the probe.  No cap: con-leche's tables have none, and task #115
/// removed the port's (`arena::core_state`'s module note).
pub fn lvl_eq_set(st: &mut AState, k: LIdxPair, r: bool) {
    let _ = st.caches.lvl_eq_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/Level.lean:169-175 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:155-172 lvlsEq?` — the verdict probe, as
/// its own function over a *shared* state borrow (task #97-P4a's rule, and
/// `con_ron_core::cached::core_c::whnf_core_probe`'s reason): the table's
/// borrow ends with the lookup, so the miss branch can take the state mutably
/// again.  Inlined, Aeneas cannot join the two arms' loan contexts ("Could
/// not match the contexts", `interp/Interp.ml:617`).
pub fn lvls_eq_probe(st: &AState, k: &LsIdxPair) -> Option<bool> {
    match st.caches.lvls_eq_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:169-175 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:155-172 lvlsEq?` — pairwise
/// `Level.isEquiv` at two universe-argument LIST handles, cached on the pair.
pub fn lvls_eq(
    pers: &PersTier,
    st: &mut AState,
    us: &LsIdx,
    vs: &LsIdx,
) -> Result<Option<bool>, CheckError>  {
    let k: LsIdxPair = lsidx_pair(us, vs);
    match lvls_eq_probe(st, &k) {
        Some(r) => Ok(Some(r)),
        None => match read_levels_m(pers, st, us) {
            Err(e) => Err(e),
            Ok(lu) => match read_levels_m(pers, st, vs) {
                Err(e) => Err(e),
                Ok(lv) => match level::is_equiv_list(&lu, &lv) {
                    Some(r) => {
                        lvls_eq_set(st, k, r);
                        Ok(Some(r))
                    }
                    None => Ok(None),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:169-175 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:155-172 lvlsEq?` — the record half.
pub fn lvls_eq_set(st: &mut AState, k: LsIdxPair, r: bool) {
    let _ = st.caches.lvls_eq_c.insert(k, r);
}

// ---------------------------------------------------------------------------
// The lazy instantiated-constant caches (`Core.lean:178-235`)
// ---------------------------------------------------------------------------

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:182-195 constTyAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn const_ty_probe(st: &AState, k: &NLsKey) -> Option<EIdx> {
    match st.caches.const_ty_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache, `constTyAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:182-195 constTyAt` — a stored
/// constant's TYPE at a universe instantiation, memoized on `(name, levels)`.
/// The key is never the instantiated term, which is the point: the
/// instantiation is what the cache avoids computing.
pub fn const_ty_at(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    us: &LsIdx,
) -> Result<EIdx, CheckError> {
    let k: NLsKey = nls_key(&cv.name, us);
    match const_ty_probe(st, &k) {
        Some(r) => Ok(r),
        None => match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cv.level_params, us, &cv.ty) {
            Err(e) => Err(e),
            Ok(r) => {
                const_ty_set(st, k, &r);
                Ok(r)
            }
        },
    }
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:182-195 constTyAt` — the record half.
pub fn const_ty_set(st: &mut AState, k: NLsKey, r: &EIdx) {
    let _ = st.caches.const_ty_c.insert(k, r.dup2());
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:197-211 constValAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn const_val_probe(st: &AState, k: &NLsKey) -> Option<EIdx> {
    match st.caches.const_val_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's `constValAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:197-211 constValAt` — a stored
/// definition's VALUE at a universe instantiation, memoized on `(name,
/// levels)`.  The delta step's only expensive half.
pub fn const_val_at(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    lps: &Vec<NIdx>,
    value: &EIdx,
    us: &LsIdx,
) -> Result<EIdx, CheckError> {
    let k: NLsKey = nls_key(n, us);
    match const_val_probe(st, &k) {
        Some(r) => Ok(r),
        None => match inst_lp_fast(pers, st, CORE_WALK_FUEL, lps, us, value) {
            Err(e) => Err(e),
            Ok(r) => {
                const_val_set(st, k, &r);
                Ok(r)
            }
        },
    }
}

/// con-leche: none — DESIGN.md §8.3's `constValAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:197-211 constValAt` — the record half.
pub fn const_val_set(st: &mut AState, k: NLsKey, r: &EIdx) {
    let _ = st.caches.const_val_c.insert(k, r.dup2());
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:213-228 ruleRhsAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn rule_rhs_probe(st: &AState, k: &NNLsKey) -> Option<EIdx> {
    match st.caches.rule_rhs_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's `ruleRhsAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:213-228 ruleRhsAt` — an iota
/// rule's right-hand side at the recursor's universe instantiation, memoized
/// on `(recursor, rule constructor, levels)` — the three data that determine
/// it.
pub fn rule_rhs_at(
    pers: &PersTier,
    st: &mut AState,
    rec_name: &NIdx,
    ctor: &NIdx,
    lps: &Vec<NIdx>,
    rhs: &EIdx,
    us: &LsIdx,
) -> Result<EIdx, CheckError> {
    let k: NNLsKey = nnls_key(rec_name, ctor, us);
    match rule_rhs_probe(st, &k) {
        Some(r) => Ok(r),
        None => match inst_lp_fast(pers, st, CORE_WALK_FUEL, lps, us, rhs) {
            Err(e) => Err(e),
            Ok(r) => {
                rule_rhs_set(st, k, &r);
                Ok(r)
            }
        },
    }
}

/// con-leche: none — DESIGN.md §8.3's `ruleRhsAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:213-228 ruleRhsAt` — the record half.
pub fn rule_rhs_set(st: &mut AState, k: NNLsKey, r: &EIdx) {
    let _ = st.caches.rule_rhs_c.insert(k, r.dup2());
}

// ---------------------------------------------------------------------------
// The error (`Core.lean:237-249`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:50-68 unknownConstError
/// Lean twin: `proof/ConRon/Arena/Core.lean:232-246 unknownConstError` — **the
/// verdict at a constant the environment does not know**: `sorryAx` is a
/// positively detected unsupported feature and DECLINES, every other
/// unresolved name is a malformed stream and REJECTS.  The twin reads the
/// name back for the message; the port drops the interpolation (§3.1), so the
/// readback is gone with it and the comparison is the handle equality
/// DESIGN.md §8.3 licenses.
pub fn unknown_const_error(st: &mut AState, n: &NIdx) -> Result<CheckError, CheckError> {
    match pin_sorry_ax(st) {
        Err(e) => Err(e),
        Ok(sa) => {
            if n.eq2(&sa) {
                Ok(CheckError::NotImplemented(code_points(&M_SORRY)))
            } else {
                Ok(CheckError::Invalid(code_points(&M_UNKNOWN_CONST)))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:70-95 projIndexedStructLike
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::proj_indexed_struct_like_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:279-298 projIndexedStructLike` — **could
/// official's `infer_proj` type `.proj sn i _` at a subject of type `T a⃗`
/// where we store no projection table for `T`?**  Only at a
/// single-constructor inductive `T` named by the node, applied to MORE
/// arguments than its parameters, at a field index below the constructor's
/// field count: an INDEXED structure-like type.  The cited `&&` chain, left
/// to right.
#[allow(clippy::too_many_arguments)]
pub fn proj_indexed_struct_like(
    pers: &PersTier,
    fe: &IFEnv,
    t: &NIdx,
    sn: &NIdx,
    i: u64,
    n_args: u64,
) -> bool {
    if !t.eq2(sn) {
        false
    } else {
        match env::ifenv_find(pers, fe, t) {
            Some(IConstantInfo::IndInfo(_, caps)) => {
                if caps.ctors.len() == 1 && caps.nparams < n_args {
                    match env::ifenv_find(pers, fe, &caps.ctors[0]) {
                        Some(IConstantInfo::CtorInfo(_, _, n_f)) => i < *n_f,
                        _ => false,
                    }
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:97-110 projMissError
/// Lean twin: `proof/ConRon/Arena/Core.lean:300-311 projMissError` — **the verdict at a
/// `.proj sn i _` whose subject type is headed by `T` (applied to `n_args`
/// arguments) with no table entry at field `i`**: an out-of-range index at a
/// table; a positively detected indexed structure-like type DECLINES
/// (`lean4#14977`); everything else is official's reject.  `has_table` is the
/// cited `(findTable? T).isSome`, read by the caller.
pub fn proj_miss_error(
    pers: &PersTier,
    fe: &IFEnv,
    has_table: bool,
    t: &NIdx,
    sn: &NIdx,
    i: u64,
    n_args: u64,
) -> CheckError {
    if has_table {
        CheckError::Invalid(code_points(&M_RANGE))
    } else if proj_indexed_struct_like(pers, fe, t, sn, i, n_args) {
        CheckError::NotImplemented(code_points(&M_INDEXED_PROJ))
    } else {
        CheckError::Invalid(code_points(&M_INVALID_PROJ))
    }
}

// ---------------------------------------------------------------------------
// The bodies' small helpers (`Core.lean:274-412`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:155-166 liftFueled
/// Lean twin: `proof/ConRon/Arena/Core.lean:313-318 liftFueled` — lift a
/// fuel-style partial result; `none` is the level comparison's fuel running
/// out, OUR resource limit, so a DECLINE (con-leche's charter item 9, lane
/// SMALLFIX), never a verdict.  Monomorphic at
/// `Option bool` and with the `what` parameter baked in, because every call
/// site in the twin passes `"level comparison"` —
/// `con_ron_core::kernel::core_k::lift_fueled`'s own two deviations.
pub fn lift_fueled(o: Option<bool>) -> Result<bool, CheckError> {
    match o {
        Some(a) => Ok(a),
        None => fail(CheckError::NotImplemented(code_points(&M_FUEL_LEVEL_CMP))),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:37-45 Expr.ioNeutral
/// Lean twin: `proof/ConRon/Arena/Core.lean:320-329 ioNeutral` — is the
/// spine's head neither a λ nor a `let` (nor a loose bound variable)?  The io
/// grade's claim of such a term is a membership of its io-inferred type
/// (con-leche task #342 L18); `etaCert` asks it of the stuck side.
pub fn io_neutral(pers: &PersTier, st: &AState, e: &EIdx) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => {
            let t: u32 = h.tag();
            Ok(t != ETAG_LAM && t != ETAG_LET_E && t != ETAG_BVAR)
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:48-55 isCtorApp
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::is_ctor_app_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:331-342 isCtorApp` — is the
/// expression headed by a stored constructor?
pub fn is_ctor_app(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => if h.tag() == ETAG_CONST {
            match view_const_name(pers, st, &h) {
                None => fail_dangling_e(),
                Some(c) => match env::ifenv_find(pers, fe, &c) {
                    Some(IConstantInfo::CtorInfo(_, _, _)) => Ok(true),
                    Some(_) => Ok(false),
                    None => Ok(false),
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:57-63 formerResSort
/// Lean twin: `proof/ConRon/Arena/Core.lean:344-353 formerResSort` — **a stored
/// inductive's result sort, read where it is needed**: the sort its stored
/// type ends in, `none` where the type does not end in one.
pub fn former_res_sort(pers: &PersTier, st: &AState, ty: &EIdx) -> Result<Option<LIdx>, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, ty) {
        Err(er) => Err(er),
        Ok(pr) => if pr.tag() == ETAG_SORT {
            match view_sort(pers, st, &pr) {
                None => fail_dangling_e(),
                Some(s) => Ok(Some(s)),
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:65-67 formerDefHeaded
/// Lean twin: `proof/ConRon/Arena/Core.lean:355-360 formerDefHeaded` — a stored former
/// that does not show its telescope.
pub fn former_def_headed(pers: &PersTier, st: &AState, cv: &IConstantVal) -> Result<bool, CheckError> {
    match former_res_sort(pers, st, &cv.ty) {
        Err(er) => Err(er),
        Ok(Some(_)) => Ok(false),
        Ok(None) => Ok(true),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:69-75 formerZ
/// Lean twin: `proof/ConRon/Arena/Core.lean:362-370 formerZ` — **the family's
/// result-sort zero-ness datum**, read off its type (the level read back,
/// deviation 4); where the sort is not read, `ifAllZero []`.
pub fn former_z(pers: &PersTier, st: &mut AState, cvt: &IConstantVal) -> Result<PropWhen, CheckError> {
    match former_res_sort(pers, st, &cvt.ty) {
        Err(er) => Err(er),
        Ok(Some(s)) => match read_level_m(pers, st, &s) {
            Err(er) => Err(er),
            Ok(l) => Ok(level::zeroness_of(&l)),
        },
        Ok(None) => Ok(prop_when::if_all_zero(Vec::new())),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:77-85 formerNeverZero
/// Lean twin: `proof/ConRon/Arena/Core.lean:372-380 formerNeverZero` — is a stored
/// inductive's result sort, at the level instantiation `us`, provably nonzero
/// (official `is_never_zero`)?  The instantiated zero-ness datum is
/// unsatisfiable exactly where the instantiated sort is never zero.
pub fn former_never_zero(
    pers: &PersTier,
    st: &mut AState,
    cvt: &IConstantVal,
    us: &LsIdx,
) -> Result<bool, CheckError> {
    match former_z(pers, st, cvt) {
        Err(er) => Err(er),
        Ok(z) => match read_names_m(pers, st, &cvt.level_params) {
            Err(er) => Err(er),
            Ok(ks) => match read_levels_m(pers, st, us) {
                Err(er) => Err(er),
                Ok(vs) => Ok(prop_when::is_never(&level::subst_pw(&ks, &vs, &z))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:87-94 ctorFamily
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::ctor_family_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:382-395 ctorFamily` — **the family a
/// constructor's type concludes in**: its former and its capabilities, `none`
/// where its type concludes in no stored inductive.  Read out of the
/// environment and copied out, as every reader of a stored record here does.
pub fn ctor_family(
    pers: &PersTier,
    st: &AState,
    fe: &IFEnv,
    cvj: &IConstantVal,
) -> Result<Option<(IConstantVal, IIndCaps)>, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, &cvj.ty) {
        Err(er) => Err(er),
        Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
            Err(er) => Err(er),
            Ok(h) => if h.tag() == ETAG_CONST {
                match view_const_name(pers, st, &h) {
                    None => fail_dangling_e(),
                    Some(t) => match env::ifenv_find(pers, fe, &t) {
                        Some(IConstantInfo::IndInfo(cvt, caps)) => {
                            Ok(Some((env::i_constant_val_dup(cvt), env::i_ind_caps_dup(caps))))
                        }
                        Some(_) => Ok(None),
                        None => Ok(None),
                    },
                }
            } else {
                Ok(None)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:96-115 unfoldDefinition
/// Lean twin: `proof/ConRon/Arena/Core.lean:397-417 unfoldDefinition` — unfold
/// the (application of a) definition at the head, one step.  The stored value
/// is instantiated through `const_val_at`, so a constant unfolded twice at the
/// same levels pays the substitution once.
pub fn unfold_definition(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => if h.tag() == ETAG_CONST {
            match view_const(pers, st, &h) {
                None => fail_dangling_e(),
                Some((n, us)) => match env::ifenv_find(pers, fe, &n) {
                    Some(IConstantInfo::DefnInfo(cv, value, _)) => {
                        let lps: Vec<NIdx> = env::nidx_vec_dup(&cv.level_params);
                        let val: EIdx = value.dup2();
                        match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => {
                                if usl == lps.len() {
                                    match const_val_at(pers, st, &n, &lps, &val, &us) {
                                        Err(er) => Err(er),
                                        Ok(v) => match get_app_args(pers, st, CORE_WALK_FUEL, e) {
                                            Err(er) => Err(er),
                                            Ok(args) => match mk_app_n(pers, st, &v, &args) {
                                                Err(er) => Err(er),
                                                Ok(r) => Ok(Some(r)),
                                            },
                                        },
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        }
                    }
                    Some(_) => Ok(None),
                    None => Ok(None),
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:117-130 unfoldableHead
/// Lean twin: `proof/ConRon/Arena/Core.lean:419-435 unfoldableHead` — may the
/// delta step unfold `e`'s head (the official kernel's `is_delta`)?  The
/// DECISION, taken before the unfolding is materialized.
pub fn unfoldable_head(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => if h.tag() == ETAG_CONST {
            match view_const(pers, st, &h) {
                None => fail_dangling_e(),
                Some((n, us)) => match env::ifenv_find(pers, fe, &n) {
                    Some(IConstantInfo::DefnInfo(cv, _, _)) => {
                        let k = cv.level_params.len();
                        match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => Ok(usl == k),
                        }
                    }
                    Some(_) => Ok(false),
                    None => Ok(false),
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:132-141 headHint
/// Lean twin: `proof/ConRon/Arena/Core.lean:437-448 headHint` — the
/// reducibility hint of the constant at the head of `e`.
pub fn head_hint(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<ReducibilityHint, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => if h.tag() == ETAG_CONST {
            match view_const_name(pers, st, &h) {
                None => fail_dangling_e(),
                Some(n) => match env::ifenv_find(pers, fe, &n) {
                    Some(IConstantInfo::DefnInfo(_, _, hint)) => {
                        Ok(crate::kernel::env::reducibility_hint_dup(hint))
                    }
                    Some(_) => Ok(ReducibilityHint::Opaque),
                    None => Ok(ReducibilityHint::Opaque),
                },
            }
        } else {
            Ok(ReducibilityHint::Opaque)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:143-152 sameConstHeads
/// Lean twin: `proof/ConRon/Arena/Core.lean:450-475 sameConstHeads` — are `a`
/// and `b` applications of the *same* constant (the lazy delta same-head
/// short-circuit)?  Both sides must actually be applications.
pub fn same_const_heads(
    pers: &PersTier,
    st: &mut AState,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if a.tag() == ETAG_APP {
        match view_app(pers, st, a) {
            None => fail_dangling_e(),
            Some((f1, _)) => if b.tag() == ETAG_APP {
                match view_app(pers, st, b) {
                    None => fail_dangling_e(),
                    Some((f2, _)) => match get_app_fn(pers, st, CORE_WALK_FUEL, &f1) {
                        Err(e) => Err(e),
                        Ok(h1) => if h1.tag() == ETAG_CONST {
                            match view_const_name(pers, st, &h1) {
                                None => fail_dangling_e(),
                                Some(n1) => {
                                    match get_app_fn(pers, st, CORE_WALK_FUEL, &f2) {
                                        Err(e) => Err(e),
                                        Ok(h2) => if h2.tag() == ETAG_CONST {
                                            match view_const_name(pers, st, &h2) {
                                                None => fail_dangling_e(),
                                                Some(n2) => Ok(n1.eq2(&n2)),
                                            }
                                        } else {
                                            Ok(false)
                                        },
                                    }
                                },
                            }
                        } else {
                            Ok(false)
                        },
                    },
                }
            } else {
                Ok(false)
            },
        }
    } else {
        Ok(false)
    }
}

// ---------------------------------------------------------------------------
// `Nat` literals (`Core.lean:414-534`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:154-160 natLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:477-488 natLitToConstructor` — the
/// constructor form of a `Nat` literal, one layer.  The cited `match n with |
/// 0 | k + 1` is `nat::is_zero` plus `nat::pred` on the bignum (§3.3), as
/// `con_ron_core::kernel::core_k::nat_lit_to_constructor` spells it.
pub fn nat_lit_to_constructor(
    pers: &PersTier,
    st: &mut AState,
    n: &Nat,
) -> Result<EIdx, CheckError>  {
    if nat::is_zero(n) {
        match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(z) => const_e(pers, st, &z),
        }
    } else {
        match pin_nat_succ(st) {
            Err(e) => Err(e),
            Ok(s) => match const_e(pers, st, &s) {
                Err(e) => Err(e),
                Ok(sc) => {
                    match intern_e_lit(pers, st, expr::literal_nat(nat::pred(n))) {
                        Err(e) => Err(e),
                        Ok(l) => intern_e_app(pers, st, sc, l),
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:162-166 natIndOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:490-496 natIndOk` — the stored
/// `Nat` declaration has the expected shape.
pub fn nat_ind_ok(
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(IConstantInfo::IndInfo(cv, _)) => {
            let lp0 = cv.level_params.len() == 0;
            let ty: EIdx = cv.ty.dup2();
            match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if lp0 {
                        Ok(ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:168-172 natZeroOk
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_zero_ok_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:498-505 natZeroOk` — the stored
/// `Nat.zero` declaration has the expected shape.
pub fn nat_zero_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(IConstantInfo::CtorInfo(cv, _, _)) => {
            let lp0 = cv.level_params.len() == 0;
            let ty: EIdx = cv.ty.dup2();
            match pin_nat(st) {
                Err(e) => Err(e),
                Ok(nt) => match const_e(pers, st, &nt) {
                    Err(e) => Err(e),
                    Ok(nc) => {
                        if lp0 {
                            Ok(ty.eq2(&nc))
                        } else {
                            Ok(false)
                        }
                    }
                },
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:174-182 natSuccOk
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_succ_ok_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:507-519 natSuccOk` — the stored
/// `Nat.succ` declaration has the expected shape.
pub fn nat_succ_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(IConstantInfo::CtorInfo(cv, _, _)) => {
            if cv.level_params.len() != 0 {
                Ok(false)
            } else {
                let ty: EIdx = cv.ty.dup2();
                match pin_nat(st) {
                    Err(e) => Err(e),
                    Ok(nt) => match const_e(pers, st, &nt) {
                        Err(e) => Err(e),
                        Ok(nc) => if ty.tag() == ETAG_FORALL_E {
                            match view_bind(pers, st, &ty) {
                                None => fail_dangling_e(),
                                Some((dom, body)) => {
                                    if dom.eq2(&nc) {
                                        Ok(body.eq2(&nc))
                                    } else {
                                        Ok(false)
                                    }
                                },
                            }
                        } else {
                            Ok(false)
                        },
                    },
                }
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:184-189 natLitSupported
/// con-leche: ConLeche/Kernel/FEnv.lean:195-198 natLitSupportedF
/// Lean twin: `proof/ConRon/Arena/Core.lean:521-531 natLitSupported` — whether
/// the environment supports `Nat` literals.  One twin for con-leche's two
/// spellings (deviation 1).
pub fn nat_lit_supported(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match nat_ind_ok(st, env::ifenv_find(pers, fe, &nt)) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match pin_nat_zero(st) {
                Err(e) => Err(e),
                Ok(nz) => match nat_zero_ok(pers, st, env::ifenv_find(pers, fe, &nz)) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match pin_nat_succ(st) {
                        Err(e) => Err(e),
                        Ok(ns) => nat_succ_ok(pers, st, env::ifenv_find(pers, fe, &ns)),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:191-194 natLitStored
/// con-leche: ConLeche/Kernel/FEnv.lean:200-202 natLitStoredF
/// Lean twin: `proof/ConRon/Arena/Core.lean:533-543 natLitStored` — whether a `Nat`
/// literal's constants are stored (presence only: what they are is the
/// declarations' own check, `lit_shape_ok`).  The conjunction is
/// `constsResolve`'s `.natVal` arm's, so it is that arm's function.  One twin
/// for con-leche's two spellings (deviation 1).
pub fn nat_lit_stored(pers: &PersTier, st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    nat_trio_stored(pers, st, fe)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:196-221 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:545-591 constsResolve` — `(fe.find?
/// n).isSome`, as its own function so the two literal arms below read as the
/// twin's conjunctions do.
pub fn stored(pers: &PersTier, fe: &IFEnv, n: &NIdx) -> bool {
    match env::ifenv_find(pers, fe, n) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:196-221 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:545-591 constsResolve` — the
/// `.lit (.natVal _)` arm's three `find?`s, as its own function
/// (`con_ron_core::kernel::core_k::nat_trio_stored`'s reason: the `String`
/// arm repeats them).
pub fn nat_trio_stored(pers: &PersTier, st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(nz) => match pin_nat_succ(st) {
                Err(e) => Err(e),
                Ok(ns) => Ok(stored(pers, fe, &nt) && stored(pers, fe, &nz) && stored(pers, fe, &ns)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:196-221 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:545-591 constsResolve` — the
/// `.lit (.strVal _)` arm's seven further `find?`s.
pub fn str_support_stored(pers: &PersTier, st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match pin_string(st) {
        Err(e) => Err(e),
        Ok(a1) => match pin_string_of_list(st) {
            Err(e) => Err(e),
            Ok(a2) => match pin_list(st) {
                Err(e) => Err(e),
                Ok(a3) => match pin_list_nil(st) {
                    Err(e) => Err(e),
                    Ok(a4) => match pin_list_cons(st) {
                        Err(e) => Err(e),
                        Ok(a5) => match pin_char(st) {
                            Err(e) => Err(e),
                            Ok(a6) => match pin_char_of_nat(st) {
                                Err(e) => Err(e),
                                Ok(a7) => Ok(stored(pers, fe, &a1)
                                    && stored(pers, fe, &a2)
                                    && stored(pers, fe, &a3)
                                    && stored(pers, fe, &a4)
                                    && stored(pers, fe, &a5)
                                    && stored(pers, fe, &a6)
                                    && stored(pers, fe, &a7)),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:196-221 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:545-591 constsResolve` — do all
/// constants referenced in `e` (including inside `fvar` type annotations)
/// resolve in `fe`?  A full walk over the term, hence fuel; unlike the
/// checker's hot walks it is run once per declaration and carries no memo, as
/// con-leche's does not.
pub fn consts_resolve(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    fuel: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CONSTS_RESOLVE)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(true),
            Ok(ENodeView::Sort(_)) => Ok(true),
            Ok(ENodeView::Lit(Literal::NatVal(_))) => nat_trio_stored(pers, st, fe),
            // **Both halves run**: the twin's `.strVal` arm `pin`s all ten
            // names and *then* takes one conjunction, so short-circuiting the
            // string half would leave seven names uninterned and the store
            // behind the twin's (see the evaluation-order note in DESIGN.md's
            // task #97-P4c section).
            Ok(ENodeView::Lit(Literal::StrVal(_))) => match nat_trio_stored(pers, st, fe) {
                Err(e) => Err(e),
                Ok(nats) => match str_support_stored(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(strs) => Ok(nats && strs),
                },
            },
            Ok(ENodeView::Const(n, _)) => Ok(stored(pers, fe, &n)),
            Ok(ENodeView::FVar(_, ty)) => consts_resolve(pers, st, fe, fuel - 1, &ty),
            Ok(ENodeView::App(f, a)) => match consts_resolve(pers, st, fe, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(true) => consts_resolve(pers, st, fe, fuel - 1, &a),
                Ok(false) => Ok(false),
            },
            Ok(ENodeView::Lam(ty, body)) => match consts_resolve(pers, st, fe, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(true) => consts_resolve(pers, st, fe, fuel - 1, &body),
                Ok(false) => Ok(false),
            },
            Ok(ENodeView::ForallE(ty, body)) => {
                match consts_resolve(pers, st, fe, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(true) => consts_resolve(pers, st, fe, fuel - 1, &body),
                    Ok(false) => Ok(false),
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                match consts_resolve(pers, st, fe, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match consts_resolve(pers, st, fe, fuel - 1, &val) {
                        Err(e) => Err(e),
                        Ok(true) => consts_resolve(pers, st, fe, fuel - 1, &body),
                        Ok(false) => Ok(false),
                    },
                }
            }
            Ok(ENodeView::Proj(s, _, sub)) => {
                if stored(pers, fe, &s) {
                    consts_resolve(pers, st, fe, fuel - 1, &sub)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:223-228 litToCtorIfNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:593-601 litToCtorIfNat` — convert a
/// `Nat`-literal major premise to constructor form, one layer.
pub fn lit_to_ctor_if_nat(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if h.tag() == ETAG_LIT {
        match view_lit(pers, st, h) {
            None => fail_dangling_e(),
            Some(Literal::NatVal(n)) => {
                let m: Nat = nat::clone(&n);
                match nat_lit_stored(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(true) => nat_lit_to_constructor(pers, st, &m),
                    Ok(false) => Ok(h.dup2()),
                }
            }
            Some(_) => Ok(h.dup2()),
        }
    } else {
        Ok(h.dup2())
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:230-235 rawNatLit?
/// Lean twin: `proof/ConRon/Arena/Core.lean:603-613 rawNatLit?` — a `Nat`
/// literal reading of a whnf'd expression (the official kernel's
/// `rawNatLitExt?`).
pub fn raw_nat_lit(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<Option<Nat>, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lit(Literal::NatVal(n))) => Ok(Some(nat::clone(&n))),
        Ok(ENodeView::Const(c, us)) => match empty_levels(st) {
            Err(e) => Err(e),
            Ok(el) => match pin_nat_zero(st) {
                Err(e) => Err(e),
                Ok(nz) => {
                    if c.eq2(&nz) && us.eq2(&el) {
                        Ok(Some(nat::zero()))
                    } else {
                        Ok(None)
                    }
                }
            },
        },
        Ok(_) => Ok(None),
    }
}

// ---------------------------------------------------------------------------
// String literals (`Core.lean:536-723`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:250-261 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:617-629 strLitConsSpine` — the
/// `List.cons` spine of a string literal's constructor form.  con-leche writes
/// `s.toList.foldr (init := nil) fun c e => …`; DESIGN.md §3.4 turns the
/// closure into the twin's explicit recursion over the character list, and the
/// `Vec<u32>` of code points turns that into a cursor recursion.
pub fn str_lit_cons_spine(
    pers: &PersTier,
    st: &mut AState,
    cons: &EIdx,
    of_nat: &EIdx,
    nil_e: &EIdx,
    s: &Vec<u32>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= s.len() {
        Ok(nil_e.dup2())
    } else {
        match str_lit_cons_spine(pers, st, cons, of_nat, nil_e, s, i + 1) {
            Err(e) => Err(e),
            Ok(rest) => {
                let c: u64 = s[i] as u64;
                match intern_e_lit(pers, st, expr::literal_nat(nat::from_u64(c))) {
                    Err(e) => Err(e),
                    Ok(lit) => match intern_e_app(pers, st, of_nat.dup2(), lit) {
                        Err(e) => Err(e),
                        Ok(ch) => match intern_e_app(pers, st, cons.dup2(), ch) {
                            Err(e) => Err(e),
                            Ok(f) => intern_e_app(pers, st, f, rest),
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:250-261 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:631-650 strLitToConstructor` — the
/// tail of the cited `do` block, from `let lcN ← pin listConsName` on.  Split
/// off so that the `let` chain does not nest fifteen `match`es deep; the
/// statements are the twin's, in the twin's order.
pub fn str_lit_to_constructor_rest(
    pers: &PersTier,
    st: &mut AState,
    s: &Vec<u32>,
    zs: &LsIdx,
    ch_c: &EIdx,
    nil_e: &EIdx,
) -> Result<EIdx, CheckError> {
    match pin_list_cons(st) {
        Err(e) => Err(e),
        Ok(lc_n) => match intern_e_const(pers, st, lc_n, zs.dup2()) {
            Err(e) => Err(e),
            Ok(lc) => match intern_e_app(pers, st, lc, ch_c.dup2()) {
                Err(e) => Err(e),
                Ok(cons) => match pin_char_of_nat(st) {
                    Err(e) => Err(e),
                    Ok(co_n) => match const_e(pers, st, &co_n) {
                        Err(e) => Err(e),
                        Ok(of_nat) => {
                            match str_lit_cons_spine(pers, st, &cons, &of_nat, nil_e, s, 0) {
                                Err(e) => Err(e),
                                Ok(spine) => {
                                    match pin_string_of_list(st) {
                                        Err(e) => Err(e),
                                        Ok(sl_n) => match const_e(pers, st, &sl_n) {
                                            Err(e) => Err(e),
                                            Ok(sl) => {
                                                intern_e_app(pers, st, sl, spine)
                                            }
                                        },
                                    }
                                }
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:250-261 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:631-650 strLitToConstructor` — the
/// constructor form of a `String` literal: `String.ofList (List.cons.{0} Char
/// (Char.ofNat (lit c₁)) (… (List.nil.{0} Char)))`.
pub fn str_lit_to_constructor(
    pers: &PersTier,
    st: &mut AState,
    s: &Vec<u32>,
) -> Result<EIdx, CheckError>  {
    match zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => {
            let mut zl: Vec<LIdx> = Vec::new();
            zl.push(z);
            match intern_ls_node(pers, st, zl) {
                Err(e) => Err(e),
                Ok(zs) => match pin_char(st) {
                    Err(e) => Err(e),
                    Ok(ch_n) => match const_e(pers, st, &ch_n) {
                        Err(e) => Err(e),
                        Ok(ch_c) => match pin_list_nil(st) {
                            Err(e) => Err(e),
                            Ok(ln_n) => {
                                match intern_e_const(pers, st, ln_n, zs.dup2()) {
                                    Err(e) => Err(e),
                                    Ok(ln) => {
                                        match intern_e_app(pers, st, ln, ch_c.dup2())
                                        {
                                            Err(e) => Err(e),
                                            Ok(nil_e) => str_lit_to_constructor_rest(
                                                pers,
                                                st, s, &zs, &ch_c, &nil_e,
                                            ),
                                        }
                                    }
                                }
                            }
                        },
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:263-269 stringTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:652-659 stringTyOk` — the stored
/// `String` declaration has the expected shape.
pub fn string_ty_ok(
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:271-277 charTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:661-668 charTyOk` — the stored
/// `Char` declaration has the expected shape.
pub fn char_ty_ok(
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:279-290 listTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:670-687 listTyOk` — the stored
/// `List` declaration has the expected shape `List.{p} : Type p →
/// Type p`.
pub fn list_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            if cv.level_params.len() != 1 {
                Ok(false)
            } else {
                let p: NIdx = cv.level_params[0].dup2();
                match intern_l_node(pers, st, LNodeView::Param(p)) {
                    Err(e) => Err(e),
                    Ok(pl) => match intern_l_node(pers, st, LNodeView::Succ(pl)) {
                        Err(e) => Err(e),
                        Ok(sp) => match intern_e_sort(pers, st, sp) {
                            Err(e) => Err(e),
                            Ok(sort) => if cv.ty.tag() == ETAG_FORALL_E {
                                match view_bind(pers, st, &cv.ty) {
                                    None => fail_dangling_e(),
                                    Some((d, b)) => {
                                        if d.eq2(&sort) {
                                            Ok(b.eq2(&sort))
                                        } else {
                                            Ok(false)
                                        }
                                    },
                                }
                            } else {
                                Ok(false)
                            },
                        },
                    },
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:292-303 listNilTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:689-723 listNilTyOk` — the cited
/// `match ← view cv.type with | .forallE d b _mb => …` tail, split off so that
/// the `let` chain above does not nest six deep.
pub fn list_nil_ty_body(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    sort: &EIdx,
    ps: &LsIdx,
    li: &NIdx,
) -> Result<bool, CheckError> {
    if ty.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, ty) {
            None => fail_dangling_e(),
            Some((d, b)) => {
                if !d.eq2(sort) {
                    Ok(false)
                } else {
                    if b.tag() == ETAG_APP {
                        match view_app(pers, st, &b) {
                            None => fail_dangling_e(),
                            Some((f, a)) => if f.tag() == ETAG_CONST {
                                match view_const(pers, st, &f) {
                                    None => fail_dangling_e(),
                                    Some((l1, us1)) => if a.tag() == ETAG_BVAR {
                                        match view_bvar(pers, st, &a) {
                                            None => fail_dangling_e(),
                                            Some(0) => {
                                                if l1.eq2(li) {
                                                    Ok(us1.eq2(ps))
                                                } else {
                                                    Ok(false)
                                                }
                                            }
                                            Some(_) => Ok(false),
                                        }
                                    } else {
                                        Ok(false)
                                    },
                                }
                            } else {
                                Ok(false)
                            },
                        }
                    } else {
                        Ok(false)
                    }
                }
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:292-303 listNilTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:689-723 listNilTyOk` — the stored
/// `List.nil` declaration has the expected shape.
pub fn list_nil_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            if cv.level_params.len() != 1 {
                Ok(false)
            } else {
                let p: NIdx = cv.level_params[0].dup2();
                match intern_l_node(pers, st, LNodeView::Param(p)) {
                    Err(e) => Err(e),
                    Ok(pl) => match intern_l_node(pers, st, LNodeView::Succ(pl.dup2())) {
                        Err(e) => Err(e),
                        Ok(sp) => match intern_e_sort(pers, st, sp) {
                            Err(e) => Err(e),
                            Ok(sort) => {
                                let mut pv: Vec<LIdx> = Vec::new();
                                pv.push(pl);
                                match intern_ls_node(pers, st, pv) {
                                    Err(e) => Err(e),
                                    Ok(ps) => {
                                        match pin_list(st) {
                                            Err(e) => Err(e),
                                            Ok(li) => list_nil_ty_body(
                                                pers,
                                                st, &cv.ty, &sort, &ps, &li,
                                            ),
                                        }
                                    }
                                }
                            }
                        },
                    },
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:305-321 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:725-761 listConsTyOk` — the three
/// nested ∀ tests, once the comparands are interned.
pub fn list_cons_ty_body(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    sort: &EIdx,
    b0: &EIdx,
    l1: &EIdx,
    b1: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match intern_e_app(pers, st, l1.dup2(), b1.dup2()) {
        Err(e) => Err(e),
        Ok(dom3) => match intern_e_app(pers, st, l1.dup2(), b2.dup2()) {
            Err(e) => Err(e),
            Ok(cod3) => if ty.tag() == ETAG_FORALL_E {
                match view_bind(pers, st, ty) {
                    None => fail_dangling_e(),
                    Some((d1, r1)) => {
                        if !d1.eq2(sort) {
                            Ok(false)
                        } else {
                            if r1.tag() == ETAG_FORALL_E {
                                match view_bind(pers, st, &r1) {
                                    None => fail_dangling_e(),
                                    Some((d2, r2)) => {
                                        if !d2.eq2(b0) {
                                            Ok(false)
                                        } else {
                                            if r2.tag() == ETAG_FORALL_E {
                                                match view_bind(pers, st, &r2) {
                                                    None => fail_dangling_e(),
                                                    Some((d3, c3)) => {
                                                        if d3.eq2(&dom3) {
                                                            Ok(c3.eq2(&cod3))
                                                        } else {
                                                            Ok(false)
                                                        }
                                                    },
                                                }
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                    },
                                }
                            } else {
                                Ok(false)
                            }
                        }
                    },
                }
            } else {
                Ok(false)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:305-321 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:725-761 listConsTyOk` — the cited
/// `[p]` arm: the eight comparands, then the three-deep ∀ match.
pub fn list_cons_ty_at(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    p: &NIdx,
) -> Result<bool, CheckError>  {
    match intern_l_node(pers, st, LNodeView::Param(p.dup2())) {
        Err(e) => Err(e),
        Ok(pl) => match intern_l_node(pers, st, LNodeView::Succ(pl.dup2())) {
            Err(e) => Err(e),
            Ok(sp) => match intern_e_sort(pers, st, sp) {
                Err(e) => Err(e),
                Ok(sort) => {
                    let mut pv: Vec<LIdx> = Vec::new();
                    pv.push(pl);
                    match intern_ls_node(pers, st, pv) {
                        Err(e) => Err(e),
                        Ok(ps) => match pin_list(st) {
                            Err(e) => Err(e),
                            Ok(li) => match intern_e_bvar(pers, st, 0) {
                                Err(e) => Err(e),
                                Ok(b0) => match intern_e_bvar(pers, st, 1) {
                                    Err(e) => Err(e),
                                    Ok(b1) => match intern_e_bvar(pers, st, 2) {
                                        Err(e) => Err(e),
                                        Ok(b2) => {
                                            match intern_e_const(pers, st, li, ps) {
                                                Err(e) => Err(e),
                                                Ok(l1) => list_cons_ty_body(
                                                    pers,
                                                    st, ty, &sort, &b0, &l1, &b1, &b2,
                                                ),
                                            }
                                        }
                                    },
                                },
                            },
                        },
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:305-321 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:725-761 listConsTyOk` — the stored
/// `List.cons` declaration has the expected shape.
pub fn list_cons_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            if cv.level_params.len() != 1 {
                Ok(false)
            } else {
                let p: NIdx = cv.level_params[0].dup2();
                list_cons_ty_at(pers, st, &cv.ty, &p)
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:323-332 charOfNatTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:763-778 charOfNatTyOk` — the stored
/// `Char.ofNat` declaration has the expected shape `Nat → Char`.
pub fn char_of_nat_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            if cv.level_params.len() != 0 {
                Ok(false)
            } else {
                match pin_nat(st) {
                    Err(e) => Err(e),
                    Ok(nt) => match const_e(pers, st, &nt) {
                        Err(e) => Err(e),
                        Ok(nc) => match pin_char(st) {
                            Err(e) => Err(e),
                            Ok(ch) => match const_e(pers, st, &ch) {
                                Err(e) => Err(e),
                                Ok(cc) => if cv.ty.tag() == ETAG_FORALL_E {
                                    match view_bind(pers, st, &cv.ty) {
                                        None => fail_dangling_e(),
                                        Some((d, b)) => {
                                            if d.eq2(&nc) {
                                                Ok(b.eq2(&cc))
                                            } else {
                                                Ok(false)
                                            }
                                        },
                                    }
                                } else {
                                    Ok(false)
                                },
                            },
                        },
                    },
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:334-344 stringOfListTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:780-801 stringOfListTyOk` — the
/// cited `do` block's body, once the level-parameter test has passed.
pub fn string_of_list_ty_body(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
) -> Result<bool, CheckError>  {
    match zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => {
            let mut zv: Vec<LIdx> = Vec::new();
            zv.push(z);
            match intern_ls_node(pers, st, zv) {
                Err(e) => Err(e),
                Ok(zs) => match pin_list(st) {
                    Err(e) => Err(e),
                    Ok(li) => match intern_e_const(pers, st, li, zs) {
                        Err(e) => Err(e),
                        Ok(lc) => match pin_char(st) {
                            Err(e) => Err(e),
                            Ok(ch) => match const_e(pers, st, &ch) {
                                Err(e) => Err(e),
                                Ok(cc) => match intern_e_app(pers, st, lc, cc) {
                                    Err(e) => Err(e),
                                    Ok(dom) => {
                                        match pin_string(st) {
                                            Err(e) => Err(e),
                                            Ok(stn) => match const_e(pers, st, &stn) {
                                                Err(e) => Err(e),
                                                Ok(sc) => if ty.tag() == ETAG_FORALL_E {
                                                    match view_bind(pers, st, ty) {
                                                        None => fail_dangling_e(),
                                                        Some((d, b)) => {
                                                            if d.eq2(&dom) {
                                                                Ok(b.eq2(&sc))
                                                            } else {
                                                                Ok(false)
                                                            }
                                                        },
                                                    }
                                                } else {
                                                    Ok(false)
                                                },
                                            },
                                        }
                                    }
                                },
                            },
                        },
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:334-344 stringOfListTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:780-801 stringOfListTyOk` — the
/// stored `String.ofList` declaration has the expected shape
/// `List.{0} Char → String`.
pub fn string_of_list_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(c);
            if cv.level_params.len() != 0 {
                Ok(false)
            } else {
                string_of_list_ty_body(pers, st, &cv.ty)
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:362-367 strLitStored
/// con-leche: ConLeche/Kernel/FEnv.lean:204-209 strLitStoredF
/// Lean twin: `proof/ConRon/Arena/Core.lean:803-820 strLitStored` — whether a `String`
/// literal's constants are stored: `natLitStored` and the seven
/// string-support names, read by presence only.  One twin for con-leche's two
/// spellings (deviation 1).
pub fn str_lit_stored(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError> {
    match nat_lit_stored(pers, st, fe) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => str_support_stored(pers, st, fe),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:369-385 litShapeOk
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::lit_shape_ok_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:822-839 litShapeOk` — **the shape a
/// declaration at a literal's name must have**, its level parameters and type,
/// checked at the declaration; any other name passes.  A declaration check
/// cannot show a kind, so the three `Nat` names are read at the kinds their
/// guards ask for (an inductive at no capabilities, two constructors).  The
/// cited `if`-chain, each name interned only when the chain reaches it.
pub fn lit_shape_ok(
    pers: &PersTier,
    st: &mut AState,
    c: &IConstantInfo,
) -> Result<bool, CheckError> {
    let n: NIdx = env::i_constant_info_name(c);
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(a0) => if n.eq2(&a0) {
            let ci: IConstantInfo =
                IConstantInfo::IndInfo(env::i_constant_info_to_constant_val(c), env::i_ind_caps_default());
            nat_ind_ok(st, Some(&ci))
        } else {
            match pin_nat_zero(st) {
                Err(e) => Err(e),
                Ok(a1) => if n.eq2(&a1) {
                    let ci: IConstantInfo = IConstantInfo::CtorInfo(env::i_constant_info_to_constant_val(c), 0, 0);
                    nat_zero_ok(pers, st, Some(&ci))
                } else {
                    match pin_nat_succ(st) {
                        Err(e) => Err(e),
                        Ok(a2) => if n.eq2(&a2) {
                            let ci: IConstantInfo =
                                IConstantInfo::CtorInfo(env::i_constant_info_to_constant_val(c), 0, 1);
                            nat_succ_ok(pers, st, Some(&ci))
                        } else {
                            lit_shape_ok_str(pers, st, &n, c)
                        },
                    }
                },
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:369-385 litShapeOk
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::lit_shape_ok_str_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:822-839 litShapeOk` — the chain's
/// `String`, `String.ofList` and `List` rungs, split off so the nesting stays
/// readable.
pub fn lit_shape_ok_str(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    c: &IConstantInfo,
) -> Result<bool, CheckError> {
    match pin_string(st) {
        Err(e) => Err(e),
        Ok(a3) => if n.eq2(&a3) {
            string_ty_ok(st, Some(c))
        } else {
            match pin_string_of_list(st) {
                Err(e) => Err(e),
                Ok(a4) => if n.eq2(&a4) {
                    string_of_list_ty_ok(pers, st, Some(c))
                } else {
                    match pin_list(st) {
                        Err(e) => Err(e),
                        Ok(a5) => if n.eq2(&a5) {
                            list_ty_ok(pers, st, Some(c))
                        } else {
                            lit_shape_ok_rest(pers, st, n, c)
                        },
                    }
                },
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:369-385 litShapeOk
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::lit_shape_ok_rest_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:822-839 litShapeOk` — the chain's last
/// four rungs (`List.nil`, `List.cons`, `Char`, `Char.ofNat`) and its `true`.
pub fn lit_shape_ok_rest(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    c: &IConstantInfo,
) -> Result<bool, CheckError> {
    match pin_list_nil(st) {
        Err(e) => Err(e),
        Ok(a6) => if n.eq2(&a6) {
            list_nil_ty_ok(pers, st, Some(c))
        } else {
            match pin_list_cons(st) {
                Err(e) => Err(e),
                Ok(a7) => if n.eq2(&a7) {
                    list_cons_ty_ok(pers, st, Some(c))
                } else {
                    match pin_char(st) {
                        Err(e) => Err(e),
                        Ok(a8) => if n.eq2(&a8) {
                            char_ty_ok(st, Some(c))
                        } else {
                            match pin_char_of_nat(st) {
                                Err(e) => Err(e),
                                Ok(a9) => if n.eq2(&a9) {
                                    char_of_nat_ty_ok(pers, st, Some(c))
                                } else {
                                    Ok(true)
                                },
                            }
                        },
                    }
                },
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Structural-`Nat` literal acceleration (`Core.lean:726-1172`)
//
// con-leche's certified fast path: an operation participates only when its
// defining recurrence equations hold by definitional equality — checked once,
// at its check, so *presence in the store is the certificate*.  The nineteen
// reserved names are interned here exactly as the literal guards' are; the
// `ConLeche.Name` values are `con_ron_core::kernel::core_k`'s own, so the two
// crates cannot spell a reserved name differently.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:415 natPredName
/// Lean twin: `proof/ConRon/Arena/Core.lean:849-850 natPredName`.
pub fn nat_pred_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_pred(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:416 natAddName
/// Lean twin: `proof/ConRon/Arena/Core.lean:851-852 natAddName`.
pub fn nat_add_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_add(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:417 natSubName
/// Lean twin: `proof/ConRon/Arena/Core.lean:853-854 natSubName`.
pub fn nat_sub_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_sub(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:418 natMulName
/// Lean twin: `proof/ConRon/Arena/Core.lean:855-856 natMulName`.
pub fn nat_mul_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_mul(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:419 natPowName
/// Lean twin: `proof/ConRon/Arena/Core.lean:857-858 natPowName`.
pub fn nat_pow_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_pow(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:420 natBeqName
/// Lean twin: `proof/ConRon/Arena/Core.lean:859-860 natBeqName`.
pub fn nat_beq_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_beq(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:421 natBleName
/// Lean twin: `proof/ConRon/Arena/Core.lean:861-862 natBleName`.
pub fn nat_ble_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_ble(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:422 natDivName
/// Lean twin: `proof/ConRon/Arena/Core.lean:863-864 natDivName`.
pub fn nat_div_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_div(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:423 natModName
/// Lean twin: `proof/ConRon/Arena/Core.lean:865-866 natModName`.
pub fn nat_mod_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_mod(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:424 natGcdName
/// Lean twin: `proof/ConRon/Arena/Core.lean:867-868 natGcdName`.
pub fn nat_gcd_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_gcd(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:425 natLandName
/// Lean twin: `proof/ConRon/Arena/Core.lean:869-870 natLandName`.
pub fn nat_land_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_land(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:426 natLorName
/// Lean twin: `proof/ConRon/Arena/Core.lean:871-872 natLorName`.
pub fn nat_lor_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_lor(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:427 natXorName
/// Lean twin: `proof/ConRon/Arena/Core.lean:873-874 natXorName`.
pub fn nat_xor_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_xor(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:428 natShiftLeftName
/// Lean twin: `proof/ConRon/Arena/Core.lean:875-876 natShiftLeftName`.
pub fn nat_shift_left_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_shift_left(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:429 natShiftRightName
/// Lean twin: `proof/ConRon/Arena/Core.lean:877-878 natShiftRightName`.
pub fn nat_shift_right_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_shift_right(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:430 boolName
/// Lean twin: `proof/ConRon/Arena/Core.lean:879-880 boolName`.
pub fn bool_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:442 boolTrueName
/// Lean twin: `proof/ConRon/Arena/Core.lean:881-882 boolTrueName`.
pub fn bool_true_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool_true(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:443 boolFalseName
/// Lean twin: `proof/ConRon/Arena/Core.lean:883-884 boolFalseName`.
pub fn bool_false_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool_false(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:445-450 Expr.isBoolTrue
/// Lean twin: `proof/ConRon/Arena/Core.lean:888-900 isBoolTrue` — is `e` the
/// constant `Bool.true` (the official kernel's `is_constant(e, Bool.true)`):
/// the name, no universe levels.
pub fn is_bool_true(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<bool, CheckError> {
    if h.tag() == ETAG_CONST {
        match view_const(pers, st, h) {
            None => fail_dangling_e(),
            Some((c, us)) => match empty_levels(st) {
                Err(e) => Err(e),
                Ok(el) => {
                    if !us.eq2(&el) {
                        Ok(false)
                    } else {
                        match bool_true_name(st) {
                            Err(e) => Err(e),
                            Ok(bt) => Ok(c.eq2(&bt)),
                        }
                    }
                }
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:432-434 eagerReduceName
/// Lean twin: `proof/ConRon/Arena/Core.lean:885-886 eagerReduceName`.
pub fn eager_reduce_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_eager_reduce(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:436-441 Expr.isEagerReduce
/// Lean twin: `proof/ConRon/Arena/Core.lean:902-922 isEagerReduce` — is `e` of the
/// form `eagerReduce _ _` (official `is_eager_reduce`): the head constant
/// `eagerReduce`, exactly two arguments, any universe levels.
pub fn is_eager_reduce(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<bool, CheckError> {
    if h.tag() == ETAG_APP {
        match view_app(pers, st, h) {
            None => fail_dangling_e(),
            Some((f, _y)) => if f.tag() == ETAG_APP {
                match view_app(pers, st, &f) {
                    None => fail_dangling_e(),
                    Some((g, _x)) => if g.tag() == ETAG_CONST {
                        match view_const(pers, st, &g) {
                            None => fail_dangling_e(),
                            Some((c, _us)) => match eager_reduce_name(st) {
                                Err(e) => Err(e),
                                Ok(er) => Ok(c.eq2(&er)),
                            },
                        }
                    } else {
                        Ok(false)
                    },
                }
            } else {
                Ok(false)
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: none — the `List NIdx` accumulator Lean's list literal hides
/// Lean twin: `proof/ConRon/Arena/Core.lean:924-930 natOpNames` — push one
/// interned name onto a `Vec`, so the name lists below read as the twin's
/// bracket literals do.
pub fn push_nidx(out: Vec<NIdx>, n: &NIdx) -> Vec<NIdx> {
    let mut out = out;
    out.push(n.dup2());
    out
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:452-460 natOpNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:924-930 natOpNames` — the certified
/// structural-`Nat` operations.
pub fn nat_op_names(st: &mut AState) -> Result<Vec<NIdx>, CheckError> {
    match nat_pred_name(st) {
        Err(e) => Err(e),
        Ok(a) => match nat_add_name(st) {
            Err(e) => Err(e),
            Ok(b) => match nat_sub_name(st) {
                Err(e) => Err(e),
                Ok(c) => match nat_mul_name(st) {
                    Err(e) => Err(e),
                    Ok(d) => match nat_pow_name(st) {
                        Err(e) => Err(e),
                        Ok(f) => match nat_beq_name(st) {
                            Err(e) => Err(e),
                            Ok(g) => match nat_ble_name(st) {
                                Err(e) => Err(e),
                                Ok(h) => {
                                    let out: Vec<NIdx> = Vec::new();
                                    let out = push_nidx(out, &a);
                                    let out = push_nidx(out, &b);
                                    let out = push_nidx(out, &c);
                                    let out = push_nidx(out, &d);
                                    let out = push_nidx(out, &f);
                                    let out = push_nidx(out, &g);
                                    Ok(push_nidx(out, &h))
                                }
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:462-475 natDivModNames
/// con-leche: ConLeche/Kernel/CoreDefs.lean:506-520 reservedRecName
/// Lean twin: `proof/ConRon/Arena/Core.lean:1573-1583 reservedRecBool` — the last three
/// disjuncts: `n == boolName || n == boolTrueName || n == boolFalseName`.
pub fn reserved_rec_bool(st: &AState, n: &NIdx) -> Result<bool, CheckError> {
    match pin_bool(st) {
        Err(e) => Err(e),
        Ok(b) => {
            if n.eq2(&b) {
                Ok(true)
            } else {
                match pin_bool_true(st) {
                    Err(e) => Err(e),
                    Ok(t) => {
                        if n.eq2(&t) {
                            Ok(true)
                        } else {
                            match pin_bool_false(st) {
                                Err(e) => Err(e),
                                Ok(f) => Ok(n.eq2(&f)),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:630-640 natOpWfNames
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_div_mod_names_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:932-938 natDivModNames`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1211-1217 natOpWfNames`
/// The WF-recursive operations with a *pinned-declaration* certified fast
/// path.  The twin spells the same eight names twice, under two names, exactly
/// as con-leche does; one function serves both and carries both citations.
pub fn nat_div_mod_names(st: &mut AState) -> Result<Vec<NIdx>, CheckError> {
    match nat_div_name(st) {
        Err(e) => Err(e),
        Ok(a) => match nat_mod_name(st) {
            Err(e) => Err(e),
            Ok(b) => match nat_gcd_name(st) {
                Err(e) => Err(e),
                Ok(c) => match nat_land_name(st) {
                    Err(e) => Err(e),
                    Ok(d) => match nat_lor_name(st) {
                        Err(e) => Err(e),
                        Ok(f) => match nat_xor_name(st) {
                            Err(e) => Err(e),
                            Ok(g) => match nat_shift_left_name(st) {
                                Err(e) => Err(e),
                                Ok(h) => match nat_shift_right_name(st) {
                                    Err(e) => Err(e),
                                    Ok(i) => {
                                        let out: Vec<NIdx> = Vec::new();
                                        let out = push_nidx(out, &a);
                                        let out = push_nidx(out, &b);
                                        let out = push_nidx(out, &c);
                                        let out = push_nidx(out, &d);
                                        let out = push_nidx(out, &f);
                                        let out = push_nidx(out, &g);
                                        let out = push_nidx(out, &h);
                                        Ok(push_nidx(out, &i))
                                    }
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:477-481 natOpName
/// Lean twin: `proof/ConRon/Arena/Core.lean:940-947 natOpName` — **the certified
/// operations' names**: the fast path fires on them by name, so only a
/// definition may take one (`checkConstantVal`, `reservedRecName`).
pub fn nat_op_name(st: &mut AState, n: &NIdx) -> Result<bool, CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ops) => if env::nidx_vec_contains(&ops, n) {
            Ok(true)
        } else {
            match nat_div_mod_names(st) {
                Err(e) => Err(e),
                Ok(dms) => Ok(env::nidx_vec_contains(&dms, n)),
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:499-504 litGuardNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:1555-1571 litGuardNames` — the ten names the
/// two literal guards look up: the `Nat` guard's three and the `String`
/// guard's seven, off the pin table (every one is pinned).
pub fn lit_guard_names(st: &AState) -> Result<Vec<NIdx>, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(a) => match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(b) => match pin_nat_succ(st) {
                Err(e) => Err(e),
                Ok(c) => match pin_string(st) {
                    Err(e) => Err(e),
                    Ok(d) => match pin_string_of_list(st) {
                        Err(e) => Err(e),
                        Ok(f) => match pin_list(st) {
                            Err(e) => Err(e),
                            Ok(g) => match pin_list_nil(st) {
                                Err(e) => Err(e),
                                Ok(h) => match pin_list_cons(st) {
                                    Err(e) => Err(e),
                                    Ok(i) => match pin_char(st) {
                                        Err(e) => Err(e),
                                        Ok(j) => match pin_char_of_nat(st) {
                                            Err(e) => Err(e),
                                            Ok(k) => {
                                                let out: Vec<NIdx> = Vec::new();
                                                let out = push_nidx(out, &a);
                                                let out = push_nidx(out, &b);
                                                let out = push_nidx(out, &c);
                                                let out = push_nidx(out, &d);
                                                let out = push_nidx(out, &f);
                                                let out = push_nidx(out, &g);
                                                let out = push_nidx(out, &h);
                                                let out = push_nidx(out, &i);
                                                let out = push_nidx(out, &j);
                                                Ok(push_nidx(out, &k))
                                            }
                                        },
                                    },
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:506-520 reservedRecName
/// Lean twin: `proof/ConRon/Arena/Core.lean:1585-1600 reservedRecName` — **a name no
/// block RECURSOR may take**: one a literal guard looks up, one of the
/// certified `Nat` operations, or `Bool` and its two constructors, whose stored
/// entries the certified operations' guards read.  The basis names are
/// `basisNamesOk`'s (a pinned block's own recursor carries one).  The cited
/// `||` chain, each list read off the pin table (handle equality).
pub fn reserved_rec_name(st: &mut AState, n: &NIdx) -> Result<bool, CheckError> {
    match lit_guard_names(st) {
        Err(e) => Err(e),
        Ok(ls) => {
            if env::nidx_vec_contains(&ls, n) {
                Ok(true)
            } else {
                match nat_op_names(st) {
                    Err(e) => Err(e),
                    Ok(os) => {
                        if env::nidx_vec_contains(&os, n) {
                            Ok(true)
                        } else {
                            match nat_div_mod_names(st) {
                                Err(e) => Err(e),
                                Ok(ds) => {
                                    if env::nidx_vec_contains(&ds, n) {
                                        Ok(true)
                                    } else {
                                        reserved_rec_bool(st, n)
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:630-640 natOpWfNames
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_op_wf_names_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1211-1217 natOpWfNames` — the
/// pin-certified WF-recursive `Nat` operations, as a *safety net*.  The twin's
/// list is `natDivModNames`' element for element.
pub fn nat_op_wf_names(st: &mut AState) -> Result<Vec<NIdx>, CheckError> {
    nat_div_mod_names(st)
}

/// con-leche: none — the fifteen reserved `Nat`-operation handles, interned once
/// Lean twin: `proof/ConRon/Arena/Core.lean:949-972 natOpDeps` — the twin
/// opens `natOpDeps`, `natOpResult` and `natBinOpName` with the same fifteen
/// `let`s; the port interns them once into a record so the three functions
/// read as the twin's `if` chains do and the pin cost is paid once per call
/// rather than three times.
pub struct NatOpPins {
    pub pr: NIdx,
    pub ad: NIdx,
    pub su: NIdx,
    pub mu: NIdx,
    pub po: NIdx,
    pub be: NIdx,
    pub bl: NIdx,
    pub di: NIdx,
    pub mo: NIdx,
    pub gc: NIdx,
    pub la: NIdx,
    pub lo: NIdx,
    pub xo: NIdx,
    pub sl: NIdx,
    pub sr: NIdx,
}

/// con-leche: none — the fifteen reserved `Nat`-operation handles, interned once
/// Lean twin: `proof/ConRon/Arena/Core.lean:949-972 natOpDeps` — the `let`
/// prefix, once.
pub fn nat_op_pins(st: &mut AState) -> Result<NatOpPins, CheckError> {
    match nat_pred_name(st) {
        Err(e) => Err(e),
        Ok(pr) => match nat_add_name(st) {
            Err(e) => Err(e),
            Ok(ad) => match nat_sub_name(st) {
                Err(e) => Err(e),
                Ok(su) => match nat_mul_name(st) {
                    Err(e) => Err(e),
                    Ok(mu) => match nat_pow_name(st) {
                        Err(e) => Err(e),
                        Ok(po) => match nat_beq_name(st) {
                            Err(e) => Err(e),
                            Ok(be) => match nat_ble_name(st) {
                                Err(e) => Err(e),
                                Ok(bl) => nat_op_pins_rest(st, pr, ad, su, mu, po, be, bl),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: none — the fifteen reserved `Nat`-operation handles, interned once
/// Lean twin: `proof/ConRon/Arena/Core.lean:949-972 natOpDeps` — the last eight
/// of the `let` prefix.
pub fn nat_op_pins_rest(
    st: &mut AState,
    pr: NIdx,
    ad: NIdx,
    su: NIdx,
    mu: NIdx,
    po: NIdx,
    be: NIdx,
    bl: NIdx,
) -> Result<NatOpPins, CheckError> {
    match nat_div_name(st) {
        Err(e) => Err(e),
        Ok(di) => match nat_mod_name(st) {
            Err(e) => Err(e),
            Ok(mo) => match nat_gcd_name(st) {
                Err(e) => Err(e),
                Ok(gc) => match nat_land_name(st) {
                    Err(e) => Err(e),
                    Ok(la) => match nat_lor_name(st) {
                        Err(e) => Err(e),
                        Ok(lo) => match nat_xor_name(st) {
                            Err(e) => Err(e),
                            Ok(xo) => match nat_shift_left_name(st) {
                                Err(e) => Err(e),
                                Ok(sl) => match nat_shift_right_name(st) {
                                    Err(e) => Err(e),
                                    Ok(sr) => Ok(NatOpPins {
                                        pr,
                                        ad,
                                        su,
                                        mu,
                                        po,
                                        be,
                                        bl,
                                        di,
                                        mo,
                                        gc,
                                        la,
                                        lo,
                                        xo,
                                        sl,
                                        sr,
                                    }),
                                },
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:522-545 natOpDeps
/// Lean twin: `proof/ConRon/Arena/Core.lean:949-972 natOpDeps` — the operations
/// (transitively) involved in `c`'s recurrences.  The cited `if … else if …`
/// chain, arm for arm; the empty tail is `[]`.
pub fn nat_op_deps(st: &mut AState, c: &NIdx) -> Result<Vec<NIdx>, CheckError> {
    match nat_op_pins(st) {
        Err(e) => Err(e),
        Ok(p) => {
            let out: Vec<NIdx> = Vec::new();
            if c.eq2(&p.pr) {
                Ok(push_nidx(out, &p.pr))
            } else if c.eq2(&p.ad) {
                Ok(push_nidx(out, &p.ad))
            } else if c.eq2(&p.su) {
                let out = push_nidx(out, &p.pr);
                Ok(push_nidx(out, &p.su))
            } else if c.eq2(&p.mu) {
                let out = push_nidx(out, &p.ad);
                Ok(push_nidx(out, &p.mu))
            } else if c.eq2(&p.po) {
                let out = push_nidx(out, &p.ad);
                let out = push_nidx(out, &p.mu);
                Ok(push_nidx(out, &p.po))
            } else if c.eq2(&p.be) {
                Ok(push_nidx(out, &p.be))
            } else if c.eq2(&p.bl) {
                Ok(push_nidx(out, &p.bl))
            } else if c.eq2(&p.di) {
                let out = push_nidx(out, &p.pr);
                let out = push_nidx(out, &p.su);
                let out = push_nidx(out, &p.bl);
                Ok(push_nidx(out, &p.di))
            } else if c.eq2(&p.mo) {
                let out = push_nidx(out, &p.pr);
                let out = push_nidx(out, &p.su);
                let out = push_nidx(out, &p.bl);
                Ok(push_nidx(out, &p.mo))
            } else if c.eq2(&p.gc) {
                let out = push_nidx(out, &p.bl);
                let out = push_nidx(out, &p.mo);
                Ok(push_nidx(out, &p.gc))
            } else if c.eq2(&p.la) {
                let out = push_nidx(out, &p.ad);
                let out = push_nidx(out, &p.mu);
                let out = push_nidx(out, &p.bl);
                let out = push_nidx(out, &p.di);
                let out = push_nidx(out, &p.mo);
                Ok(push_nidx(out, &p.la))
            } else if c.eq2(&p.lo) {
                let out = push_nidx(out, &p.ad);
                let out = push_nidx(out, &p.su);
                let out = push_nidx(out, &p.mu);
                let out = push_nidx(out, &p.bl);
                let out = push_nidx(out, &p.di);
                let out = push_nidx(out, &p.mo);
                Ok(push_nidx(out, &p.lo))
            } else if c.eq2(&p.xo) {
                let out = push_nidx(out, &p.ad);
                let out = push_nidx(out, &p.mu);
                let out = push_nidx(out, &p.bl);
                let out = push_nidx(out, &p.di);
                let out = push_nidx(out, &p.mo);
                Ok(push_nidx(out, &p.xo))
            } else if c.eq2(&p.sl) {
                let out = push_nidx(out, &p.su);
                let out = push_nidx(out, &p.mu);
                let out = push_nidx(out, &p.bl);
                Ok(push_nidx(out, &p.sl))
            } else if c.eq2(&p.sr) {
                let out = push_nidx(out, &p.su);
                let out = push_nidx(out, &p.bl);
                let out = push_nidx(out, &p.di);
                Ok(push_nidx(out, &p.sr))
            } else {
                Ok(out)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:974-979 natAp1` — `ap1 n a`, one of
/// the equation builder's three local lambdas.  DESIGN.md §3.4 forbids the
/// closure, so each is a named function.
pub fn nat_ap1(pers: &PersTier, st: &mut AState, n: &NIdx, a: &EIdx) -> Result<EIdx, CheckError> {
    match const_e(pers, st, n) {
        Err(e) => Err(e),
        Ok(f) => intern_e_app(pers, st, f, a.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:981-984 natAp2` — `ap2 n a b`.
pub fn nat_ap2(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match nat_ap1(pers, st, n, a) {
        Err(e) => Err(e),
        Ok(f) => intern_e_app(pers, st, f, b.dup2()),
    }
}

/// con-leche: none — the `List (Expr × Expr)` accumulator Lean's list literal hides
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — push one
/// equation onto the result `Vec`.
pub fn push_eq(out: Vec<(EIdx, EIdx)>, l: &EIdx, r: &EIdx) -> Vec<(EIdx, EIdx)> {
    let mut out = out;
    out.push((l.dup2(), r.dup2()));
    out
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the
/// comparands the cited `let` block opens with: the two free variables, `0`,
/// the two successors and the two `Bool` constructors.
pub struct NatEqCtx {
    pub x: EIdx,
    pub y: EIdx,
    pub z: EIdx,
    pub s_n: NIdx,
    pub sx: EIdx,
    pub sy: EIdx,
    pub b_t: EIdx,
    pub b_f: EIdx,
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the `let`
/// prefix, as its own function.
pub fn nat_eq_ctx(pers: &PersTier, st: &mut AState, d: u64) -> Result<NatEqCtx, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(n_n) => match const_e(pers, st, &n_n) {
            Err(e) => Err(e),
            Ok(nat_ty) => match intern_e_fvar(pers, st, d, nat_ty.dup2()) {
                Err(e) => Err(e),
                Ok(x) => match intern_e_fvar(pers, st, d + 1, nat_ty) {
                    Err(e) => Err(e),
                    Ok(y) => match pin_nat_zero(st) {
                        Err(e) => Err(e),
                        Ok(z_n) => match const_e(pers, st, &z_n) {
                            Err(e) => Err(e),
                            Ok(z) => match pin_nat_succ(st) {
                                Err(e) => Err(e),
                                Ok(s_n) => nat_eq_ctx_rest(pers, st, x, y, z, s_n),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the last
/// four `let`s of the prefix.
pub fn nat_eq_ctx_rest(
    pers: &PersTier,
    st: &mut AState,
    x: EIdx,
    y: EIdx,
    z: EIdx,
    s_n: NIdx,
) -> Result<NatEqCtx, CheckError> {
    match nat_ap1(pers, st, &s_n, &x) {
        Err(e) => Err(e),
        Ok(sx) => match nat_ap1(pers, st, &s_n, &y) {
            Err(e) => Err(e),
            Ok(sy) => match bool_true_name(st) {
                Err(e) => Err(e),
                Ok(bt_n) => match const_e(pers, st, &bt_n) {
                    Err(e) => Err(e),
                    Ok(b_t) => match bool_false_name(st) {
                        Err(e) => Err(e),
                        Ok(bf_n) => match const_e(pers, st, &bf_n) {
                            Err(e) => Err(e),
                            Ok(b_f) => Ok(NatEqCtx {
                                x,
                                y,
                                z,
                                s_n,
                                sx,
                                sy,
                                b_t,
                                b_f,
                            }),
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the
/// defining recurrence equations of a structural-`Nat` operation, over
/// constructor forms with free variables `d`, `d + 1` (binder-free, so the
/// equation sides carry no annotations).  Run by the install, never by
/// reduction.
pub fn nat_op_equations(
    pers: &PersTier,
    st: &mut AState,
    d: u64,
    c: &NIdx,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    match nat_eq_ctx(pers, st, d) {
        Err(e) => Err(e),
        Ok(cx) => match nat_op_pins(st) {
            Err(e) => Err(e),
            Ok(p) => nat_op_equations_at(pers, st, &cx, &p, c),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the cited
/// seven-way `if` chain, once the comparands are interned.
pub fn nat_op_equations_at(
    pers: &PersTier,
    st: &mut AState,
    cx: &NatEqCtx,
    p: &NatOpPins,
    c: &NIdx,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    let out: Vec<(EIdx, EIdx)> = Vec::new();
    if c.eq2(&p.pr) {
        match nat_ap1(pers, st, c, &cx.z) {
            Err(e) => Err(e),
            Ok(l1) => match nat_ap1(pers, st, c, &cx.sx) {
                Err(e) => Err(e),
                Ok(l2) => {
                    let out = push_eq(out, &l1, &cx.z);
                    Ok(push_eq(out, &l2, &cx.x))
                }
            },
        }
    } else if c.eq2(&p.ad) {
        match nat_ap2(pers, st, c, &cx.x, &cx.z) {
            Err(e) => Err(e),
            Ok(l1) => match nat_ap2(pers, st, c, &cx.x, &cx.sy) {
                Err(e) => Err(e),
                Ok(l2) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap1(pers, st, &cx.s_n, &inner) {
                        Err(e) => Err(e),
                        Ok(r2) => {
                            let out = push_eq(out, &l1, &cx.x);
                            Ok(push_eq(out, &l2, &r2))
                        }
                    },
                },
            },
        }
    } else if c.eq2(&p.su) {
        match nat_ap2(pers, st, c, &cx.x, &cx.z) {
            Err(e) => Err(e),
            Ok(l1) => match nat_ap2(pers, st, c, &cx.x, &cx.sy) {
                Err(e) => Err(e),
                Ok(l2) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap1(pers, st, &p.pr, &inner) {
                        Err(e) => Err(e),
                        Ok(r2) => {
                            let out = push_eq(out, &l1, &cx.x);
                            Ok(push_eq(out, &l2, &r2))
                        }
                    },
                },
            },
        }
    } else if c.eq2(&p.mu) {
        match nat_ap2(pers, st, c, &cx.x, &cx.z) {
            Err(e) => Err(e),
            Ok(l1) => match nat_ap2(pers, st, c, &cx.x, &cx.sy) {
                Err(e) => Err(e),
                Ok(l2) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap2(pers, st, &p.ad, &inner, &cx.x) {
                        Err(e) => Err(e),
                        Ok(r2) => {
                            let out = push_eq(out, &l1, &cx.z);
                            Ok(push_eq(out, &l2, &r2))
                        }
                    },
                },
            },
        }
    } else if c.eq2(&p.po) {
        nat_op_equations_pow(pers, st, cx, p, c, out)
    } else if c.eq2(&p.be) {
        nat_op_equations_beq(pers, st, cx, c, out)
    } else if c.eq2(&p.bl) {
        nat_op_equations_ble(pers, st, cx, c, out)
    } else {
        Ok(out)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the `pow`
/// arm, whose first right-hand side is `Nat.succ Nat.zero`.
pub fn nat_op_equations_pow(
    pers: &PersTier,
    st: &mut AState,
    cx: &NatEqCtx,
    p: &NatOpPins,
    c: &NIdx,
    out: Vec<(EIdx, EIdx)>,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    match nat_ap2(pers, st, c, &cx.x, &cx.z) {
        Err(e) => Err(e),
        Ok(l1) => match nat_ap1(pers, st, &cx.s_n, &cx.z) {
            Err(e) => Err(e),
            Ok(sz) => match nat_ap2(pers, st, c, &cx.x, &cx.sy) {
                Err(e) => Err(e),
                Ok(l2) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                    Err(e) => Err(e),
                    Ok(inner) => match nat_ap2(pers, st, &p.mu, &inner, &cx.x) {
                        Err(e) => Err(e),
                        Ok(r2) => {
                            let out = push_eq(out, &l1, &sz);
                            Ok(push_eq(out, &l2, &r2))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the `beq`
/// arm's four equations.
pub fn nat_op_equations_beq(
    pers: &PersTier,
    st: &mut AState,
    cx: &NatEqCtx,
    c: &NIdx,
    out: Vec<(EIdx, EIdx)>,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    match nat_ap2(pers, st, c, &cx.z, &cx.z) {
        Err(e) => Err(e),
        Ok(l1) => match nat_ap2(pers, st, c, &cx.z, &cx.sy) {
            Err(e) => Err(e),
            Ok(l2) => match nat_ap2(pers, st, c, &cx.sx, &cx.z) {
                Err(e) => Err(e),
                Ok(l3) => match nat_ap2(pers, st, c, &cx.sx, &cx.sy) {
                    Err(e) => Err(e),
                    Ok(l4) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                        Err(e) => Err(e),
                        Ok(r4) => {
                            let out = push_eq(out, &l1, &cx.b_t);
                            let out = push_eq(out, &l2, &cx.b_f);
                            let out = push_eq(out, &l3, &cx.b_f);
                            Ok(push_eq(out, &l4, &r4))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:547-576 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:986-1049 natOpEquations` — the `ble`
/// arm's three equations.
pub fn nat_op_equations_ble(
    pers: &PersTier,
    st: &mut AState,
    cx: &NatEqCtx,
    c: &NIdx,
    out: Vec<(EIdx, EIdx)>,
) -> Result<Vec<(EIdx, EIdx)>, CheckError> {
    match nat_ap2(pers, st, c, &cx.z, &cx.y) {
        Err(e) => Err(e),
        Ok(l1) => match nat_ap2(pers, st, c, &cx.sx, &cx.z) {
            Err(e) => Err(e),
            Ok(l2) => match nat_ap2(pers, st, c, &cx.sx, &cx.sy) {
                Err(e) => Err(e),
                Ok(l3) => match nat_ap2(pers, st, c, &cx.x, &cx.y) {
                    Err(e) => Err(e),
                    Ok(r3) => {
                        let out = push_eq(out, &l1, &cx.b_t);
                        let out = push_eq(out, &l2, &cx.b_f);
                        Ok(push_eq(out, &l3, &r3))
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:578-603 natOpResult
/// con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_op_result_refines, then delete this line
/// con-leche: ConLeche/Cached/StateC.lean:254-263 natResultRefused
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_op_result_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:403-457 reduceNatI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_op_result_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1114-1160 natOpResult` — the reduct of
/// op `c` on literal arguments (`pred` ignores the second slot).  `ron::Nat` is
/// con-leche's `Nat` here, and a literal is a `Literal` value in a `lit` node.
/// The computation is the cited one at any size; the run's maximum `Nat` size
/// (con-leche's cached `reduceNatI`) refuses `pow` and `shiftLeft` before
/// computing (`pow_guard`, `shift_left_guard`: the cited `natOpRefusal`) and an
/// `add`, `sub` or `mul` result after it (`lit_nat_sized`: `natResultRefused`).
/// Each refusal throws, so it sits in the arm that computes: where con-leche
/// tests the operation's name a second time and reads the result back, the
/// port is already in the arm and holds the number.
pub fn nat_op_result(
    pers: &PersTier,
    st: &mut AState,
    c: &NIdx,
    a: &Nat,
    b: &Nat,
) -> Result<Option<EIdx>, CheckError> {
    match nat_op_pins(st) {
        Err(e) => Err(e),
        Ok(p) => {
            if c.eq2(&p.pr) {
                lit_nat(pers, st, nat::pred(a))
            } else if c.eq2(&p.ad) {
                lit_nat_sized(pers, st, nat::add(a, b))
            } else if c.eq2(&p.su) {
                lit_nat_sized(pers, st, nat::sub(a, b))
            } else if c.eq2(&p.mu) {
                lit_nat_sized(pers, st, nat::mul(a, b))
            } else if c.eq2(&p.po) {
                match pow_guard(st, a, b) {
                    Err(e) => Err(e),
                    Ok(()) => lit_nat(pers, st, nat::pow_nat(a, b)),
                }
            } else if c.eq2(&p.di) {
                lit_nat(pers, st, nat::div(a, b))
            } else if c.eq2(&p.mo) {
                lit_nat(pers, st, nat::modulo(a, b))
            } else if c.eq2(&p.gc) {
                lit_nat(pers, st, nat::gcd(a, b))
            } else if c.eq2(&p.la) {
                lit_nat(pers, st, nat::land(a, b))
            } else if c.eq2(&p.lo) {
                lit_nat(pers, st, nat::lor(a, b))
            } else if c.eq2(&p.xo) {
                lit_nat(pers, st, nat::xor(a, b))
            } else if c.eq2(&p.sl) {
                match shift_left_guard(st, a, b) {
                    Err(e) => Err(e),
                    Ok(()) => lit_nat(pers, st, nat::shift_left_nat(a, b)),
                }
            } else if c.eq2(&p.sr) {
                lit_nat(pers, st, nat::shift_right_nat(a, b))
            } else if c.eq2(&p.be) {
                bool_const(pers, st, nat::beq(a, b))
            } else if c.eq2(&p.bl) {
                bool_const(pers, st, nat::ble(a, b))
            } else {
                Ok(None)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:254-263 natResultRefused
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::lit_nat_sized_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:403-457 reduceNatI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::lit_nat_sized_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1063-1073 litNatSized` — a computed
/// numeral, refused above the run's maximum `Nat` size (the cited
/// `natNumeralTooBig`), otherwise interned like `lit_nat`.
pub fn lit_nat_sized(pers: &PersTier, st: &mut AState, n: Nat) -> Result<Option<EIdx>, CheckError> {
    if nat_size_refused(st, &n) {
        fail(CheckError::Invalid(code_points(&M_NAT_NUMERAL_TOO_BIG)))
    } else {
        lit_nat(pers, st, n)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:156-159 natSizeBytes
/// con-leche: ConLeche/Cached/StateC.lean:326-330 maxNatSizeM
/// Lean twin: `proof/ConRon/Arena/Core.lean:1056-1061 natSizeRefused` — whether the
/// numeral `n` is above the run's maximum `Nat` size,
/// `natSizeBytes n > maxNatSize`.
pub fn nat_size_refused(st: &AState, n: &Nat) -> bool {
    nat::size_bytes_gt(n, max_nat_size(st))
}

/// con-leche: ConLeche/Cached/StateC.lean:161-163 natCountMax
/// con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::pow_guard_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1084-1094 powGuard` — the cited `Nat.pow`
/// clause: an exponent above `natCountMax` is refused whatever the base, and
/// `a > 1`, `b ≠ 0`, `natSizeBytes a > maxNatSize / b` (`pow_refused`) is.
pub fn pow_guard(st: &AState, a: &Nat, b: &Nat) -> Result<(), CheckError> {
    if nat::blt(&nat::from_u64(4294967295), b) {
        fail(CheckError::Invalid(code_points(&M_NAT_POW_COUNT)))
    } else if pow_refused(st, a, b) {
        fail(CheckError::Invalid(code_points(&M_NAT_POW_TOO_BIG)))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::pow_refused_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1075-1082 powRefused` — `a ^ b` has at most
/// `natSizeBytes a * b` bytes, and a base `≤ 1` gives `0` or `1`.
pub fn pow_refused(st: &AState, a: &Nat, b: &Nat) -> bool {
    if nat::ble(a, &nat::one()) {
        false
    } else if nat::is_zero(b) {
        false
    } else {
        nat::size_bytes_gt(a, &nat::div(max_nat_size(st), b))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::shift_left_guard_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1102-1112 shiftLeftGuard` — the cited
/// `Nat.shiftLeft` clause: `0 <<< b = 0` computes; otherwise an amount above
/// `natCountMax` is refused, and so is a result of about
/// `natSizeBytes a + b / 8` bytes above the maximum (`shift_left_refused`).
pub fn shift_left_guard(st: &AState, a: &Nat, b: &Nat) -> Result<(), CheckError> {
    if nat::is_zero(a) {
        Ok(())
    } else if nat::blt(&nat::from_u64(4294967295), b) {
        fail(CheckError::Invalid(code_points(&M_NAT_SHIFT_COUNT)))
    } else if shift_left_refused(st, a, b) {
        fail(CheckError::Invalid(code_points(&M_NAT_NUMERAL_TOO_BIG)))
    } else {
        Ok(())
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:234-252 natOpRefusal
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::shift_left_refused_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1096-1100 shiftLeftRefused` —
/// `natSizeBytes a + b / 8 + 1 > maxNatSize`.
pub fn shift_left_refused(st: &AState, a: &Nat, b: &Nat) -> bool {
    let s = nat::add(&nat::add(&nat::size_bytes(a), &nat::shift_right(b, 3)), &nat::one());
    nat::blt(max_nat_size(st), &s)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:578-603 natOpResult
/// Lean twin: `proof/ConRon/Arena/Core.lean:1114-1160 natOpResult` — `internE (.lit
/// (.natVal …))` wrapped in `some`, which every arithmetic arm above ends in.
pub fn lit_nat(pers: &PersTier, st: &mut AState, n: Nat) -> Result<Option<EIdx>, CheckError> {
    match intern_e_lit(pers, st, expr::literal_nat(n)) {
        Err(e) => Err(e),
        Ok(x) => Ok(Some(x)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:578-603 natOpResult
/// Lean twin: `proof/ConRon/Arena/Core.lean:1114-1160 natOpResult` — the two
/// comparison arms' `Bool` constructor, interned.
pub fn bool_const(pers: &PersTier, st: &mut AState, b: bool) -> Result<Option<EIdx>, CheckError> {
    let r = if b {
        bool_true_name(st)
    } else {
        bool_false_name(st)
    };
    match r {
        Err(e) => Err(e),
        Ok(n) => match const_e(pers, st, &n) {
            Err(e) => Err(e),
            Ok(x) => Ok(Some(x)),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:1162-1171 natOpDepsStored` —
/// con-leche writes `(natOpDeps c).all (fun n => …)`; DESIGN.md §3.4's rule for
/// a `List` walk is a named helper, and the `Vec` turns the twin's cons
/// recursion into a cursor.
pub fn nat_op_deps_stored(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(true)
    } else {
        match env::ifenv_find(pers, fe, &ns[i]) {
            Some(IConstantInfo::DefnInfo(cv, _, _)) => {
                if cv.level_params.len() == 0 {
                    nat_op_deps_stored(pers, st, fe, ns, i + 1)
                } else {
                    Ok(false)
                }
            }
            Some(_) => Ok(false),
            None => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:1185-1209 natOpGuard` — the two
/// `Bool` constructors stored level-free at the type `Bool` itself, the
/// guard's tail.  (Task #119, con-leche task #342: was
/// `bool_ctors_lp_empty`, which checked the level parameters only.)
pub fn bool_ctors_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match bool_true_name(st) {
        Err(e) => Err(e),
        Ok(bt) => match bool_ctor_ok(pers, st, fe, &bt) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match bool_false_name(st) {
                Err(e) => Err(e),
                Ok(bf) => bool_ctor_ok(pers, st, fe, &bf),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:1173-1183 boolCtorOk` — `match
/// fe.find? n with | some ci => ci.levelParams.isEmpty && ci.type == .const
/// boolName [] | none => false`, at one name.  (Task #119: was `lp_empty`.)
pub fn bool_ctor_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError>  {
    match env::ifenv_find(pers, fe, n) {
        Some(ci) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(ci);
            if cv.level_params.len() == 0 {
                match bool_name(st) {
                    Err(e) => Err(e),
                    Ok(bn) => match const_e(pers, st, &bn) {
                        Err(e) => Err(e),
                        Ok(b) => Ok(cv.ty.eq2(&b)),
                    },
                }
            } else {
                Ok(false)
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:605-626 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:211-226 natOpGuardF
/// Lean twin: `proof/ConRon/Arena/Core.lean:1185-1209 natOpGuard` —
/// stored-constant guards for op `c`: the `Nat` basis, every dependency stored
/// as a definition, and (for the `Bool`-valued ops and the `ble`-guarded
/// `div`/`mod`) the `Bool` constructors stored, level-free, at the type `Bool`
/// itself (`bool_ctor_ok`).
pub fn nat_op_guard(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError>  {
    match nat_lit_supported(pers, st, fe) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match nat_op_deps(st, c) {
            Err(e) => Err(e),
            Ok(deps) => match nat_op_deps_stored(pers, st, fe, &deps, 0) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => match nat_beq_name(st) {
                    Err(e) => Err(e),
                    Ok(be) => match nat_ble_name(st) {
                        Err(e) => Err(e),
                        Ok(bl) => match nat_div_mod_names(st) {
                            Err(e) => Err(e),
                            Ok(dm) => {
                                if c.eq2(&be) || c.eq2(&bl) || env::nidx_vec_contains(&dm, c)
                                {
                                    bool_ctors_ok(pers, st, fe)
                                } else {
                                    Ok(true)
                                }
                            }
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:628-634 Expr.substConst0
/// Lean twin: `proof/ConRon/Arena/Core.lean:1219-1233 substConst0` — substitute
/// the level-monomorphic constant `n` by `r` through an application spine (the
/// equation sides are binder-free, so only `app` recurses).
pub fn subst_const0(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    fuel: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_SUBST_CONST0)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(c, us)) => match empty_levels(st) {
                Err(e) => Err(e),
                Ok(el) => {
                    if c.eq2(n) && us.eq2(&el) {
                        Ok(r.dup2())
                    } else {
                        Ok(h.dup2())
                    }
                }
            },
            Ok(ENodeView::App(f, a)) => match subst_const0(pers, st, n, r, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(f2) => match subst_const0(pers, st, n, r, fuel - 1, &a) {
                    Err(e) => Err(e),
                    Ok(a2) => intern_e_app(pers, st, f2, a2),
                },
            },
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:636-652 Expr.substConstAll
/// Lean twin: `proof/ConRon/Arena/Core.lean:1235-1265 substConstAll` —
/// substitute the level-monomorphic constant `n` by the *closed* term `r`
/// everywhere, including under binders.  `fvar` annotations are not entered.
pub fn subst_const_all(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    r: &EIdx,
    fuel: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_SUBST_CONST_ALL)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(c, us)) => match empty_levels(st) {
                Err(e) => Err(e),
                Ok(el) => {
                    if c.eq2(n) && us.eq2(&el) {
                        Ok(r.dup2())
                    } else {
                        Ok(h.dup2())
                    }
                }
            },
            Ok(ENodeView::App(f, a)) => match subst_const_all(pers, st, n, r, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(f2) => match subst_const_all(pers, st, n, r, fuel - 1, &a) {
                    Err(e) => Err(e),
                    Ok(a2) => intern_e_app(pers, st, f2, a2),
                },
            },
            Ok(ENodeView::Lam(ty, b)) => match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                    Err(e) => Err(e),
                    Ok(b2) => intern_e_lam(pers, st, t2, b2),
                },
            },
            Ok(ENodeView::ForallE(ty, b)) => {
                match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(b2) => intern_e_forall_e(pers, st, t2, b2),
                    },
                }
            }
            Ok(ENodeView::LetE(ty, v, b)) => match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &v) {
                    Err(e) => Err(e),
                    Ok(v2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(b2) => intern_e_let_e(pers, st, t2, v2, b2),
                    },
                },
            },
            Ok(ENodeView::Proj(s, i, e2)) => match subst_const_all(pers, st, n, r, fuel - 1, &e2) {
                Err(er) => Err(er),
                Ok(x) => intern_e_proj(pers, st, s, i, x),
            },
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:654-664 natOpCod
/// Lean twin: `proof/ConRon/Arena/Core.lean:1267-1286 natOpCod` — the pinned
/// codomain of a structural-`Nat` operation: `Bool` for the comparisons, `Nat`
/// otherwise.
pub fn nat_op_cod(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match nat_beq_name(st) {
        Err(er) => Err(er),
        Ok(be) => match nat_ble_name(st) {
            Err(er) => Err(er),
            Ok(bl) => {
                if c.eq2(&be) || c.eq2(&bl) {
                    match bool_name(st) {
                        Err(er) => Err(er),
                        Ok(bn) => match const_e(pers, st, &bn) {
                            Err(er) => Err(er),
                            Ok(bc) => {
                                if !e.eq2(&bc) {
                                    Ok(false)
                                } else {
                                    bool_ty_ok(pers, st, fe, &bn)
                                }
                            }
                        },
                    }
                } else {
                    match pin_nat(st) {
                        Err(er) => Err(er),
                        Ok(nn) => match const_e(pers, st, &nn) {
                            Err(er) => Err(er),
                            Ok(nc) => Ok(e.eq2(&nc)),
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:654-664 natOpCod
/// Lean twin: `proof/ConRon/Arena/Core.lean:1267-1286 natOpCod` — the stored
/// `Bool` declaration at no level parameters and type `Sort 1`.
pub fn bool_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    bn: &NIdx,
) -> Result<bool, CheckError>  {
    match env::ifenv_find(pers, fe, bn) {
        Some(ci) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(ci);
            match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:666-681 natOpTyPinned
/// Lean twin: `proof/ConRon/Arena/Core.lean:1288-1314 natOpTyPinned` — the
/// pinned type of a certified `Nat` operation: `Nat → Nat` for the unary
/// `pred`, `Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat → Bool`
/// for the comparisons.
pub fn nat_op_ty_pinned(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ty: &EIdx,
) -> Result<bool, CheckError> {
    match pin_nat(st) {
        Err(er) => Err(er),
        Ok(nn) => match const_e(pers, st, &nn) {
            Err(er) => Err(er),
            Ok(nc) => match nat_pred_name(st) {
                Err(er) => Err(er),
                Ok(pr) => {
                    if c.eq2(&pr) {
                        if ty.tag() == ETAG_FORALL_E {
                            match view_bind(pers, st, ty) {
                                None => fail_dangling_e(),
                                Some((dom, body)) => {
                                    if dom.eq2(&nc) {
                                        nat_op_cod(pers, st, fe, c, &body)
                                    } else {
                                        Ok(false)
                                    }
                                },
                            }
                        } else {
                            Ok(false)
                        }
                    } else {
                        if ty.tag() == ETAG_FORALL_E {
                            match view_bind(pers, st, ty) {
                                None => fail_dangling_e(),
                                Some((dom, rest)) => if rest.tag() == ETAG_FORALL_E {
                                    match view_bind(pers, st, &rest) {
                                        None => fail_dangling_e(),
                                        Some((dom2, body)) => {
                                            if dom.eq2(&nc) && dom2.eq2(&nc) {
                                                nat_op_cod(pers, st, fe, c, &body)
                                            } else {
                                                Ok(false)
                                            }
                                        },
                                    }
                                } else {
                                    Ok(false)
                                },
                            }
                        } else {
                            Ok(false)
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:683-689 natOpStoredOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:1316-1322 natOpStoredOk` — op `n`
/// is stored as a level-monomorphic definition with the pinned type.
pub fn nat_op_stored_ok(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError> {
    match env::ifenv_find(pers, fe, n) {
        Some(IConstantInfo::DefnInfo(cv, _, _)) => {
            if cv.level_params.len() == 0 {
                let ty: EIdx = cv.ty.dup2();
                nat_op_ty_pinned(pers, st, fe, n, &ty)
            } else {
                Ok(false)
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::nat_bin_op_name_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1324-1336 natBinOpName` — the binary
/// literal acceleration's name test.  con-leche writes a fourteen-way
/// disjunction inline; over handles the comparands have to be interned first,
/// so the chain is its own function and the caller reads one `bool`.
pub fn nat_bin_op_name(st: &mut AState, c: &NIdx) -> Result<bool, CheckError> {
    match nat_op_pins(st) {
        Err(e) => Err(e),
        Ok(p) => Ok(c.eq2(&p.ad)
            || c.eq2(&p.su)
            || c.eq2(&p.mu)
            || c.eq2(&p.po)
            || c.eq2(&p.be)
            || c.eq2(&p.bl)
            || c.eq2(&p.di)
            || c.eq2(&p.mo)
            || c.eq2(&p.gc)
            || c.eq2(&p.la)
            || c.eq2(&p.lo)
            || c.eq2(&p.xo)
            || c.eq2(&p.sl)
            || c.eq2(&p.sr)),
    }
}

// ---------------------------------------------------------------------------
// `Vec` helpers for the `List` operations the twin gets for free
//
// `expr_ops` already has `take_eidx`, `cons_eidx` and `eidx_copy_upto`; the
// four below are the rest of what `Core.lean`'s spine arithmetic uses, and
// each is `con_ron_core::kernel::core_k`'s same function over handles.
// ---------------------------------------------------------------------------

/// con-leche: none — `List.drop` on a `Vec`; Lean's list tail is shared
/// Lean twin: `proof/ConRon/Arena/Core.lean:1461-1471 iotaIndexOk` — `args.drop k`,
/// as a fresh `Vec` of handle words.
pub fn drop_eidx(xs: &Vec<EIdx>, k: usize) -> Vec<EIdx> {
    drop_eidx_from(xs, k, Vec::new())
}

/// con-leche: none — `List.drop` on a `Vec`; Lean's list tail is shared
/// Lean twin: `proof/ConRon/Arena/Core.lean:1461-1471 iotaIndexOk` — the cursor
/// recursion behind `drop_eidx`.
pub fn drop_eidx_from(xs: &Vec<EIdx>, k: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if k >= xs.len() {
        out
    } else {
        let mut out = out;
        out.push(xs[k].dup2());
        drop_eidx_from(xs, k + 1, out)
    }
}

/// con-leche: none — `List.drop` on a `Vec` at a `u64` count, without a `usize` cast
/// `xs.drop n` where the count is a machine word of the checker's own
/// arithmetic: task #61's `kernel::core_k::drop_exprs_n` over handles (task
/// #97-P5-Usize).  `drop_eidx_n(xs, n)` is a *truncating* cast under
/// Aeneas, so on a 32-bit target a count past `u32::MAX` would keep entries
/// the twin's `List.drop` drops.  The count is consumed by the recursion
/// instead: `i` walks the `Vec` and `n` counts down.
/// Lean twin: `proof/ConRon/Arena/Core.lean:1461-1471 iotaIndexOk` — `args.drop k`.
pub fn drop_eidx_n(xs: &Vec<EIdx>, n: u64) -> Vec<EIdx> {
    drop_eidx_n_from(xs, n, 0)
}

/// con-leche: none — `List.drop` on a `Vec` at a `u64` count
/// The index recursion behind `drop_eidx_n`: it walks the prefix without
/// copying and hands the rest to `drop_eidx_from`.
/// Lean twin: `proof/ConRon/Arena/Core.lean:1461-1471 iotaIndexOk` — the
/// cursor recursion behind `drop_eidx_n`.
pub fn drop_eidx_n_from(xs: &Vec<EIdx>, n: u64, i: usize) -> Vec<EIdx> {
    if n == 0 {
        drop_eidx_from(xs, i, Vec::new())
    } else if i >= xs.len() {
        Vec::new()
    } else {
        drop_eidx_n_from(xs, n - 1, i + 1)
    }
}

/// con-leche: none — `List.append` on a `Vec`; Lean's `++` shares the tail
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — `xs ++
/// ys`, consuming `xs` and copying `ys`' spine.
pub fn append_eidx(xs: Vec<EIdx>, ys: &Vec<EIdx>) -> Vec<EIdx> {
    append_eidx_from(xs, ys, 0)
}

/// con-leche: none — `List.append` on a `Vec`; Lean's `++` shares the tail
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// cursor recursion behind `append_eidx`.
pub fn append_eidx_from(xs: Vec<EIdx>, ys: &Vec<EIdx>, i: usize) -> Vec<EIdx> {
    if i >= ys.len() {
        xs
    } else {
        let mut xs = xs;
        xs.push(ys[i].dup2());
        append_eidx_from(xs, ys, i + 1)
    }
}

/// con-leche: none — `xs ++ [y] ++ [z]` on a `Vec`, sized once
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// two-element case of `snoc_eidx_of` (task #97-P6-13); nested `snoc_eidx`
/// was three allocations.
pub fn snoc2_eidx_of(xs: &Vec<EIdx>, y: &EIdx, z: &EIdx) -> Vec<EIdx> {
    let out: Vec<EIdx> = Vec::with_capacity(xs.len() + 2);
    let mut out = crate::arena::expr_ops::eidx_copy_upto(xs, xs.len(), 0, out);
    out.push(y.dup2());
    out.push(z.dup2());
    out
}

/// con-leche: none — `xs ++ ys` on a `Vec`, at a borrowed `xs`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// same `++` sized once (task #97-P6-13); see `snoc_eidx_of`.
pub fn append_eidx_of(xs: &Vec<EIdx>, ys: &Vec<EIdx>) -> Vec<EIdx> {
    let out: Vec<EIdx> = Vec::with_capacity(xs.len() + ys.len());
    let out2 = crate::arena::expr_ops::eidx_copy_upto(xs, xs.len(), 0, out);
    append_eidx_from(out2, ys, 0)
}

/// con-leche: none — `List.reverse` on a `Vec`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3555-3581 defeqSpine` — `aa.reverse`: pushes
/// `xs[i-1], …, xs[0]` onto `out` (`rec_check::nfs_reverse`'s pattern).
pub fn eidx_rev(xs: &Vec<EIdx>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i == 0 {
        out
    } else if i > xs.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(xs[i - 1].dup2());
        eidx_rev(xs, i - 1, o)
    }
}

/// con-leche: none — `List.getD` on a `Vec`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — `args.getD i b0`,
/// the out-of-range guard the cited `.bvar 0` default stands for.
pub fn get_d_eidx(xs: &Vec<EIdx>, i: u64, dflt: &EIdx) -> EIdx {
    if i < xs.len() as u64 {
        xs[i as usize].dup2()
    } else {
        dflt.dup2()
    }
}

// ---------------------------------------------------------------------------
// `reduceNat` (`Core.lean:1122-1172`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::reduce_nat_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1338-1390 reduceNat` — literal
/// acceleration (the official kernel's `reduceNat`, run in the `whnf` loop
/// *before* delta-unfolding).  The divergence audit's D15 is preserved: the
/// FIRST argument is head-normalised and, unless it is a literal, the step
/// fails WITHOUT touching the second.
pub fn reduce_nat(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if e.tag() == ETAG_APP {
        match view_app(pers, st, e) {
            None => fail_dangling_e(),
            Some((f, b)) => match view(pers, st, &f) {
                Err(er) => Err(er),
                Ok(ENodeView::Const(c, us)) => {
                    reduce_nat_succ(pers, st, mode, eager, lane, fuel, fe, depth, &c, &us, &b)
                }
                Ok(ENodeView::App(g, a)) => if g.tag() == ETAG_CONST {
                    match view_const(pers, st, &g) {
                        None => fail_dangling_e(),
                        Some((c, us)) => {
                            reduce_nat_bin(pers, st, mode, eager, lane, fuel, fe, depth, &c, &us, &a, &b)
                        },
                    }
                } else {
                    Ok(None)
                },
                Ok(_) => Ok(None),
            },
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::reduce_nat_succ_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1338-1390 reduceNat` — the cited
/// `.app (.const c []) a` arm: `Nat.succ` at a literal argument.
pub fn reduce_nat_succ(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    c: &NIdx,
    us: &LsIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match empty_levels(st) {
        Err(er) => Err(er),
        Ok(el) => {
            if !us.eq2(&el) {
                Ok(None)
            } else {
                match pin_nat_succ(st) {
                    Err(er) => Err(er),
                    // **Both conjuncts are evaluated**, because Lean's `do`
                    // lifts `(← natLitStored fe)` out of the condition
                    // `c == ns && …` to a `let` before the `if`.
                    // `natLitStored` interns its names, so running it only when
                    // `c == ns` would leave the store a node behind the twin's.
                    Ok(ns) => match nat_lit_stored(pers, st, fe) {
                        Err(er) => Err(er),
                        Ok(nls) => {
                            if c.eq2(&ns) && nls {
                                match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, b) {
                                    Err(er) => Err(er),
                                    Ok(w) => match raw_nat_lit(pers, st, &w) {
                                        Err(er) => Err(er),
                                        Ok(Some(n)) => {
                                            lit_nat_sized(pers, st, nat::add(&n, &nat::one()))
                                        }
                                        Ok(None) => Ok(None),
                                    },
                                }
                            } else {
                                Ok(None)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::reduce_nat_bin_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1338-1390 reduceNat` — the cited
/// `.app (.app (.const c []) a) b` arm: a certified binary operation at two
/// literal arguments, or the WF-recursive safety net's decline.
pub fn reduce_nat_bin(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    c: &NIdx,
    us: &LsIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match empty_levels(st) {
        Err(er) => Err(er),
        Ok(el) => {
            if !us.eq2(&el) {
                Ok(None)
            } else {
                match nat_bin_op_name(st, c) {
                    Err(er) => Err(er),
                    Ok(bin) => {
                        if bin {
                            match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, a) {
                                Err(er) => Err(er),
                                Ok(wa) => match raw_nat_lit(pers, st, &wa) {
                                    Err(er) => Err(er),
                                    Ok(None) => Ok(None),
                                    Ok(Some(n1)) => {
                                        match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, b)
                                        {
                                            Err(er) => Err(er),
                                            Ok(wb) => match raw_nat_lit(pers, st, &wb) {
                                                Err(er) => Err(er),
                                                Ok(None) => Ok(None),
                                                Ok(Some(n2)) => {
                                                    nat_op_result(pers, st, c, &n1, &n2)
                                                }
                                            },
                                        }
                                    }
                                },
                            }
                        } else {
                            reduce_nat_wf(pers, st, mode, eager, lane, fuel, fe, depth, c, a, b)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:168-209 reduceNat
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::reduce_nat_wf_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1338-1390 reduceNat` — the
/// WF-recursive safety net: a pinned `div`/`mod`/… at two literals is a
/// positively detected unsupported feature, not a reduction.
pub fn reduce_nat_wf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    c: &NIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match nat_op_wf_names(st) {
        Err(er) => Err(er),
        Ok(wf) => {
            if env::nidx_vec_contains(&wf, c) {
                match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, a) {
                    Err(er) => Err(er),
                    Ok(wa) => match raw_nat_lit(pers, st, &wa) {
                        Err(er) => Err(er),
                        Ok(None) => Ok(None),
                        Ok(Some(_)) => {
                            match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, b) {
                                Err(er) => Err(er),
                                Ok(wb) => match raw_nat_lit(pers, st, &wb) {
                                    Err(er) => Err(er),
                                    Ok(None) => Ok(None),
                                    Ok(Some(_)) => fail(CheckError::NotImplemented(
                                        code_points(&M_NATIVE_NAT),
                                    )),
                                },
                            }
                        }
                    },
                }
            } else {
                Ok(None)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The certification helpers (`Core.lean:1175-1581`)
//
// con-leche's `Core.lean`:865-1310.  Every one of these recurses structurally
// on a LIST (an argument spine, a slot index list), so none of them takes
// fuel; what they call into the store does.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:212-227 iotaCertsFull
/// con-leche: ConLeche/Cached/CoreC.lean:485-489 iotaCertsFullI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_certs_full_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1432-1437 iotaCertsFull` — **the
/// full-grade telescope certificate** (ι's case 3): every argument is inferred
/// at the FULL grade and its type compared with its (instantiated) domain; no
/// slot is skipped.  The cached tier's bulk form at the empty accumulator.
/// (Task #119: was `iotaCerts`, with the ι-slot licence and the io grade.)
pub fn iota_certs_full(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    let acc: Vec<EIdx> = Vec::new();
    iota_certs_full_aux(pers, st, mode, eager, lane, fuel, fe, depth, h, acc, args, i)
}

/// con-leche: ConLeche/Cached/CoreC.lean:459-483 iotaCertsFullIAux
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_certs_full_aux_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1398-1430 iotaCertsFullAux` — the
/// cached tier's bulk form of `iotaCertsFull`.
///
/// **The batched instantiation lever** (task #97-P6-9): peel the RAW telescope
/// while the certified arguments accumulate, and substitute only each
/// binder's DOMAIN instead of copying the whole residual telescope per
/// argument.  `acc` is the list `instantiate_list` takes at cursor 0, built in
/// PUSH order on an OWNED vector (task #97-P6-15).  A raw `bvar` body
/// substitutes the accumulator and re-enters at the same argument, exactly as
/// the cited function does; every other non-`forallE` view is `false`.
pub fn iota_certs_full_aux(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
    acc: Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= args.len() {
        Ok(true)
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, body)) => {
                let arg: EIdx = args[i].dup2();
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, &acc, 0) {
                    Err(e) => Err(e),
                    Ok(ty2) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, &arg) {
                        Err(e) => Err(e),
                        Ok(ta) => match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &ta, &ty2) {
                            Err(e) => Err(e),
                            Ok(false) => Ok(false),
                            Ok(true) => {
                                let mut acc2: Vec<EIdx> = acc;
                                acc2.push(arg);
                                iota_certs_full_aux(
                                    pers, st, mode, eager, lane, fuel, fe, depth, &body, acc2, args,
                                    i + 1,
                                )
                            }
                        },
                    },
                }
            }
            Ok(ENodeView::BVar(_)) => {
                if acc.len() == 0 {
                    Ok(false)
                } else {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, h, &acc, 0) {
                        Err(e) => Err(e),
                        Ok(ty2) => {
                            let acc2: Vec<EIdx> = Vec::new();
                            iota_certs_full_aux(
                                pers, st, mode, eager, lane, fuel, fe, depth, &ty2, acc2, args, i,
                            )
                        }
                    }
                }
            }
            Ok(_) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:691-696 piResidual
/// Lean twin: `proof/ConRon/Arena/Core.lean:1439-1450 piResidual` — peel a
/// ∀-telescope along an argument list.
pub fn pi_residual(
    pers: &PersTier,
    st: &mut AState,
    e: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(e.dup2()))
    } else {
        if e.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, e) {
                None => fail_dangling_e(),
                Some((_, b)) => {
                    let a: EIdx = args[i].dup2();
                    match instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &a, 0) {
                        Err(er) => Err(er),
                        Ok(b2) => pi_residual(pers, st, &b2, args, i + 1),
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:229-238 defEqList
/// con-leche: ConLeche/Cached/CoreC.lean:491-500 defEqListI
/// Lean twin: `proof/ConRon/Arena/Core.lean:1452-1459 defEqList` — pairwise
/// definitional equality of two spines.  The twin's `| _, _ => false`
/// catch-all is the length test.
pub fn def_eq_list(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    xs: &Vec<EIdx>,
    ys: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= xs.len() {
        if i >= ys.len() {
            Ok(true)
        } else {
            Ok(false)
        }
    } else if i >= ys.len() {
        Ok(false)
    } else {
        let a: EIdx = xs[i].dup2();
        let b: EIdx = ys[i].dup2();
        match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &a, &b) {
            Err(e) => Err(e),
            Ok(true) => def_eq_list(pers, st, mode, eager, lane, fuel, fe, depth, xs, ys, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:240-254 iotaIndexOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:1461-1471 iotaIndexOk` — the
/// canonical-index comparison of a firing ι redex.
pub fn iota_index_ok(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    ty_ctor: &EIdx,
    margs: &Vec<EIdx>,
    idx: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if m_i == r_p {
        Ok(true)
    } else {
        match pi_residual(pers, st, ty_ctor, margs, 0) {
            Err(e) => Err(e),
            Ok(Some(residual)) => match get_app_args(pers, st, CORE_WALK_FUEL, &residual) {
                Err(e) => Err(e),
                Ok(args) => {
                    let rest: Vec<EIdx> = drop_eidx_n(&args, cn_p);
                    def_eq_list(pers, st, mode, eager, lane, fuel, fe, depth, &rest, idx, 0)
                }
            },
            Ok(None) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:256-278 proofIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1473-1498 proofIrrel` — proof
/// irrelevance certification: both sides' types' *sorts* are `Prop`.
/// con-leche's task #172 B4: every inference here is at the io grade.  The
/// unit-type branch went with the pinned `PUnit` (con-leche's lane PUNIT).
/// `fe` stays a parameter although con-leche's lost its `env`: the arena's
/// knot reads the environment it is handed.
pub fn proof_irrel(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(ta) => prop_sorts_zero(pers, st, mode, eager, lane, fuel, fe, depth, &ta, b),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:256-278 proofIrrel
/// con-leche: ConLeche/Kernel/Core.lean:280-322 propIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1473-1498 proofIrrel`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1500-1531 propIrrel`
/// The `Prop` branch both certifications end in: the *sort* of the type of `a`
/// and the sort of the type of `b` are both `Prop`.  `proofIrrel` reaches it
/// with `ta` already inferred, `propIrrel` with `ta` inferred after its two
/// fast arms have declined, so the twin writes the same eleven lines twice and
/// the port writes them once.
pub fn prop_sorts_zero(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ta: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, ta) {
        Err(e) => Err(e),
        Ok(tta) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tta) {
            Err(e) => Err(e),
            Ok(wa) => if wa.tag() == ETAG_SORT {
                match view_sort(pers, st, &wa) {
                    None => fail_dangling_e(),
                    Some(u_t) => match zero_level(st) {
                        Err(e) => Err(e),
                        Ok(z) => match lvl_eq(pers, st, &u_t, &z) {
                            Err(e) => Err(e),
                            Ok(o) => match lift_fueled(o) {
                                Err(e) => Err(e),
                                Ok(ok_a) => {
                                    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, b) {
                                        Err(e) => Err(e),
                                        Ok(tb) => prop_sorts_zero_right(
                                            pers,
                                            st, mode, eager, lane, fuel, fe, depth, ok_a, &tb,
                                        ),
                                    }
                                }
                            },
                        },
                    },
                }
            } else {
                Ok(false)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:256-278 proofIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1473-1498 proofIrrel` — the right
/// side of `prop_sorts_zero`.
pub fn prop_sorts_zero_right(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ok_a: bool,
    tb: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, tb) {
        Err(e) => Err(e),
        Ok(ttb) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &ttb) {
            Err(e) => Err(e),
            Ok(wb) => if wb.tag() == ETAG_SORT {
                match view_sort(pers, st, &wb) {
                    None => fail_dangling_e(),
                    Some(v_t) => match zero_level(st) {
                        Err(e) => Err(e),
                        Ok(z) => match lvl_eq(pers, st, &v_t, &z) {
                            Err(e) => Err(e),
                            Ok(o) => match lift_fueled(o) {
                                Err(e) => Err(e),
                                Ok(ok_b) => Ok(ok_a && ok_b),
                            },
                        },
                    },
                }
            } else {
                Ok(false)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:280-322 propIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1500-1531 propIrrel` — **the
/// hoisted proof-irrelevance test** (con-leche's task #168, Option U): the
/// `Prop` branch of `proofIrrel` alone, with the head-symbol readers deciding
/// both fast arms before any inference.
pub fn prop_irrel(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    // **Both `notProofFast` calls run**, and so do both `isProofFast` calls:
    // Lean's `do` lifts every `(← …)` out of `if (← f a) || (← f b) then`, and
    // the readers touch the state (a stored constant's `toConstantVal` may
    // intern), so short-circuiting either pair would leave the store behind the
    // twin's.
    match not_proof_fast(pers, st, fe, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(na) => match not_proof_fast(pers, st, fe, CORE_WALK_FUEL, b) {
            Err(e) => Err(e),
            Ok(nb) => {
                if na || nb {
                    Ok(false)
                } else {
                    match is_proof_fast(pers, st, fe, CORE_WALK_FUEL, a) {
                        Err(e) => Err(e),
                        Ok(pa) => match is_proof_fast(pers, st, fe, CORE_WALK_FUEL, b) {
                            Err(e) => Err(e),
                            Ok(pb) => {
                                if pa && pb {
                                    Ok(true)
                                } else {
                                    match knot_infer_io(
                                        pers,
                                        st, mode, eager, lane, fuel, fe, depth, a,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(ta) => prop_sorts_zero(
                                            pers,
                                            st, mode, eager, lane, fuel, fe, depth, &ta, b,
                                        ),
                                    }
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: none — `List NIdx` equality; Lean's `deriving DecidableEq` on the level-parameter list
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — a
/// level-parameter list comparison (`structEtaCertWith`'s `cvc.levelParams =
/// cvT.levelParams`, `recRuleEtaOf`'s), over the `Vec` the port stores it in.
pub fn nidx_vec_beq(a: &Vec<NIdx>, b: &Vec<NIdx>) -> bool {
    if a.len() == b.len() {
        nidx_vec_beq_from(a, b, 0)
    } else {
        false
    }
}

/// con-leche: none — `List NIdx` equality; Lean's `deriving DecidableEq` on the level-parameter list
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// cursor recursion behind `nidx_vec_beq`.
pub fn nidx_vec_beq_from(a: &Vec<NIdx>, b: &Vec<NIdx>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i].eq2(&b[i]) {
        nidx_vec_beq_from(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:698-702 etaProjs
/// con-leche: ConLeche/Cached/CoreC.lean:94-101 projNodesI
/// Lean twin: `proof/ConRon/Arena/Core.lean:1533-1540 projNodesGo` — the
/// `.proj T j b` spine, as a counted recursion over `List.range nF`.
pub fn proj_nodes_go(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    b: &EIdx,
    n: u64,
    j: u64,
) -> Result<Vec<EIdx>, CheckError> {
    if n == 0 {
        Ok(Vec::new())
    } else {
        match intern_e_proj(pers, st, t.dup2(), j, b.dup2()) {
            Err(e) => Err(e),
            Ok(p) => match proj_nodes_go(pers, st, t, b, n - 1, j + 1) {
                Err(e) => Err(e),
                Ok(rest) => Ok(cons_eidx(&p, &rest)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:698-702 etaProjs
/// Lean twin: `proof/ConRon/Arena/Core.lean:1542-1547 etaProjs` — the
/// fabricated projections of a structure-eta spine: the `.proj T j b` nodes
/// (one per field of the family's projection table: the node is what the
/// table types and reduces).
pub fn eta_projs(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    b: &EIdx,
    n_f: u64,
) -> Result<Vec<EIdx>, CheckError> {
    proj_nodes_go(pers, st, t, b, n_f, 0)
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:95-102 reservedBasisNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:1549-1553 reservedBasisNames` — the
/// names reserved for the pinned basis blocks, interned.  `contains` is then
/// handle equality, as everywhere else in this module.  The nineteen
/// `ConLeche.Name` values are `con_ron_core::kernel::basis_names`' own list, in
/// the cited order.
///
/// **Task #97-P6-4a: read off `arena::pins`, not interned.**  Every caller is
/// on a per-declaration path (`check_constant_val_guards` is one of them), and
/// building the nineteen `Name` values alone was 1.1 % of `Init`'s cycles
/// before the interning walk that followed it.  The handles are the same
/// handles: `intern_reserved_pins` interned this very list at startup.  The
/// twin's `reservedBasisNamesFrom` cursor goes with it — that walk now runs
/// once, at the driver, as `arena::intern::intern_name_list`, which is the
/// same recursion.
pub fn reserved_basis_names(st: &AState) -> Result<Vec<NIdx>, CheckError> {
    pin_reserved(st)
}

/// con-leche: ConLeche/Kernel/Core.lean:324-364 structEtaCertWith
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_tail_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:585-623 structEtaCertWithI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_tail_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// certificate's tail, from the level comparison on: the constructor's levels
/// against the type's, `defEqList (aargs.take tbl.numParams) targs` and the
/// field comparison against the `.proj` nodes.  No type-application
/// certificate and no per-slot one (con-leche task #342 L11b, L-DEAD: `wtb` is
/// the reduced type of `b`, so its spine fits the former's telescope).
pub fn struct_eta_cert_tail(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    us: &LsIdx,
    t: &NIdx,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    aargs: &Vec<EIdx>,
    n_p: u64,
    n_f: u64,
) -> Result<bool, CheckError> {
    match lvls_eq(pers, st, us, us2) {
        Err(e) => Err(e),
        Ok(o) => match lift_fueled(o) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => {
                let head: Vec<EIdx> = take_eidx_n(aargs, n_p);
                match def_eq_list(pers, st, mode, eager, lane, fuel, fe, depth, &head, targs, 0) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match eta_projs(pers, st, t, b, n_f) {
                        Err(e) => Err(e),
                        Ok(projs) => {
                            let rest: Vec<EIdx> = drop_eidx_n(aargs, n_p);
                            def_eq_list(pers, st, mode, eager, lane, fuel, fe, depth, &rest, &projs, 0)
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:324-364 structEtaCertWith
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_at_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:585-623 structEtaCertWithI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// certificate's head: the stuck side's whnf'd type must be a stored,
/// eta-capable inductive whose projection table's constructor is the
/// candidate's own, at the table's parameter count and the former's level
/// parameters.  The constructor and the counts are the table's, at every
/// field count (official: the family's constructor list).
pub fn struct_eta_cert_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvc: &IConstantVal,
    c: &NIdx,
    us: &LsIdx,
    b: &EIdx,
    wtb: &EIdx,
    aargs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, wtb) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const(pers, st, &hd) {
                None => fail_dangling_e(),
                Some((t, us2)) => match env::ifenv_find(pers, fe, &t) {
                    Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
                        let cvt: IConstantVal = env::i_constant_val_dup(cvt0);
                        let eta: bool = caps0.eta;
                        match env::ifenv_find_table(pers, fe, &t) {
                            None => Ok(false),
                            Some(tbl) => {
                                let tctor: NIdx = tbl.ctor.dup2();
                                let n_p: u64 = tbl.num_params;
                                let n_f: u64 = tbl.num_fields;
                                match get_app_args(pers, st, CORE_WALK_FUEL, wtb) {
                                    Err(e) => Err(e),
                                    Ok(targs) => match view_ls(pers, st, &us2) {
                                        Err(e) => Err(e),
                                        Ok(uslen) => {
                                            if eta
                                                && tctor.eq2(c)
                                                && targs.len() as u64 == n_p
                                                && uslen.len() == cvt.level_params.len()
                                                && nidx_vec_beq(
                                                    &cvc.level_params,
                                                    &cvt.level_params,
                                                )
                                            {
                                                struct_eta_cert_tail(
                                                    pers, st, mode, eager, lane, fuel, fe, depth,
                                                    us, &t, &us2, &targs, b, aargs, n_p, n_f,
                                                )
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                    },
                                }
                            }
                        }
                    }
                    Some(_) => Ok(false),
                    None => Ok(false),
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:324-364 structEtaCertWith
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_with_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:585-623 structEtaCertWithI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_with_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1602-1651 structEtaCertWith` — the
/// structure-eta certificate against the weak-head-normal type `wtb` of the
/// stuck side `b`.
pub fn struct_eta_cert_with(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
    wtb: &EIdx,
) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const(pers, st, &hd) {
                None => fail_dangling_e(),
                Some((c, us)) => match env::ifenv_find(pers, fe, &c) {
                    Some(IConstantInfo::CtorInfo(cvc0, cn_p, cn_f)) => {
                        let cvc: IConstantVal = env::i_constant_val_dup(cvc0);
                        let want: u64 = *cn_p + *cn_f;
                        match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                            Err(e) => Err(e),
                            Ok(aargs) => {
                                if aargs.len() as u64 == want {
                                    struct_eta_cert_at(
                                        pers,
                                        st, mode, eager, lane, fuel, fe, depth, &cvc, &c, &us, b,
                                        wtb, &aargs,
                                    )
                                } else {
                                    Ok(false)
                                }
                            }
                        }
                    }
                    Some(_) => Ok(false),
                    None => Ok(false),
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:704-715 etaCtorShape
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_ctor_shape_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1653-1668 etaCtorShape` — the
/// constructor shape official's `try_eta_struct_core` tests before inferring
/// anything: the candidate's head is a stored constructor applied to exactly
/// its parameters and fields.
pub fn eta_ctor_shape(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    a: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const_name(pers, st, &hd) {
                None => fail_dangling_e(),
                Some(c) => match env::ifenv_find(pers, fe, &c) {
                    Some(IConstantInfo::CtorInfo(_, cn_p, cn_f)) => {
                        let want: u64 = *cn_p + *cn_f;
                        match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                            Err(e) => Err(e),
                            Ok(args) => Ok(args.len() as u64 == want),
                        }
                    }
                    Some(_) => Ok(false),
                    None => Ok(false),
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:717-740 etaCtorPartial
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_ctor_partial_fam_refines, then delete this line
/// con-leche: ConLeche/Cached/StateC.lean:97-115 etaCtorPartialC
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_ctor_partial_fam_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1670-1686 etaCtorPartialFam` — the
/// family half of `etaCtorPartial`: the family the constructor's type ends in
/// is a stored η family whose projection table's constructor is `c`.
pub fn eta_ctor_partial_fam(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    ty: &EIdx,
) -> Result<bool, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, ty) {
        Err(e) => Err(e),
        Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
            Err(e) => Err(e),
            Ok(hd) => if hd.tag() == ETAG_CONST {
                match view_const_name(pers, st, &hd) {
                    None => fail_dangling_e(),
                    Some(t) => match env::ifenv_find(pers, fe, &t) {
                        Some(IConstantInfo::IndInfo(_, caps)) => {
                            let eta: bool = caps.eta;
                            match env::ifenv_find_table(pers, fe, &t) {
                                Some(tbl) => Ok(eta && tbl.ctor.eq2(c)),
                                None => Ok(false),
                            }
                        }
                        Some(_) => Ok(false),
                        None => Ok(false),
                    },
                }
            } else {
                Ok(false)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:717-740 etaCtorPartial
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_ctor_partial_refines, then delete this line
/// con-leche: ConLeche/Cached/StateC.lean:97-115 etaCtorPartialC
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_ctor_partial_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1688-1709 etaCtorPartial` — **a
/// partially applied η constructor** (official's `try_eta_struct_core` since
/// lean4#15373): the candidate's head is a stored constructor applied to fewer
/// than its parameters and fields, of a stored η family whose projection
/// table's constructor it is.  `Some(k)`, `k > 0` the arguments it lacks.
/// Read off the stored records alone, before any inference.
pub fn eta_ctor_partial(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    a: &EIdx,
) -> Result<Option<u64>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const_name(pers, st, &hd) {
                None => fail_dangling_e(),
                Some(c) => match env::ifenv_find(pers, fe, &c) {
                    Some(IConstantInfo::CtorInfo(cvc0, cn_p, cn_f)) => {
                        let ty: EIdx = cvc0.ty.dup2();
                        let want: u64 = *cn_p + *cn_f;
                        match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                            Err(e) => Err(e),
                            Ok(args) => {
                                let n: u64 = args.len() as u64;
                                if n < want {
                                    match eta_ctor_partial_fam(pers, st, fe, &c, &ty) {
                                        Err(e) => Err(e),
                                        Ok(true) => Ok(Some(want - n)),
                                        Ok(false) => Ok(None),
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        }
                    }
                    Some(_) => Ok(None),
                    None => Ok(None),
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:366-387 structEtaFull
/// con-leche: ConLeche/Cached/CoreC.lean:625-635 structEtaFullI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_full_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1711-1720 structEtaFullAt` — the body
/// of **structure η at a fully applied constructor**, past the
/// constructor-shape gate: `b`'s io-inferred type, head-normalised, and the
/// certificate against it.
pub fn struct_eta_full_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, b) {
        Err(e) => Err(e),
        Ok(tb) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tb) {
            Err(e) => Err(e),
            Ok(wtb) => {
                struct_eta_cert_with(pers, st, mode, eager, lane, fuel, fe, depth, a, b, &wtb)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:366-387 structEtaFull
/// con-leche: ConLeche/Cached/CoreC.lean:625-635 structEtaFullI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_full_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1722-1729 structEtaFull` — **structure
/// η at a fully applied constructor**.  The constructor-shape test comes FIRST
/// (the divergence audit's D13).
pub fn struct_eta_full(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match eta_ctor_shape(pers, st, fe, a) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => struct_eta_full_at(pers, st, mode, eager, lane, fuel, fe, depth, a, b),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:389-401 structEtaExpand
/// con-leche: ConLeche/Cached/CoreC.lean:637-646 structEtaExpandI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_expand_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1731-1749 structEtaExpand` — **the
/// η-expansion of a partially applied constructor**: both sides applied to
/// fresh variables along the constructor side's type `ta`, one binder per
/// missing argument, read syntactically; at the full application,
/// `struct_eta_full`.
pub fn struct_eta_expand(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    k: u64,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
    ta: &EIdx,
) -> Result<bool, CheckError> {
    if k == 0 {
        struct_eta_full(pers, st, mode, eager, lane, fuel, fe, depth, a, b)
    } else if ta.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, ta) {
            None => fail_dangling_e(),
            Some((dom, body)) => match intern_e_fvar(pers, st, depth, dom) {
                Err(e) => Err(e),
                Ok(fv) => match intern_e_app(pers, st, a.dup2(), fv.dup2()) {
                    Err(e) => Err(e),
                    Ok(a2) => match intern_e_app(pers, st, b.dup2(), fv.dup2()) {
                        Err(e) => Err(e),
                        Ok(b2) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                            Err(e) => Err(e),
                            Ok(body2) => struct_eta_expand(
                                pers, st, mode, eager, lane, fuel, fe, k - 1, depth + 1, &a2, &b2,
                                &body2,
                            ),
                        },
                    },
                },
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:403-421 structEtaCert
/// con-leche: ConLeche/Cached/CoreC.lean:648-661 structEtaCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_partial_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1751-1763 structEtaCertPartial` — the
/// partial-constructor arm of `structEtaCert`, at `k` missing arguments: the
/// other side neutral, the two io-inferred types compared (official's
/// `is_def_eq(t_type, s_type)`), then both sides η-expanded.
pub fn struct_eta_cert_partial(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    k: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match io_neutral(pers, st, b) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, a) {
            Err(e) => Err(e),
            Ok(ta) => match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, b) {
                Err(e) => Err(e),
                Ok(tb) => match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &tb, &ta) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => {
                        struct_eta_expand(pers, st, mode, eager, lane, fuel, fe, k, depth, a, b, &ta)
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:403-421 structEtaCert
/// con-leche: ConLeche/Cached/CoreC.lean:648-661 structEtaCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_eta_cert_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1765-1776 structEtaCert` — structural
/// eta certification (official's `try_eta_struct_core`): `a` is a constructor
/// application of a stored η family, fully applied (`struct_eta_full`'s body;
/// the shape gate is read once) or partially (`eta_ctor_partial`).
pub fn struct_eta_cert(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match eta_ctor_shape(pers, st, fe, a) {
        Err(e) => Err(e),
        Ok(true) => struct_eta_full_at(pers, st, mode, eager, lane, fuel, fe, depth, a, b),
        Ok(false) => match eta_ctor_partial(pers, st, fe, a) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(k)) => {
                struct_eta_cert_partial(pers, st, mode, eager, lane, fuel, fe, depth, k, a, b)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:423-428 isPropType
/// con-leche: ConLeche/Cached/CoreC.lean:663-672 isPropTypeI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::is_prop_type_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1778-1791 isPropType` — **is a
/// proposition** (official's `is_prop`): `t`'s io-inferred type head-normalises
/// to a sort equivalent to `Prop`.
pub fn is_prop_type(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    t: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, t) {
        Err(e) => Err(e),
        Ok(tt) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tt) {
            Err(e) => Err(e),
            Ok(w) => if w.tag() == ETAG_SORT {
                match view_sort(pers, st, &w) {
                    None => fail_dangling_e(),
                    Some(u) => match zero_level(st) {
                        Err(e) => Err(e),
                        Ok(z) => match lvl_eq(pers, st, &u, &z) {
                            Err(e) => Err(e),
                            Ok(o) => lift_fueled(o),
                        },
                    },
                }
            } else {
                Ok(false)
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:430-445 unitLikeFields
/// con-leche: ConLeche/Cached/CoreC.lean:674-688 unitLikeFieldsI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_fields_next_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1793-1816 unitLikeFields` — one field
/// accepted: the field opened at a fresh variable, then the rest of the loop.
/// Both arms of the cited loop call it.
pub fn unit_like_fields_next(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    ul_fuel: u64,
    n: u64,
    depth: u64,
    dom: &EIdx,
    body: &EIdx,
) -> Result<bool, CheckError> {
    match intern_e_fvar(pers, st, depth, dom.dup2()) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
            Err(e) => Err(e),
            Ok(body2) => {
                unit_like_fields(pers, st, mode, eager, lane, fuel, fe, ul_fuel, n, depth + 1, &body2)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:430-445 unitLikeFields
/// con-leche: ConLeche/Cached/CoreC.lean:674-688 unitLikeFieldsI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_fields_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1793-1816 unitLikeFields` — **the field
/// loop of official's `is_unit_like`**: each of the `n` field binders of an η
/// family's instance telescope has a proposition or a unit-like type
/// (`unit_like_loop` at `ul_fuel`, the cited loop's `ul`), the field opened at
/// a fresh variable before the next.  The binders are syntactic.
pub fn unit_like_fields(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    ul_fuel: u64,
    n: u64,
    depth: u64,
    tele: &EIdx,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(true)
    } else if tele.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, tele) {
            None => fail_dangling_e(),
            Some((dom, body)) => match is_prop_type(pers, st, mode, eager, lane, fuel, fe, depth, &dom) {
                Err(e) => Err(e),
                Ok(true) => unit_like_fields_next(
                    pers, st, mode, eager, lane, fuel, fe, ul_fuel, n - 1, depth, &dom, &body,
                ),
                Ok(false) => match unit_like_loop(pers, st, mode, eager, lane, fuel, fe, ul_fuel, depth, &dom) {
                    Err(e) => Err(e),
                    Ok(true) => unit_like_fields_next(
                        pers, st, mode, eager, lane, fuel, fe, ul_fuel, n - 1, depth, &dom, &body,
                    ),
                    Ok(false) => Ok(false),
                },
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:447-450 unitLikeFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1818-1821 unitLikeFuel` — recursion
/// budget of the unit-like test (`unit_like_loop`).  Exhaustion is "not
/// unit-like", which is always sound.
pub const UNIT_LIKE_FUEL: u64 = 4611686018427387904; // 2^62

/// con-leche: ConLeche/Kernel/CoreDefs.lean:750-777 unitLikeShape
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_shape_at_refines, then delete this line
/// con-leche: ConLeche/Kernel/CoreDefs.lean:742-748 unitFieldTele
/// con-leche: ConLeche/Cached/CoreC.lean:103-124 unitLikeShapeF
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_shape_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1823-1839 unitLikeShapeAt` — the
/// field telescope of an instance at its family's table: the table's
/// constructor, stored, its type at the instance's levels `us`, the table's
/// `n_p` parameter binders dropped and instantiated with the instance's
/// arguments in one pass.
pub fn unit_like_shape_at(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    us: &LsIdx,
    targs: &Vec<EIdx>,
    tctor: &NIdx,
    n_p: u64,
    n_f: u64,
) -> Result<Option<(EIdx, u64)>, CheckError> {
    match env::ifenv_find(pers, fe, tctor) {
        Some(IConstantInfo::CtorInfo(cvc0, _, _)) => {
            let cvc: IConstantVal = env::i_constant_val_dup(cvc0);
            match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cvc.level_params, us, &cvc.ty) {
                Err(e) => Err(e),
                Ok(cty) => match peel_pis(pers, st, n_p, &cty) {
                    Err(e) => Err(e),
                    Ok(None) => Ok(None),
                    Ok(Some(body)) => {
                        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &body, targs, 0) {
                            Err(e) => Err(e),
                            Ok(tele) => Ok(Some((tele, n_f))),
                        }
                    }
                },
            }
        }
        Some(_) => Ok(None),
        None => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:750-777 unitLikeShape
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_shape_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:103-124 unitLikeShapeF
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_shape_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1841-1868 unitLikeShape` — **the shape
/// of an instance in official's `is_unit_like`**, read off the stored records:
/// `w` is an instance of a stored η family at its parameters (the table's
/// count), whose constructor's field telescope at the instance's parameters is
/// `tele` with `n` fields to check (`Some((tele, n))`), or not (`None`).
pub fn unit_like_shape(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    w: &EIdx,
) -> Result<Option<(EIdx, u64)>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, w) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const(pers, st, &hd) {
                None => fail_dangling_e(),
                Some((s, us)) => match env::ifenv_find(pers, fe, &s) {
                    Some(IConstantInfo::IndInfo(cvs0, caps0)) => {
                        let nlp: usize = cvs0.level_params.len();
                        let eta: bool = caps0.eta;
                        match view_ls(pers, st, &us) {
                            Err(e) => Err(e),
                            Ok(usl) => {
                                if eta && usl.len() == nlp {
                                    match env::ifenv_find_table(pers, fe, &s) {
                                        None => Ok(None),
                                        Some(tbl) => {
                                            let tctor: NIdx = tbl.ctor.dup2();
                                            let n_p: u64 = tbl.num_params;
                                            let n_f: u64 = tbl.num_fields;
                                            match get_app_args(pers, st, CORE_WALK_FUEL, w) {
                                                Err(e) => Err(e),
                                                Ok(targs) => {
                                                    if targs.len() as u64 == n_p {
                                                        unit_like_shape_at(
                                                            pers, st, fe, &us, &targs, &tctor, n_p,
                                                            n_f,
                                                        )
                                                    } else {
                                                        Ok(None)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        }
                    }
                    Some(_) => Ok(None),
                    None => Ok(None),
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:452-462 unitLikeStruct
/// con-leche: ConLeche/Cached/CoreC.lean:690-696 unitLikeStructI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_struct_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1870-1879 unitLikeStruct` — **the
/// structure arm of official's `is_unit_like`**: `w`, a head normal form that
/// is no ∀, is an instance of a stored η family every field of whose
/// constructor, at the instance's parameters, has a proposition or a unit-like
/// type (a fieldless family has none to check).
pub fn unit_like_struct(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    ul_fuel: u64,
    depth: u64,
    w: &EIdx,
) -> Result<bool, CheckError> {
    match unit_like_shape(pers, st, fe, w) {
        Err(e) => Err(e),
        Ok(None) => Ok(false),
        Ok(Some((tele, n))) => {
            unit_like_fields(pers, st, mode, eager, lane, fuel, fe, ul_fuel, n, depth, &tele)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:464-476 unitLikeLoop
/// con-leche: ConLeche/Cached/CoreC.lean:698-708 unitLikeLoopI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::unit_like_loop_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1881-1898 unitLikeLoop` — **is a type
/// unit-like** (official's `is_unit_like`, lean4#15372): its head normal form
/// is a ∀ whose codomain, opened at a fresh variable, is unit-like, or an
/// instance of a stored η family every field of whose constructor is a
/// proposition or unit-like.  Structural on `ul_fuel`.
pub fn unit_like_loop(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    ul_fuel: u64,
    depth: u64,
    t: &EIdx,
) -> Result<bool, CheckError> {
    if ul_fuel == 0 {
        Ok(false)
    } else {
        match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, t) {
            Err(e) => Err(e),
            Ok(w) => if w.tag() == ETAG_FORALL_E {
                match view_bind(pers, st, &w) {
                    None => fail_dangling_e(),
                    Some((dom, body)) => match intern_e_fvar(pers, st, depth, dom) {
                        Err(e) => Err(e),
                        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                            Err(e) => Err(e),
                            Ok(body2) => unit_like_loop(
                                pers, st, mode, eager, lane, fuel, fe, ul_fuel - 1, depth + 1, &body2,
                            ),
                        },
                    },
                }
            } else {
                unit_like_struct(pers, st, mode, eager, lane, fuel, fe, ul_fuel - 1, depth, &w)
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:478-495 structUnitCert
/// con-leche: ConLeche/Cached/CoreC.lean:710-722 structUnitCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_unit_cert_tail_refines, then delete this line
/// con-leche: ConLeche/Kernel/ExprOps.lean:835-838 isForallE
/// Lean twin: `proof/ConRon/Arena/Core.lean:1900-1918 structUnitCert` — the
/// certificate's tail, once `a`'s type is unit-like: `b`'s whnf'd type, which
/// must not be a `∀` unless `b` is neutral (con-leche task #342 L18), is
/// defeq to `a`'s.  No type-application certificate (task #342 L11b), as
/// official's `is_def_eq_unit_like`.
pub fn struct_unit_cert_tail(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    wta: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, b) {
        Err(e) => Err(e),
        Ok(tb) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tb) {
            Err(e) => Err(e),
            Ok(wtb) => {
                let guard: Result<bool, CheckError> = if wtb.tag() == ETAG_FORALL_E {
                    io_neutral(pers, st, b)
                } else {
                    Ok(true)
                };
                match guard {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, wta, &wtb),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:478-495 structUnitCert
/// con-leche: ConLeche/Cached/CoreC.lean:710-722 structUnitCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::struct_unit_cert_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1900-1918 structUnitCert` —
/// **unit-likeness** (official's `is_def_eq_unit_like`): `a`'s io-inferred
/// type, head-normalised, is unit-like (`unit_like_loop`), and `b`'s type is
/// definitionally equal to it.  A side whose type is a ∀ must be neutral.
pub fn struct_unit_cert(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(ta) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &ta) {
            Err(e) => Err(e),
            Ok(wta) => {
                let guard: Result<bool, CheckError> = if wta.tag() == ETAG_FORALL_E {
                    io_neutral(pers, st, a)
                } else {
                    Ok(true)
                };
                match guard {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match unit_like_loop(
                        pers, st, mode, eager, lane, fuel, fe, UNIT_LIKE_FUEL, depth, &wta,
                    ) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => struct_unit_cert_tail(
                            pers, st, mode, eager, lane, fuel, fe, depth, &wta, b,
                        ),
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:497-523 etaCert
/// con-leche: ConLeche/Cached/CoreC.lean:724-748 etaCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_cert_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1920-1946 etaCert` — eta
/// certification for a one-sided λ against a stuck term `b`: `b`'s head is no
/// λ and no `let` (`Expr.ioNeutral`, con-leche task #342 L18), its whnf'd
/// type is a `∀` whose domain is defeq to the λ's, and (`eta_cert_body`) the
/// λ's body is pointwise the application of `b`.
pub fn eta_cert(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty1: &EIdx,
    body1: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match io_neutral(pers, st, b) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, b) {
            Err(e) => Err(e),
            Ok(tb) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tb) {
                Err(e) => Err(e),
                Ok(w) => if w.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &w) {
                        None => fail_dangling_e(),
                        Some((ty2, cod2)) => {
                            match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &ty2, ty1) {
                                Err(e) => Err(e),
                                Ok(false) => Ok(false),
                                Ok(true) => eta_cert_body(
                                    pers, st, mode, eager, lane, fuel, fe, depth, ty1, body1, &cod2, b,
                                ),
                            }
                        }
                    }
                } else {
                    Ok(false)
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:497-523 etaCert
/// con-leche: ConLeche/Cached/CoreC.lean:724-748 etaCertI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::eta_cert_body_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1920-1946 etaCert` — the cited
/// certificate's body, once the domains agree: open the λ at a fresh free
/// variable and compare against `b` applied to it; then, at the verified mode
/// only, **the η check** (con-leche task #342, T2): the λ body's FULL-grade
/// type against the `∀`'s codomain at the variable.
pub fn eta_cert_body(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty1: &EIdx,
    body1: &EIdx,
    cod2: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match intern_e_fvar(pers, st, depth, ty1.dup2()) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body1, &fv, 0) {
            Err(e) => Err(e),
            Ok(b1) => match intern_e_app(pers, st, b.dup2(), fv.dup2()) {
                Err(e) => Err(e),
                Ok(ba) => {
                    match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth + 1, &b1, &ba) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            if verified_checks(mode) {
                                match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth + 1, &b1) {
                                    Err(e) => Err(e),
                                    Ok(t1) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, cod2, &fv, 0) {
                                        Err(e) => Err(e),
                                        Ok(t2) => knot_defeq(
                                            pers, st, mode, eager, lane, fuel, fe, depth + 1, &t1, &t2,
                                        ),
                                    },
                                }
                            } else {
                                Ok(true)
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:525-532 stuckIrrel
/// con-leche: ConLeche/Cached/CoreC.lean:750-757 stuckIrrelI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::stuck_irrel_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1948-1956 stuckIrrel` — the
/// fallback for structurally distinct stuck terms: structural eta in either
/// direction, unit-likeness, else proof irrelevance.
pub fn stuck_irrel(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match struct_eta_cert(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => match struct_eta_cert(pers, st, mode, eager, lane, fuel, fe, depth, b, a) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => match struct_unit_cert(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => proof_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a, b),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:534-545 formerSortLoop
/// con-leche: ConLeche/Cached/CoreC.lean:759-773 formerSortLoopI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::former_sort_loop_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1958-1982 formerSortLoop` — **official's
/// walk to a family's sort** (the loop of `check_inductive_types` at the use):
/// `n` binders down, each reached by head normalization (the knot's `whnf`),
/// then a sort; `none` where the type does not get there.  Structural on `n`;
/// the body is instantiated through the memoized `instantiate1`, as the cached
/// twin's `inst1M`.
pub fn former_sort_loop(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    n: u64,
    e: &EIdx,
) -> Result<Option<LIdx>, CheckError> {
    match knot_whnf(pers, st, mode, eager, lane, fuel, fe, d, e) {
        Err(er) => Err(er),
        Ok(w) => if n == 0 {
            if w.tag() == ETAG_SORT {
                match view_sort(pers, st, &w) {
                    None => fail_dangling_e(),
                    Some(s) => Ok(Some(s)),
                }
            } else {
                Ok(None)
            }
        } else if w.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, &w) {
                None => fail_dangling_e(),
                Some((dom, b)) => match intern_e_fvar(pers, st, d, dom) {
                    Err(er) => Err(er),
                    Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &fv, 0) {
                        Err(er) => Err(er),
                        Ok(b2) => former_sort_loop(pers, st, mode, eager, lane, fuel, fe, d + 1, n - 1, &b2),
                    },
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:547-560 formerNeverZeroAt
/// con-leche: ConLeche/Cached/CoreC.lean:775-786 formerNeverZeroI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::former_never_zero_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:1984-2001 formerNeverZeroAt` — **is a
/// family's sort never zero at the levels `us`** (official `is_never_zero`),
/// computed where it is asked.  A stored type that ends in a sort is read off
/// directly (`former_never_zero`); any other is walked by `former_sort_loop` at
/// the use's levels, and where the walk reaches no sort the answer is the
/// conservative `false`.
pub fn former_never_zero_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    us: &LsIdx,
) -> Result<bool, CheckError> {
    match former_res_sort(pers, st, &cvt.ty) {
        Err(er) => Err(er),
        Ok(Some(_)) => former_never_zero(pers, st, cvt, us),
        Ok(None) => match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cvt.level_params, us, &cvt.ty) {
            Err(er) => Err(er),
            Ok(ty) => {
                match former_sort_loop(pers, st, mode, eager, lane, fuel, fe, 0, caps.nparams + caps.n_idx, &ty) {
                    Err(er) => Err(er),
                    Ok(Some(s)) => match read_level_m(pers, st, &s) {
                        Err(er) => Err(er),
                        Ok(l) => Ok(prop_when::is_never(&level::zeroness_of(&l))),
                    },
                    Ok(None) => Ok(false),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:562-583 iotaCase3At
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_case3_at_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:794-805 iotaCase3I
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_case3_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2003-2021 iotaCase3At` — **case 3 of the ι
/// case split** (con-leche task #342 L10, S5c): a rule that is not K (the
/// record's `isK`) whose constructor's family may be `Prop` at the comparand
/// levels `us`.  The family is not read at a K recursor.
pub fn iota_case3_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    is_k: bool,
    cvj: &IConstantVal,
    us: &LsIdx,
) -> Result<bool, CheckError> {
    if is_k {
        Ok(false)
    } else {
        match ctor_family(pers, st, fe, cvj) {
            Err(er) => Err(er),
            Ok(Some((cvt, caps))) => match view_ls_len(pers, st, us) {
                None => fail_dangling_ls(),
                Some(usl) => {
                    if cvt.level_params.len() == usl {
                        match former_never_zero_at(pers, st, mode, eager, lane, fuel, fe, &cvt, &caps, us) {
                            Err(er) => Err(er),
                            Ok(nz) => Ok(!nz),
                        }
                    } else {
                        Ok(true)
                    }
                }
            },
            Ok(None) => Ok(true),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:779-783 etaFabArgsE
/// Lean twin: `proof/ConRon/Arena/Core.lean:2023-2029 etaFabArgsE` — the
/// eta-rescue fabrication's argument spine: the major's type's arguments, then
/// the major's projections (`etaProjs`).
pub fn eta_fab_args_e(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    targs: &Vec<EIdx>,
    major: &EIdx,
    n_f: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match eta_projs(pers, st, t, major, n_f) {
        Err(e) => Err(e),
        Ok(ps) => Ok(append_eidx_of(targs, &ps)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:891-901 andRescueSlotsOf
/// Lean twin: `proof/ConRon/Arena/Core.lean:2031-2043 andRescueSlotsGo` — the
/// two-slot walk, as a counted recursion (con-leche's `(List.range 2).all`):
/// each slot stored, naming the rule's constructor at the major's parameter
/// count, with two fields.
pub fn and_rescue_slots_go(
    pers: &PersTier,
    fe: &IFEnv,
    an: &NIdx,
    ctor: &NIdx,
    n_p: u64,
    n: u64,
    j: u64,
) -> bool {
    if n == 0 {
        true
    } else {
        match env::ifenv_find_proj(pers, fe, an, j) {
            Some(entry) => {
                if entry.ctor.eq2(ctor) && entry.num_params == n_p && entry.num_fields == 2 {
                    and_rescue_slots_go(pers, fe, an, ctor, n_p, n - 1, j + 1)
                } else {
                    false
                }
            }
            None => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:891-901 andRescueSlotsOf
/// con-leche: ConLeche/Kernel/CoreDefs.lean:903-905 andRescueSlots
/// con-leche: ConLeche/Kernel/FEnv.lean:187-189 FEnv.andRescueSlotsF
/// Lean twin: `proof/ConRon/Arena/Core.lean:2045-2052 andRescueSlots` — **the
/// pinned `And`'s projection slots, ready to fire.**  One twin for con-leche's
/// three spellings (deviation 1).
pub fn and_rescue_slots(
    pers: &PersTier,
    st: &AState,
    fe: &IFEnv,
    ctor: &NIdx,
    n_p: u64,
) -> Result<bool, CheckError> {
    match pin_and(st) {
        Err(e) => Err(e),
        Ok(an) => Ok(and_rescue_slots_go(pers, fe, &an, ctor, n_p, 2, 0)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:907-924 etaRescueTable?
/// Lean twin: `proof/ConRon/Arena/Core.lean:2054-2069 etaRescueTable?` — **the
/// structure-η rescue's standing condition, at use**: the single rule's
/// constructor `ctor` (stored as `cvj`) is the constructor of its family's
/// projection table `tbl` (the family `cvt` structure-like, `IIndCaps.eta`),
/// and carries the family's level parameters; the table, for the
/// fabrication's counts.  `And.intro` is left to `And`'s own rescue.  The
/// cited `&&` chain, left to right (the `And.intro` pin is interned only when
/// the chain reaches it).
pub fn eta_rescue_table<'a>(
    st: &AState,
    tbl: Option<&'a IProjTable>,
    ctor: &NIdx,
    cvj: &IConstantVal,
    cvt: &IConstantVal,
    caps: &IIndCaps,
) -> Result<Option<&'a IProjTable>, CheckError> {
    match tbl {
        None => Ok(None),
        Some(t) => {
            if caps.eta && t.ctor.eq2(ctor) && nidx_vec_beq(&cvj.level_params, &cvt.level_params) {
                match pin_and_intro(st) {
                    Err(e) => Err(e),
                    Ok(ai) => {
                        if !ctor.eq2(&ai) {
                            Ok(Some(t))
                        } else {
                            Ok(None)
                        }
                    }
                }
            } else {
                Ok(None)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The stuck-major rescue and the ι step (`Core.lean:1584-1936`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::fab_scope_ok_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::fab_scope_ok_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2075-2092 fabScopeOk` — the scope
/// guard the three rescue branches share: the fabricated major is well-scoped,
/// closed under loose bvars, and mentions no free variable the stuck major
/// does not.
///
/// **The three tests are the EXECUTED tier's** (task #97g item 5).
/// `Kernel/Core.lean` spells the last one `fab.fvarLeaves.all (fun l =>
/// major.fvarLeaves.contains l)`, and task #97-P4d ported that literally: two
/// unmemoized DAG walks and a quadratic list containment, which on
/// `core.ndjson`'s first 27 920 declarations was 43.9 % of the whole run's
/// cycles.  `Cached/CoreC.lean` runs `wscopedBC`, `looseBVarsBounded` off the
/// packed field and `leafGuard` — the same predicate, one memoized walk each —
/// and those are what runs here. The test module of `arena::expr_ops`
/// checks `leaf_guard` against the literal containment.
pub fn fab_scope_ok(
    pers: &PersTier,
    st: &mut AState,
    depth: u64,
    fab: &EIdx,
    major: &EIdx,
) -> Result<bool, CheckError> {
    match wscoped_b_fast(pers, st, CORE_WALK_FUEL, depth, fab) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match loose_bvars_bounded_fast(pers, st, CORE_WALK_FUEL, 0, fab) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => leaf_guard(pers, st, CORE_WALK_FUEL, fab, major),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_certs_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_certs_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the
/// K and `And` rescues' checks, once the fabricated major is built: the scope
/// guard, the official `to_cnstr_when_K` type check (both modes) and proof
/// irrelevance, a certificate family off at the trusted mode
/// (`certAtI mode (proofIrrelI …)`).  Task #119: the synthetic-spine
/// telescope certificate that stood between the guard and the type check is
/// gone (con-leche task #342 L-DEAD), and so are its arguments.
pub fn major_to_ctor_certs(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    fab: &EIdx,
    tmaj: &EIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match fab_scope_ok(pers, st, depth, fab, major) {
        Err(e) => Err(e),
        Ok(false) => Ok(major.dup2()),
        Ok(true) => match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, fab) {
            Err(e) => Err(e),
            Ok(tfab) => match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, tmaj, &tfab) {
                Err(e) => Err(e),
                Ok(false) => Ok(major.dup2()),
                Ok(true) => {
                    let ir = if !verified_checks(mode) {
                        Ok(true)
                    } else {
                        proof_irrel(pers, st, mode, eager, lane, fuel, fe, depth, fab, major)
                    };
                    match ir {
                        Err(e) => Err(e),
                        Ok(true) => Ok(fab.dup2()),
                        Ok(false) => Ok(major.dup2()),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_k_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the
/// K-flagged branch (`to_cnstr_when_K`): the major's whnf'd type is the rule's
/// own inductive, and the fabricated major is its constructor at the type's
/// leading parameters.
pub fn major_to_ctor_k(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    ctor: &NIdx,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => if hd0.tag() == ETAG_CONST {
                    match view_const(pers, st, &hd0) {
                        None => fail_dangling_e(),
                        Some((t2, ust)) => match view_ls(pers, st, &ust) {
                            Err(e) => Err(e),
                            Ok(ustl) => {
                                if t2.eq2(t) && cvj.level_params.len() == ustl.len() {
                                    match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                                        Err(e) => Err(e),
                                        Ok(targs) => {
                                            if cn_p <= targs.len() as u64 {
                                                let spine: Vec<EIdx> =
                                                    take_eidx(&targs, cn_p as usize);
                                                match intern_e_const(pers, st, ctor.dup2(), ust.dup2()) {
                                                    Err(e) => Err(e),
                                                    Ok(hd) => {
                                                        match mk_app_n(pers, st, &hd, &spine) {
                                                            Err(e) => Err(e),
                                                            Ok(fab) => major_to_ctor_certs(
                                                                pers, st, mode, eager, lane, fuel,
                                                                fe, depth, &fab, &tmaj, major,
                                                            ),
                                                        }
                                                    }
                                                }
                                            } else {
                                                Ok(major.dup2())
                                            }
                                        }
                                    }
                                } else {
                                    Ok(major.dup2())
                                }
                            }
                        },
                    }
                } else {
                    Ok(major.dup2())
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the
/// η-capable branch: the fabricated major is the table's constructor at the
/// type's parameters and the `.proj` nodes of the stuck major, the counts the
/// family's projection table's, at every field count.
pub fn major_to_ctor_eta(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    tbl: &IProjTable,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => if hd0.tag() == ETAG_CONST {
                    match view_const(pers, st, &hd0) {
                        None => fail_dangling_e(),
                        Some((t2, ust)) => match view_ls(pers, st, &ust) {
                            Err(e) => Err(e),
                            Ok(ustl) => match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                                Err(e) => Err(e),
                                Ok(targs) => {
                                    if t2.eq2(t)
                                        && targs.len() as u64 == tbl.num_params
                                        && ustl.len() == cvt.level_params.len()
                                    {
                                        major_to_ctor_eta_sort(
                                            pers, st, mode, eager, lane, fuel, fe, depth, cvt,
                                            caps, tbl, t, &ust, &targs, major,
                                        )
                                    } else {
                                        Ok(major.dup2())
                                    }
                                }
                            },
                        },
                    }
                } else {
                    Ok(major.dup2())
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_sort_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_sort_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the η
/// branch's sort test: the family's sort, never zero at the major type's
/// levels (`formerNeverZeroAt`, computed here), then the fabrication.
pub fn major_to_ctor_eta_sort(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    tbl: &IProjTable,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match former_never_zero_at(pers, st, mode, eager, lane, fuel, fe, cvt, caps, ust) {
        Err(e) => Err(e),
        Ok(true) => major_to_ctor_eta_build(pers, st, depth, &tbl.ctor, tbl.num_fields, t, ust, targs, major),
        Ok(false) => Ok(major.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_build_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:807-906 majorToCtorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_eta_build_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the η
/// branch's fabrication: the argument spine, the table's constructor `ctor`
/// at `n_f` projections, and the scope guard.  No certificate on the
/// fabricated spine (con-leche task #342 L11b): the major is the fabrication
/// by the family's η law.
pub fn major_to_ctor_eta_build(
    pers: &PersTier,
    st: &mut AState,
    depth: u64,
    ctor: &NIdx,
    n_f: u64,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match eta_fab_args_e(pers, st, t, targs, major, n_f) {
        Err(e) => Err(e),
        Ok(fab_args) => match intern_e_const(pers, st, ctor.dup2(), ust.dup2()) {
            Err(e) => Err(e),
            Ok(hd) => match mk_app_n(pers, st, &hd, &fab_args) {
                Err(e) => Err(e),
                Ok(fab) => match fab_scope_ok(pers, st, depth, &fab, major) {
                    Err(e) => Err(e),
                    Ok(true) => Ok(fab),
                    Ok(false) => Ok(major.dup2()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_and_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — **THE
/// `And`-ONLY η RESCUE** (the user ruling: `And` and nothing else): the
/// fabricated major is `And.intro` at the two `.proj` nodes of the stuck one.
pub fn major_to_ctor_and(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    ctor: &NIdx,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => if hd0.tag() == ETAG_CONST {
                    match view_const(pers, st, &hd0) {
                        None => fail_dangling_e(),
                        Some((t2, ust)) => match view_ls(pers, st, &ust) {
                            Err(e) => Err(e),
                            Ok(ustl) => match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                                Err(e) => Err(e),
                                Ok(targs) => {
                                    match and_rescue_slots(pers, st, fe, ctor, cn_p) {
                                        Err(e) => Err(e),
                                        Ok(ars) => {
                                            if t2.eq2(t)
                                                && targs.len() as u64 == cn_p
                                                && cvj.level_params.len() == ustl.len()
                                                && ars
                                            {
                                                major_to_ctor_and_build(
                                                    pers, st, mode, eager, lane, fuel, fe, depth,
                                                    ctor, t, &ust, &targs, &tmaj, major,
                                                )
                                            } else {
                                                Ok(major.dup2())
                                            }
                                        }
                                    }
                                }
                            },
                        },
                    }
                } else {
                    Ok(major.dup2())
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_and_build_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the `And`
/// branch's fabrication and its certificate chain.
pub fn major_to_ctor_and_build(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ctor: &NIdx,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    tmaj: &EIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match intern_e_proj(pers, st, t.dup2(), 0, major.dup2()) {
        Err(e) => Err(e),
        Ok(p0) => match intern_e_proj(pers, st, t.dup2(), 1, major.dup2()) {
            Err(e) => Err(e),
            Ok(p1) => {
                let fab_args: Vec<EIdx> =
                    snoc2_eidx_of(targs, &p0, &p1);
                match intern_e_const(pers, st, ctor.dup2(), ust.dup2()) {
                    Err(e) => Err(e),
                    Ok(hd) => match mk_app_n(pers, st, &hd, &fab_args) {
                        Err(e) => Err(e),
                        Ok(fab) => major_to_ctor_certs(
                            pers, st, mode, eager, lane, fuel, fe, depth, &fab, tmaj, major,
                        ),
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — the
/// three-way branch, once the rule's constructor and its inductive have been
/// found: the record's K flag, the η family (`etaRescueTable?` at the
/// family's projection table, decided here), or the pinned `And`.
pub fn major_to_ctor_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    ctor: &NIdx,
    is_k: bool,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    if is_k {
        major_to_ctor_k(pers, st, mode, eager, lane, fuel, fe, depth, cvj, cn_p, ctor, t, major)
    } else {
        match eta_rescue_table(st, env::ifenv_find_table(pers, fe, t), ctor, cvj, cvt, caps) {
            Err(e) => Err(e),
            Ok(Some(tbl)) => {
                major_to_ctor_eta(pers, st, mode, eager, lane, fuel, fe, depth, cvt, caps, tbl, t, major)
            }
            Ok(None) => match pin_and(st) {
                Err(e) => Err(e),
                Ok(an) => {
                    if t.eq2(&an) {
                        major_to_ctor_and(
                            pers,
                            st, mode, eager, lane, fuel, fe, depth, cvj, cn_p, ctor, t, major,
                        )
                    } else {
                        Ok(major.dup2())
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:601-757 majorToCtor
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::major_to_ctor_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2094-2208 majorToCtor` — **the
/// stuck-major rescue** (`to_cnstr_when_K` and `to_cnstr_when_structure`): a
/// recursor's major premise that does not whnf to a constructor application
/// may still be *replaced* by one — K-flagged (the record's `isK`), η-capable,
/// or the pinned `And`.  An uncertified major stays put.
pub fn major_to_ctor(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    _rec_name: &NIdx,
    is_k: bool,
    rules: &Vec<IRecRule>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match is_ctor_app(pers, st, fe, major) {
        Err(e) => Err(e),
        Ok(true) => Ok(major.dup2()),
        Ok(false) => {
            if rules.len() != 1 {
                Ok(major.dup2())
            } else {
                let ctor: NIdx = rules[0].ctor.dup2();
                match env::ifenv_find(pers, fe, &ctor) {
                    Some(IConstantInfo::CtorInfo(cvj0, cn_p0, _)) => {
                        let cvj: IConstantVal = env::i_constant_val_dup(cvj0);
                        let cn_p: u64 = *cn_p0;
                        match pi_result(pers, st, CORE_WALK_FUEL, &cvj.ty) {
                            Err(e) => Err(e),
                            Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
                                Err(e) => Err(e),
                                Ok(hd) => if hd.tag() == ETAG_CONST {
                                    match view_const_name(pers, st, &hd) {
                                        None => fail_dangling_e(),
                                        Some(t) => {
                                            match env::ifenv_find(pers, fe, &t) {
                                                Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
                                                    let cvt: IConstantVal =
                                                        env::i_constant_val_dup(cvt0);
                                                    let caps: IIndCaps =
                                                        env::i_ind_caps_dup(caps0);
                                                    major_to_ctor_at(
                                                        pers,
                                                        st, mode, eager, lane, fuel, fe, depth,
                                                        &cvj, cn_p, &ctor, is_k, &cvt,
                                                        &caps, &t, major,
                                                    )
                                                }
                                                Some(_) => Ok(major.dup2()),
                                                None => Ok(major.dup2()),
                                            }
                                        },
                                    }
                                } else {
                                    Ok(major.dup2())
                                },
                            },
                        }
                    }
                    Some(_) => Ok(major.dup2()),
                    None => Ok(major.dup2()),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:759-771 litMajorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:2210-2223 litMajorToCtor` — convert
/// a literal major premise to constructor form: a `Nat` literal one layer, a
/// `String` literal to its *reduced* constructor form.
pub fn lit_major_to_ctor(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if h.tag() == ETAG_LIT {
        match view_lit(pers, st, h) {
            None => fail_dangling_e(),
            Some(Literal::StrVal(s)) => {
                let cs: Vec<u32> = expr::str_copy(&s);
                match str_lit_stored(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(h.dup2()),
                    Ok(true) => match str_lit_to_constructor(pers, st, &cs) {
                        Err(e) => Err(e),
                        Ok(c) => knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &c),
                    },
                }
            }
            Some(_) => lit_to_ctor_if_nat(pers, st, fe, h),
        }
    } else {
        lit_to_ctor_if_nat(pers, st, fe, h)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:773-787 projLitToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:2225-2237 projLitToCtor` — convert
/// a string-literal projection scrutinee to its *reduced* constructor form.
pub fn proj_lit_to_ctor(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if h.tag() == ETAG_LIT {
        match view_lit(pers, st, h) {
            None => fail_dangling_e(),
            Some(Literal::StrVal(s)) => {
                let cs: Vec<u32> = expr::str_copy(&s);
                match str_lit_stored(pers, st, fe) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(h.dup2()),
                    Ok(true) => match str_lit_to_constructor(pers, st, &cs) {
                        Err(e) => Err(e),
                        Ok(c) => knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &c),
                    },
                }
            }
            Some(_) => Ok(h.dup2()),
        }
    } else {
        Ok(h.dup2())
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:789-793 Expr.isStrLit
/// Lean twin: `proof/ConRon/Arena/Core.lean:2239-2247 isStrLit` — is `e` a
/// `String` literal?  (The structure rescue leaves one to the literal
/// conversion, as lean4#15351's `to_cnstr_when_structure` does.)
pub fn is_str_lit(pers: &PersTier, st: &AState, e: &EIdx) -> Result<bool, CheckError> {
    if e.tag() == ETAG_LIT {
        match view_lit(pers, st, e) {
            None => fail_dangling_e(),
            Some(Literal::StrVal(_)) => Ok(true),
            Some(_) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:795-869 prepareMajor
/// con-leche: ConLeche/Cached/CoreC.lean:932-955 prepareMajorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::prepare_major_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2249-2275 prepareMajor` — the major
/// premise's preparation before a rule fires.  At a K-flagged recursor (the
/// record's `isK`) the K
/// rescue runs on the **raw** major and, if it did not produce a constructor
/// application, the major is left as it is (con-leche task #334).  Elsewhere
/// the order of lean4#15351 (con-leche task #342 R2): the structure rescues
/// run on the major **as found** (a `String` literal skips them), and only if
/// they produce no constructor is the major head-normalized, its literal
/// converted and the rescue tried once more on the reduct — so a structure
/// major whose head normalization does not terminate is rescued off its type.
pub fn prepare_major(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    rec_name: &NIdx,
    is_k: bool,
    rules: &Vec<IRecRule>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    if is_k {
        match major_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, rec_name, is_k, rules, major) {
            Err(e) => Err(e),
            Ok(major_k) => match is_ctor_app(pers, st, fe, &major_k) {
                Err(e) => Err(e),
                Ok(true) => {
                    lit_major_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, &major_k)
                }
                Ok(false) => Ok(major_k),
            },
        }
    } else {
        let major_e: Result<EIdx, CheckError> = match is_str_lit(pers, st, major) {
            Err(e) => Err(e),
            Ok(true) => Ok(major.dup2()),
            Ok(false) => {
                major_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, rec_name, is_k, rules, major)
            }
        };
        match major_e {
            Err(e) => Err(e),
            Ok(major_e) => match is_ctor_app(pers, st, fe, &major_e) {
                Err(e) => Err(e),
                Ok(true) => Ok(major_e),
                Ok(false) => prepare_major_whnf(
                    pers, st, mode, eager, lane, fuel, fe, depth, rec_name, is_k, rules, &major_e,
                ),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:795-869 prepareMajor
/// con-leche: ConLeche/Cached/CoreC.lean:932-955 prepareMajorI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::prepare_major_whnf_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2249-2275 prepareMajor` — the
/// non-K path past a rescue that produced no constructor: head-normalize the
/// major, convert its literal, try the rescue once more on the reduct.
pub fn prepare_major_whnf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    rec_name: &NIdx,
    is_k: bool,
    rules: &Vec<IRecRule>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(major0) => match lit_major_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, &major0) {
            Err(e) => Err(e),
            Ok(major1) => {
                major_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, rec_name, is_k, rules, &major1)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:2277-2287 substLevelsAt` — the
/// nested rule's stored level comparands, substituted and re-interned
/// (`lvls.map (Level.subst lps us)` as a named recursion).
pub fn subst_levels_at(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<Name>,
    vs: &Vec<Level>,
    us: &Vec<LIdx>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= us.len() {
        Ok(out)
    } else {
        match read_level_m(pers, st, &us[i]) {
            Err(e) => Err(e),
            Ok(l) => {
                let s = level::subst(ks, vs, &l);
                match intern_level(pers, st, &s) {
                    Err(e) => Err(e),
                    Ok(h) => {
                        let mut out2 = out;
                        out2.push(h);
                        subst_levels_at(pers, st, ks, vs, us, i + 1, out2)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:2289-2299 substParamLevels` — the
/// canonical rule's level comparands, `cvjLps.map fun p => Level.subst lps us
/// (.param p)`, as a named recursion.
pub fn subst_param_levels(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<Name>,
    vs: &Vec<Level>,
    ps: &Vec<NIdx>,
    i: usize,
    out: Vec<LIdx>,
) -> Result<Vec<LIdx>, CheckError> {
    if i >= ps.len() {
        Ok(out)
    } else {
        match read_name_m(pers, st, &ps[i]) {
            Err(e) => Err(e),
            Ok(pn) => {
                let s = level::subst(ks, vs, &level::param(pn));
                match intern_level(pers, st, &s) {
                    Err(e) => Err(e),
                    Ok(h) => {
                        let mut out2 = out;
                        out2.push(h);
                        subst_param_levels(pers, st, ks, vs, ps, i + 1, out2)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:2301-2311 instSpinePins` — the
/// nested rule's stored parameter pins, level-instantiated and instantiated at
/// the recursor's leading-argument spine, as a named recursion.  `rP - 1` is
/// Lean's truncating subtraction, hence `sub_nat`.
pub fn inst_spine_pins(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    args: &Vec<EIdx>,
    r_p: u64,
    pins: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= pins.len() {
        Ok(out)
    } else {
        let p: EIdx = pins[i].dup2();
        match inst_lp_fast(pers, st, CORE_WALK_FUEL, lps, us, &p) {
            Err(e) => Err(e),
            Ok(q) => {
                let head: Vec<EIdx> = take_eidx_n(args, r_p);
                match inst_spine(pers, st, CORE_WALK_FUEL, &head, sub_nat(r_p, 1), &q) {
                    Err(e) => Err(e),
                    Ok(s) => {
                        let mut out2 = out;
                        out2.push(s);
                        inst_spine_pins(pers, st, lps, us, args, r_p, pins, i + 1, out2)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::rec_fire_levels_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2313-2336 recFireLevels` — the
/// LEVEL comparands of a firing rule (`(recFireComparands …).1`): the
/// recursor's own instantiation of the constructor's level parameters at a
/// `.plain` rule, the stored instantiation at a `.nested` or `.levels` one.  The
/// ι case split is decided at these levels.  Task #119: `recFireComparands`'
/// two halves are two functions, as the cached `iotaRecI` computes them —
/// the levels inside the case-3 block, the parameters only past its level
/// comparison.
pub fn rec_fire_levels(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    cvj_lps: &Vec<NIdx>,
) -> Result<LsIdx, CheckError> {
    match read_names_m(pers, st, lps) {
        Err(e) => Err(e),
        Ok(ks) => match read_levels_m(pers, st, us) {
            Err(e) => Err(e),
            Ok(vs) => {
                let ls = match &rl.fire {
                    IRecRuleFire::Nested(lvls, _) => {
                        let lvls2: Vec<LIdx> = env::lidx_vec_dup(lvls);
                        subst_levels_at(pers, st, &ks, &vs, &lvls2, 0, Vec::new())
                    }
                    IRecRuleFire::Plain => subst_param_levels(pers, st, &ks, &vs, cvj_lps, 0, Vec::new()),
                    IRecRuleFire::Levels(lvls) => {
                        let lvls2: Vec<LIdx> = env::lidx_vec_dup(lvls);
                        subst_levels_at(pers, st, &ks, &vs, &lvls2, 0, Vec::new())
                    }
                };
                match ls {
                    Err(e) => Err(e),
                    Ok(ls) => intern_ls_node(pers, st, ls),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:942-964 recFireComparands
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::rec_fire_args_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2338-2348 recFireArgs` — the
/// PARAMETER comparands of a firing rule (`(recFireComparands …).2`): the
/// recursor's leading `cn_p` arguments (the stored constructor's parameter
/// count) at a `.plain` or `.levels` rule, the stored pins at the recursor's
/// levels and leading arguments at a `.nested` one.
pub fn rec_fire_args(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    cn_p: u64,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    args: &Vec<EIdx>,
    r_p: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match &rl.fire {
        IRecRuleFire::Nested(_, pins) => {
            let pins2: Vec<EIdx> = env::eidx_vec_dup(pins);
            inst_spine_pins(pers, st, lps, us, args, r_p, &pins2, 0, Vec::new())
        }
        IRecRuleFire::Plain => Ok(take_eidx_n(args, cn_p)),
        IRecRuleFire::Levels(_) => Ok(take_eidx_n(args, cn_p)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::find_rule_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2350-2355 findRule` — the rule
/// lookup `rules.find? (fun r' => r'.ctor == cj)`, as a named recursion
/// (DESIGN.md §3.4).  The index is returned rather than the rule, so that the
/// caller reads the record out of the `Vec` it is stored in.
pub fn find_rule(rules: &Vec<IRecRule>, c: &NIdx, i: usize) -> Option<usize> {
    if i >= rules.len() {
        None
    } else if rules[i].ctor.eq2(c) {
        Some(i)
    } else {
        find_rule(rules, c, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_fire_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_fire_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — a matched
/// rule fires: **the ι case split** (con-leche task #342 L10, S5c) decides
/// whether the constructor application is checked at all (`iota_rec_cert`, ONE
/// certificate family, off at the trusted mode), then the reduct.
pub fn iota_rec_fire(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    is_k: bool,
    cvj: &IConstantVal,
    cn_p: u64,
    rl: &IRecRule,
    rec_c: &NIdx,
    us: &LsIdx,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    match iota_rec_cert(
        pers, st, mode, eager, lane, fuel, fe, depth, cv, is_k, cvj, cn_p, rl, us, usj, m_i, r_p,
        args, margs,
    ) {
        Err(e) => Err(e),
        Ok(false) => Ok(None),
        Ok(true) => iota_rec_reduct(pers, st, cv, cn_p, rl, rec_c, us, r_p, args, margs),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_cert_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_cert_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:84-87 certAtI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — **the
/// whole case-3 decision, one certificate family** (`certAtI mode (…)`):
/// at the trusted mode `true` without running; at the verified mode the
/// level comparands are computed and, at a case-3 redex (`iotaCase3At`: not K,
/// the constructor's family may be `Prop` at the comparand levels), the
/// constructor application is checked (`iota_rec_case3`).  Cases 1 and 2 fire
/// with no check, as official's `inductive_reduce_rec`.
pub fn iota_rec_cert(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    is_k: bool,
    cvj: &IConstantVal,
    cn_p: u64,
    rl: &IRecRule,
    us: &LsIdx,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if !verified_checks(mode) {
        Ok(true)
    } else {
        match rec_fire_levels(pers, st, rl, &cv.level_params, us, &cvj.level_params) {
            Err(e) => Err(e),
            Ok(cmp_lvls) => {
                match iota_case3_at(pers, st, mode, eager, lane, fuel, fe, is_k, cvj, &cmp_lvls) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(true),
                    Ok(true) => iota_rec_case3(
                        pers, st, mode, eager, lane, fuel, fe, depth, cv, cvj, cn_p, rl, us, usj,
                        &cmp_lvls, m_i, r_p, args, margs,
                    ),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_case3_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_case3_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — a case-3
/// redex's checks: the constructor's levels against the comparand levels,
/// its parameters against the parameter comparands, then the telescope and
/// index certificates (`iota_rec_fam`).
pub fn iota_rec_case3(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    cvj: &IConstantVal,
    cn_p: u64,
    rl: &IRecRule,
    us: &LsIdx,
    usj: &LsIdx,
    cmp_lvls: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match lvls_eq(pers, st, usj, cmp_lvls) {
        Err(e) => Err(e),
        Ok(o) => match lift_fueled(o) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match rec_fire_args(pers, st, rl, cn_p, &cv.level_params, us, args, r_p) {
                Err(e) => Err(e),
                Ok(cmp_args) => {
                    let head: Vec<EIdx> = take_eidx_n(margs, cn_p);
                    match def_eq_list(pers, st, mode, eager, lane, fuel, fe, depth, &head, &cmp_args, 0) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => iota_rec_fam(
                            pers, st, mode, eager, lane, fuel, fe, depth, cvj, cn_p, usj, m_i, r_p,
                            args, margs,
                        ),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_fam_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_fam_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — the
/// constructor telescope at the FULL grade (`iotaCertsFull`) and the
/// canonical-index comparison (`iotaIndexOk`).  The constructor's type is
/// looked up only here, where the certificates consume it.  (Task #119: the
/// recursor's own telescope run is gone — con-leche task #349 — and so is the
/// ι-slot licence.)
pub fn iota_rec_fam(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match const_ty_at(pers, st, cvj, usj) {
        Err(e) => Err(e),
        Ok(ty_c) => match iota_certs_full(pers, st, mode, eager, lane, fuel, fe, depth, &ty_c, margs, 0) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => {
                let idx: Vec<EIdx> = drop_eidx_n(&take_eidx_n(args, m_i), r_p);
                iota_index_ok(
                    pers, st, mode, eager, lane, fuel, fe, depth, m_i, r_p, cn_p, &ty_c,
                    margs, &idx,
                )
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_reduct_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_reduct_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — the ι
/// reduct: the rule's right-hand side at the recursor's levels, applied to the
/// recursor's leading arguments and the constructor's fields.
pub fn iota_rec_reduct(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    cn_p: u64,
    rl: &IRecRule,
    rec_c: &NIdx,
    us: &LsIdx,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    match rule_rhs_at(pers, st, rec_c, &rl.ctor, &cv.level_params, &rl.rhs, us) {
        Err(e) => Err(e),
        Ok(rhs) => {
            let tail: Vec<EIdx> = drop_eidx_n(margs, cn_p);
            let spine: Vec<EIdx> = append_eidx(take_eidx_n(args, r_p), &tail);
            match mk_app_n(pers, st, &rhs, &spine) {
                Err(e) => Err(e),
                Ok(x) => Ok(Some(x)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_major_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_major_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — the
/// major's side of the step: it is a fully applied constructor with a
/// matching rule.  The parameter count is the stored constructor's, the field
/// count the rule's.  (Task #119: the inert-rule decline is gone with
/// `RecRuleFire.inert`.)
pub fn iota_rec_major(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    is_k: bool,
    rules: &Vec<IRecRule>,
    rec_c: &NIdx,
    us: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    major: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, major) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const(pers, st, &hd) {
                None => fail_dangling_e(),
                Some((cj, usj)) => match env::ifenv_find(pers, fe, &cj) {
                    Some(IConstantInfo::CtorInfo(cvj0, cn_p0, _)) => {
                        let cvj: IConstantVal = env::i_constant_val_dup(cvj0);
                        let cn_p: u64 = *cn_p0;
                        match find_rule(rules, &cj, 0) {
                            None => Ok(None),
                            Some(k) => {
                                let rl: IRecRule = env::i_rec_rule_dup(&rules[k]);
                                match get_app_args(pers, st, CORE_WALK_FUEL, major) {
                                    Err(e) => Err(e),
                                    Ok(margs) => {
                                        if margs.len() as u64 != cn_p + rl.nfields {
                                            Ok(None)
                                        } else {
                                            iota_rec_fire(
                                                pers, st, mode, eager, lane, fuel, fe, depth, cv,
                                                is_k, &cvj, cn_p, &rl, rec_c, us, &usj, m_i, r_p,
                                                args, &margs,
                                            )
                                        }
                                    }
                                }
                            }
                        }
                    }
                    Some(_) => Ok(None),
                    None => Ok(None),
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:871-970 iotaRec
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_at_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:957-1042 iotaRecI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::iota_rec_at_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2444 iotaRecAt` — `iotaRec` with
/// its two spine walks HOISTED: the head and the argument vector are the
/// caller's, and `n` says how many of `sargs` the expression `e` applies.
///
/// `whnf_app` (task #97-P6-9) has both already — it walked the spine once —
/// and the spec-shaped body it replaces called `iotaRec` on every prefix of
/// the spine, so `getAppFn`+`getAppArgs` were walked once per argument: a
/// quadratic that neither checker's shape needs.  The arity test moves in
/// front of the level-list read for the same reason (both are pure tests of
/// the same conjunction, and the arity one is O(1) here).  The third
/// conjunct (con-leche task #342 L18) is the recursor's stored type's
/// syntactic arity, which the uncertified recursor spine is read against.
pub fn iota_rec_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    hd: &EIdx,
    sargs: &Vec<EIdx>,
    n: usize,
) -> Result<Option<EIdx>, CheckError> {
    if hd.tag() == ETAG_CONST {
        match view_const(pers, st, hd) {
            None => fail_dangling_e(),
            Some((c, us)) => match env::ifenv_find(pers, fe, &c) {
                Some(IConstantInfo::RecInfo(cv0, m_i0, r_p0, is_k0, rules0)) => {
                    let m_i: u64 = *m_i0;
                    // **The arity test hoisted over the copies** (task
                    // #97-P6-10): `whnf_app` asks `iota_rec_at` at every
                    // reduction step and the answer is `none` at the wrong
                    // arity, so copying the recursor's `IConstantVal` and its
                    // whole rule vector first is work for a branch that reads
                    // neither.
                    if n as u64 != m_i + 1 {
                        Ok(None)
                    } else {
                        let cv: IConstantVal = env::i_constant_val_dup(cv0);
                        let r_p: u64 = *r_p0;
                        let is_k: bool = *is_k0;
                        let rules: Vec<IRecRule> = env::i_rec_rules_dup(rules0);
                        let args: Vec<EIdx> = take_eidx(sargs, n);
                        match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => match peel_pis(pers, st, m_i + 1, &cv.ty) {
                                Err(er) => Err(er),
                                Ok(peeled) => {
                                    if args.len() as u64 == m_i + 1
                                        && usl == cv.level_params.len()
                                        && peeled.is_some()
                                    {
                                        match intern_e_bvar(pers, st, 0) {
                                            Err(er) => Err(er),
                                            Ok(b0) => {
                                                let maj0: EIdx = get_d_eidx(&args, m_i, &b0);
                                                match prepare_major(
                                                    pers, st, mode, eager, lane, fuel, fe, depth, &c,
                                                    is_k, &rules, &maj0,
                                                ) {
                                                    Err(er) => Err(er),
                                                    Ok(major) => iota_rec_major(
                                                        pers, st, mode, eager, lane, fuel, fe, depth,
                                                        &cv, is_k, &rules, &c, &us, m_i, r_p, &args,
                                                        &major,
                                                    ),
                                                }
                                            }
                                        }
                                    } else {
                                        Ok(None)
                                    }
                                }
                            },
                        }
                    }
                }
                Some(_) => Ok(None),
                None => Ok(None),
            },
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// The projection certificate and the reduction bodies (`Core.lean:1939-2087`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:992-1001 ProjEntry.typeAt
/// Lean twin: `proof/ConRon/Arena/Core.lean:2611-2622 IProjEntry.typeAt` —
/// **the type of a `.proj` node at a tower-backed entry**: the stored body,
/// level-instantiated at the subject type's levels, with the subject type's
/// arguments and the subject substituted for its `numParams + 1` loose
/// variables in ONE traversal.
pub fn proj_entry_type_at(
    pers: &PersTier,
    st: &mut AState,
    entry: &IProjEntry,
    us: &LsIdx,
    targs: &Vec<EIdx>,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match inst_lp_fast(pers, st, CORE_WALK_FUEL, &entry.level_params, us, &entry.body) {
        Err(e) => Err(e),
        Ok(b) => {
            // `instantiate_list`'s vector is in PUSH order (task #97-P6-15),
            // and the twin's list here is `pe :: targs.reverse` — so the
            // vector is `targs ++ [pe]`, which is one sized `push` where the
            // reverse-then-cons was two copies of the whole argument vector.
            let vs: Vec<EIdx> = snoc_eidx_of(targs, pe);
            instantiate_list_fast(pers, st, CORE_WALK_FUEL, &b, &vs, 0)
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:785-793 teleArityOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:2624-2629 teleArityOk` — **the
/// telescope check of a spine** (con-leche task #342 L18): the telescope's
/// syntactic arity, nothing else.
pub fn tele_arity_ok(pers: &PersTier, st: &AState, ty: &EIdx, args: &Vec<EIdx>) -> Result<bool, CheckError> {
    match peel_pis(pers, st, args.len() as u64, ty) {
        Err(e) => Err(e),
        Ok(r) => Ok(r.is_some()),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:972-984 projCert
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::proj_cert_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:199-203 projCertF
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::proj_cert_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2631-2638 projCert` — **the
/// structural projection's check** (con-leche task #175 W6, #342 L18): the
/// redex `proj_i (C p⃗ x⃗)` fires only where `C`'s stored type has the spine's
/// arity (`teleArityOk`; level instantiation keeps the arity, so the stored
/// type is read uninstantiated).  Task #119: was a telescope certificate run.
pub fn proj_cert(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
    args: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match env::ifenv_find(pers, fe, c) {
        Some(IConstantInfo::CtorInfo(cvc0, _, _)) => {
            let ty: EIdx = cvc0.ty.dup2();
            tele_arity_ok(pers, st, &ty, args)
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:986-993 projCertAt
/// con-leche: ConLeche/Cached/CoreC.lean:205-208 projCertAtF
/// Lean twin: `proof/ConRon/Arena/Core.lean:2640-2646 projCertAt` — **the fire
/// check as the mode runs it**: the verified core checks the constructor
/// telescope's arity; the trusted core is the official kernel's, which checks
/// nothing.
pub fn proj_cert_at(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    verified: bool,
    c: &NIdx,
    args: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if verified {
        proj_cert(pers, st, fe, c, args)
    } else {
        Ok(true)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:995-1023 reduceProjCore
/// con-leche: ConLeche/Cached/CoreC.lean:1044-1067 reduceProjCoreI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2648-2681 reduceProjCore` — **the
/// projection rule on a reduced scrutinee** (the official kernel's
/// `reduce_proj_core`): the scrutinee's string-literal expansion, then the
/// table entry.  `None` when the rule does not fire.  Callers: the `.proj`
/// clause of `whnfCoreBody` (`whnf_core_proj`) and `lazy_delta_proj_reduction`.
pub fn reduce_proj_core(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    c: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match proj_lit_to_ctor(pers, st, mode, eager, lane, fuel, fe, depth, c) {
        Err(e) => Err(e),
        Ok(ep) => match env::ifenv_find_proj(pers, fe, sn, i) {
            Some(entry) => reduce_proj_core_at(pers, st, mode, fe, i, &ep, &entry),
            None => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:995-1023 reduceProjCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2648-2681 reduceProjCore` — the
/// projection rule at a tower entry: the scrutinee's head must be the entry's
/// constructor at the right arities; the rule fires unguarded.
pub fn reduce_proj_core_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    i: u64,
    ep: &EIdx,
    entry: &IProjEntry,
) -> Result<Option<EIdx>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, ep) {
        Err(e) => Err(e),
        Ok(hd) => if hd.tag() == ETAG_CONST {
            match view_const(pers, st, &hd) {
                None => fail_dangling_e(),
                Some((c, us)) => match get_app_args(pers, st, CORE_WALK_FUEL, ep) {
                    Err(e) => Err(e),
                    Ok(args) => match view_ls_len(pers, st, &us) {
                        None => fail_dangling_ls(),
                        Some(usl) => {
                            if c.eq2(&entry.ctor)
                                && i < entry.num_fields
                                && args.len() as u64 == entry.num_params + entry.num_fields
                                && usl == entry.level_params.len()
                            {
                                reduce_proj_core_fire(pers, st, mode, fe, i, entry, &c, &args)
                            } else {
                                Ok(None)
                            }
                        }
                    },
                },
            }
        } else {
            Ok(None)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:995-1023 reduceProjCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2648-2681 reduceProjCore` — the
/// fire itself: the selected field, behind the mode's certificate.
pub fn reduce_proj_core_fire(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    i: u64,
    entry: &IProjEntry,
    c: &NIdx,
    args: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    match intern_e_bvar(pers, st, 0) {
        Err(e) => Err(e),
        Ok(b0) => {
            let arg: EIdx = get_d_eidx(args, entry.num_params + i, &b0);
            let verified: bool = verified_checks(mode);
            match proj_cert_at(pers, st, fe, verified, c, args) {
                Err(e) => Err(e),
                Ok(true) => Ok(Some(arg)),
                Ok(false) => Ok(None),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1094-1103 WhnfStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2522-2530 WhnfStep` — the outcome
/// of one step of the head-normalization loop: the head normal form, or the
/// term the loop continues with (con-leche task #342 R2).  A step RETURNS its
/// continuation instead of calling it, so every reduction step is the loop's
/// own iteration and a chain of any length — a non-terminating one included —
/// runs in constant native stack.
pub enum WhnfStep {
    Done(EIdx),
    Cont(EIdx),
}

/// con-leche: ConLeche/Kernel/Core.lean:1076-1092 whnfCoreLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2532-2537 whnfCoreLoopFuel` — step
/// budget of the head-normalization loop: `2^62`, con-leche's value (task
/// #330); exhaustion is an internal error, never a verdict, and a runaway
/// input is left to the external timeout.
pub const WHNF_CORE_LOOP_FUEL: u64 = 4611686018427387904; // 2^62

/// con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
/// con-leche: ConLeche/Cached/CoreC.lean:1140-1181 whnfCoreStepI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_core_step_proj_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2683-2694 whnfCoreStepProj`
/// The `.proj` clause of the step: the scrutinee by `whnf`, or — in the CHEAP
/// mode (official `cheap_proj`) — by the cheap `whnfCore`, then the
/// projection rule (`reduce_proj_core`): a fired field is the term the loop
/// continues with.
///
/// **A stuck projection is its own input `e`** (con-leche's task #323,
/// KEEPPROJ; official `whnf_core`: `reduce_proj` fails and `r = e`): the
/// scrutinee's reduct is computed to try the rule and then dropped, so no
/// node is interned.
pub fn whnf_core_step_proj(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cheap: bool,
    depth: u64,
    e: &EIdx,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<WhnfStep, CheckError> {
    let rc = if cheap {
        knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, pe)
    } else {
        knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, pe)
    };
    match rc {
        Err(er) => Err(er),
        Ok(c) => match reduce_proj_core(pers, st, mode, eager, lane, fuel, fe, depth, sn, i, &c) {
            Err(er) => Err(er),
            Ok(Some(m)) => Ok(WhnfStep::Cont(m)),
            Ok(None) => Ok(WhnfStep::Done(e.dup2())),
        },
    }
}

/// con-leche: none — `getAppFn` and `getAppArgsC` in one descent, plus the
/// spine's own application NODES (the arena's upward cutoff needs them)
/// Lean twin: `proof/ConRon/Arena/Core.lean:2472-2475 getAppSpine` —
/// `Expr.getAppFn e`, `Expr.getAppArgsC e` and the list of prefixes `e` is
/// built from.
///
/// The three results of one walk down an application spine: the head, the
/// arguments outermost-last (`get_app_args`'s order), and `nodes`, where
/// `nodes[i]` is the ORIGINAL application node that applies `args[i]` to the
/// prefix before it.  `nodes` is what keeps task #97-P6-5's upward cutoff
/// (`intern_app_rebuilt`) alive in the batched loop: the spec-shaped body got
/// the original node for free from its own recursion, and a loop does not.
pub fn get_app_spine(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<(EIdx, Vec<EIdx>, Vec<EIdx>), CheckError> {
    get_app_spine_go(pers, st, fuel, h, 0)
}

/// con-leche: none — `getAppFn`/`getAppArgsC` in one descent (see
/// `get_app_spine`)
/// Lean twin: `proof/ConRon/Arena/Core.lean:2456-2470 getAppSpineGo` — the
/// cursor recursion behind `get_app_spine`.
///
/// `k` counts the arguments seen on the way DOWN and is spent at the head, as
/// the two vectors' capacity: `whnf_core` meets an application spine on every
/// reduction step, and a `Vec` grown from empty reallocates ⌈log₂ n⌉ times per
/// spine.  A capacity is a representation difference the refinement absorbs
/// (DESIGN §8.6's twin-ledger rule), so this costs the twin nothing.
pub fn get_app_spine_go(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
    k: usize,
) -> Result<(EIdx, Vec<EIdx>, Vec<EIdx>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF_SPINE)))
    } else if h.tag() == ETAG_APP {
        match view_app(pers, st, h) {
            None => fail_dangling_e(),
            Some(p) => {
                let f: EIdx = p.0;
                let a: EIdx = p.1;
                match get_app_spine_go(pers, st, fuel - 1, &f, k + 1) {
                    Err(e) => Err(e),
                    Ok(t) => {
                        let hd: EIdx = t.0;
                        let mut args: Vec<EIdx> = t.1;
                        let mut nodes: Vec<EIdx> = t.2;
                        args.push(a);
                        nodes.push(h.dup2());
                        Ok((hd, args, nodes))
                    }
                }
            }
        }
    } else {
        Ok((h.dup2(), Vec::with_capacity(k), Vec::with_capacity(k)))
    }
}

/// con-leche: none — `getAppFn e` and `getAppArgsC e` in one place
/// Lean twin: `proof/ConRon/Arena/Core.lean:2477-2485 headAndArgs` — the head
/// and the argument vector of a term, as `whnf_app` needs them for its ι step.
///
/// `whnf_app` carries the head and the arguments of the application it has
/// accumulated so that `iota_rec_at` is O(1) per argument; when a reduction
/// replaces that application wholesale, the two have to be read off the new
/// term, which is what this does.  The handle's own tag makes the common
/// case — the reduct is not an application — one comparison and no walk.
pub fn head_and_args(
    pers: &PersTier,
    st: &AState,
    v: &EIdx,
) -> Result<(EIdx, Vec<EIdx>), CheckError> {
    if v.tag() == ETAG_APP {
        match get_app_fn(pers, st, CORE_WALK_FUEL, v) {
            Err(e) => Err(e),
            Ok(hd) => match get_app_args(pers, st, CORE_WALK_FUEL, v) {
                Err(e) => Err(e),
                Ok(va) => Ok((hd, va)),
            },
        }
    } else {
        Ok((v.dup2(), Vec::new()))
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1092-1120 whnfAppI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_app_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2574-2605 whnfApp` — the cached
/// tier's bulk-β argument loop, the EXECUTED checker's own `.app` step.
///
/// **The batched instantiation lever** (task #97-P6-9).  The loop consumes
/// the spine against the whnf'd head `v` and hands a consecutive run of λ
/// binders to `beta_peel`, which substitutes the accumulated argument vector
/// in ONE `instantiate_list` walk (con-leche's `ConLeche/Verify/BetaSpine.lean`
/// identifies the two).  β is uniform (con-leche task #342 S0: no certificate,
/// no gate).  **It returns a `WhnfStep`** (task #342 R2): the stuck spine is
/// `Done`, and a fired ι hands the loop its reduct applied to the rest of the
/// spine (`Cont`) — the loop, not a nested call, continues with it.
///
/// Three things travel with `v`, all bookkeeping:
///   * `same` — `v` still IS the function part of `nodes[i]`, which is task
///     #97-P6-5's upward cutoff (`intern_app_rebuilt`);
///   * `hd` and `vargs` — `v = mkAppN hd vargs`, so that the ι step is
///     `iota_rec_at` and not a fresh `getAppFn`/`getAppArgs` walk per argument;
///   * `i` — the cursor into `args`, which is the twin's list pattern.
pub fn whnf_app(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    v: &EIdx,
    hd: &EIdx,
    vargs: Vec<EIdx>,
    same: bool,
    args: &Vec<EIdx>,
    nodes: &Vec<EIdx>,
    i: usize,
) -> Result<WhnfStep, CheckError> {
    if i >= args.len() {
        Ok(WhnfStep::Done(v.dup2()))
    } else {
        let a: EIdx = args[i].dup2();
        let node: EIdx = nodes[i].dup2();
        if v.tag() == ETAG_LAM {
            match view_bind(pers, st, v) {
                None => fail_dangling_e(),
                Some((_, body)) => {
                    let mut acc: Vec<EIdx> = Vec::new();
                    acc.push(a);
                    beta_peel(pers, st, &body, acc, args, i + 1)
                }
            }
        } else {
            match intern_app_rebuilt(pers, st, &node, same, v, &a) {
                Err(e) => Err(e),
                Ok(ap) => {
                    let same2: bool = ap.eq2(&node);
                    let mut va: Vec<EIdx> = vargs;
                    va.push(a);
                    let n: usize = va.len();
                    let step = if hd.tag() == ETAG_CONST {
                        iota_rec_at(pers, st, mode, eager, lane, fuel, fe, depth, hd, &va, n)
                    } else {
                        // `iotaArityOk`'s `.const` match, off the handle's tag.
                        Ok(None)
                    };
                    match step {
                        Err(e) => Err(e),
                        Ok(None) => whnf_app(
                            pers, st, mode, eager, lane, fuel, fe, depth, &ap, hd, va, same2, args,
                            nodes, i + 1,
                        ),
                        Ok(Some(e2)) => match mk_app_n_from(pers, st, &e2, args, i + 1) {
                            Err(e) => Err(e),
                            Ok(e3) => Ok(WhnfStep::Cont(e3)),
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1069-1090 betaPeelI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::beta_peel_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2553-2572 betaPeel` — the peel loop
/// of `whnf_app`.
///
/// `t` is the RAW (unsubstituted) λ body after the binders consumed so far and
/// `acc` their arguments — the list `instantiate_list` takes at cursor `0`,
/// built in PUSH order on an OWNED vector (task #97-P6-15).  The body is
/// substituted once, when peeling stops, and handed to the loop (`Cont`)
/// together with the arguments left over.
pub fn beta_peel(
    pers: &PersTier,
    st: &mut AState,
    t: &EIdx,
    acc: Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<WhnfStep, CheckError> {
    if i >= args.len() {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, &acc, 0) {
            Err(e) => Err(e),
            Ok(e2) => Ok(WhnfStep::Cont(e2)),
        }
    } else if t.tag() == ETAG_LAM {
        match view_bind(pers, st, t) {
            None => fail_dangling_e(),
            Some((_, body)) => {
                let mut acc2: Vec<EIdx> = acc;
                acc2.push(args[i].dup2());
                beta_peel(pers, st, &body, acc2, args, i + 1)
            }
        }
    } else {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, &acc, 0) {
            Err(e) => Err(e),
            Ok(e2) => match mk_app_n_from(pers, st, &e2, args, i) {
                Err(e) => Err(e),
                Ok(e3) => Ok(WhnfStep::Cont(e3)),
            },
        }
    }
}

/// con-leche: none — `internE (.app f' a)`, the twin's one-line rebuild
/// Lean twin: `proof/ConRon/Arena/Core.lean:2738-2746 whnfCoreBody` — the stuck
/// application, re-interned.  Its own function because both the plain and the
/// gated β arm end in it.
pub fn intern_app(
    pers: &PersTier,
    st: &mut AState,
    f: &EIdx,
    a: &EIdx,
) -> Result<EIdx, CheckError>  {
    intern_e_app(pers, st, f.dup2(), a.dup2())
}

/// con-leche: none — `internE (.app f' a)`, the twin's one-line rebuild
/// Lean twin: `proof/ConRon/Arena/Core.lean:2450-2454 internAppRebuilt` — **the
/// UPWARD cutoff at the stuck application**, `expr_ops::intern_rebuilt`'s
/// clause where task #97-P6-5's lever 2 could not reach.
///
/// `whnfCore` of an application head-normalizes the function and re-interns
/// `.app f' a`.  When `f'` IS `f` — the head was already in normal form — the
/// node it re-interns is the node it started from, so the whole hash, cons
/// probe and (at Mathlib scale) guaranteed cache miss buy back a handle the
/// caller already holds.  On the Mathlib 25 % prefix **58.2 M of `whnfCore`'s
/// application and projection misses answer with their own argument**.
///
/// Handle-identical for the same reason task #97-P6-5 gives: the store is
/// hash-consed, `denoteE` is injective, and §8.3's cross-tier probe order
/// makes `intern` of a node's own view that node and not a twin of it in the
/// other tier.
pub fn intern_app_rebuilt(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    f: &EIdx,
    a: &EIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_app(pers, st, f, a)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
/// con-leche: ConLeche/Cached/CoreC.lean:1140-1181 whnfCoreStepI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_core_step_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2696-2723 whnfCoreStep` — one
/// head-normalization step (β, ι, projection, ζ — **no δ**), returning the head
/// normal form or the term to continue with.  Only the spine head's
/// normalization stays a knot call (genuine nesting, bounded by the term's
/// depth); every *reduction* step is the loop's iteration.  Values return
/// themselves, which over handles is the handle itself.
pub fn whnf_core_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cheap: bool,
    depth: u64,
    e: &EIdx,
) -> Result<WhnfStep, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Sort(_)) => Ok(WhnfStep::Done(e.dup2())),
        Ok(ENodeView::FVar(_, _)) => Ok(WhnfStep::Done(e.dup2())),
        Ok(ENodeView::ForallE(_, _)) => Ok(WhnfStep::Done(e.dup2())),
        Ok(ENodeView::Lam(_, _)) => Ok(WhnfStep::Done(e.dup2())),
        Ok(ENodeView::Const(_, _)) => Ok(WhnfStep::Done(e.dup2())),
        Ok(ENodeView::Lit(_)) => Ok(WhnfStep::Done(e.dup2())),
        // **The batched β spine** (task #97-P6-9): the spine's head is
        // normalized once and the whole argument vector is run through
        // `whnf_app`.
        Ok(ENodeView::App(_, _)) => match get_app_spine(pers, st, CORE_WALK_FUEL, e) {
            Err(er) => Err(er),
            Ok(sp) => {
                let hd: EIdx = sp.0;
                let args: Vec<EIdx> = sp.1;
                let nodes: Vec<EIdx> = sp.2;
                match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, cheap, depth, &hd) {
                    Err(er) => Err(er),
                    Ok(v) => {
                        let same: bool = v.eq2(&hd);
                        match head_and_args(pers, st, &v) {
                            Err(er) => Err(er),
                            Ok(hv) => whnf_app(
                                pers, st, mode, eager, lane, fuel, fe, depth, &v, &hv.0, hv.1, same,
                                &args, &nodes, 0,
                            ),
                        }
                    }
                }
            }
        },
        Ok(ENodeView::Proj(sn, i, pe)) => {
            whnf_core_step_proj(pers, st, mode, eager, lane, fuel, fe, cheap, depth, e, &sn, i, &pe)
        }
        // ζ, Lean's way (con-leche task #342 S0): lets are stored as Lean
        // stores them, and the reduct is the loop's next term.
        Ok(ENodeView::LetE(_, v, b)) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &v, 0) {
            Err(er) => Err(er),
            Ok(e2) => Ok(WhnfStep::Cont(e2)),
        },
        Ok(ENodeView::BVar(_)) => fail(CheckError::NotImplemented(code_points(&M_BVAR_WHNF))),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1183-1229 whnfCoreLoopI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_core_loop_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2725-2736 whnfCoreLoop` — iterate
/// `whnf_core_step` on its own step budget.  **A real loop** (task #119,
/// after con-leche task #342 R2): con-leche's self tail call compiles to a
/// jump, and Rust promises no tail calls, so the iteration is spelled as one —
/// a reduction chain of any length runs in constant native stack, and a
/// non-terminating one runs until the external timeout.  Extraction's
/// `-loops-to-rec` turns it back into the twin's recursion.
pub fn whnf_core_loop(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cheap: bool,
    depth: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    let mut k: u64 = n;
    let mut cur: EIdx = e.dup2();
    loop { // lint: allow (task #119: constant native stack, DESIGN.md §3.4)
        if k == 0 {
            return fail(CheckError::Internal(code_points(&M_FUEL_WHNF_CORE_LOOP)));
        }
        match whnf_core_step(pers, st, mode, eager, lane, fuel, fe, cheap, depth, &cur) {
            Err(er) => return Err(er),
            Ok(WhnfStep::Done(v)) => return Ok(v),
            Ok(WhnfStep::Cont(e2)) => {
                cur = e2;
                k = k - 1;
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
/// con-leche: ConLeche/Cached/CoreC.lean:1231-1235 whnfCoreBodyI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_core_body_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2738-2746 whnfCoreBody` — the
/// head-normalization body: the loop at its own step budget.
pub fn whnf_core_body(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cheap: bool,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    whnf_core_loop(pers, st, mode, eager, lane, fuel, fe, cheap, depth, WHNF_CORE_LOOP_FUEL, e)
}

/// con-leche: ConLeche/Kernel/Core.lean:1105-1116 whnfLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2748-2754 whnfLoopFuel` — step budget of
/// the `whnf` reduction loop.  Literal-acceleration and delta steps are
/// *iteration*, not recursion.  Effectively unbounded since con-leche task
/// #330: `2^62`, con-leche's value (exhaustion is an internal error, never an
/// accept; a runaway input is left to an external timeout).
pub const WHNF_LOOP_FUEL: u64 = 4611686018427387904; // 2^62

/// con-leche: ConLeche/Kernel/Core.lean:1123-1143 whnfStep
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_step_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:1004-1018 whnfStepI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_step_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2756-2771 whnfStep` — one iteration
/// of the reduction loop: head-normalize, try literal acceleration, unfold one
/// definition.  **The continuation is returned, not called** (task #119): the
/// cited `k e'` is `Cont(e')`, and `whnf_loop` — a real loop — continues with
/// it.  con-leche makes the same move by inlining the step into the loop so
/// that its continuation call is the loop's own tail call (task #342 R2); a
/// Rust tail call is not a jump, so the port returns the step, as
/// `whnf_core_step` does.
pub fn whnf_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<WhnfStep, CheckError> {
    match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, false, depth, e) {
        Err(er) => Err(er),
        Ok(e1) => match reduce_nat(pers, st, mode, eager, lane, fuel, fe, depth, &e1) {
            Err(er) => Err(er),
            Ok(Some(e2)) => Ok(WhnfStep::Cont(e2)),
            Ok(None) => match unfold_definition(pers, st, fe, &e1) {
                Err(er) => Err(er),
                Ok(Some(e2)) => Ok(WhnfStep::Cont(e2)),
                Ok(None) => Ok(WhnfStep::Done(e1)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1145-1150 whnfLoop
/// con-leche: ConLeche/Cached/CoreC.lean:1297-1316 whnfLoopI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::whnf_loop_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:2773-2782 whnfLoop` — the reduction
/// loop: iterate `whnf_step` on its own step budget, so the whole chain costs
/// one knot level however many steps it takes.  **A real loop** (task #119),
/// for `whnf_core_loop`'s reason: a δ chain of any length runs in constant
/// native stack (con-leche fixture `whnf_delta_loop`).
pub fn whnf_loop(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    let mut k: u64 = n;
    let mut cur: EIdx = e.dup2();
    loop { // lint: allow (task #119: constant native stack, DESIGN.md §3.4)
        if k == 0 {
            return fail(CheckError::Internal(code_points(&M_FUEL_WHNF_LOOP)));
        }
        match whnf_step(pers, st, mode, eager, lane, fuel, fe, depth, &cur) {
            Err(er) => return Err(er),
            Ok(WhnfStep::Done(v)) => return Ok(v),
            Ok(WhnfStep::Cont(e2)) => {
                cur = e2;
                k = k - 1;
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1152-1154 whnfBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2784-2787 whnfBody` — the reduction
/// loop's body: run `whnfLoop` at its own step budget.
pub fn whnf_body(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    whnf_loop(pers, st, mode, eager, lane, fuel, fe, depth, WHNF_LOOP_FUEL, e)
}

/// con-leche: ConLeche/Kernel/Core.lean:1156-1162 ensureSort
/// Lean twin: `proof/ConRon/Arena/Core.lean:2789-2798 ensureSort` — ensure `e`
/// (the type of some expression) is a sort, returning its level.
pub fn ensure_sort(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<LIdx, CheckError> {
    match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, e) {
        Err(er) => Err(er),
        Ok(w) => if w.tag() == ETAG_SORT {
            match view_sort(pers, st, &w) {
                None => fail_dangling_e(),
                Some(u) => Ok(u),
            }
        } else {
            fail(CheckError::Invalid(code_points(&M_SORT)))
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1164-1178 checkGuardRows
/// con-leche: ConLeche/Cached/CoreC.lean:1331-1344 checkGuardRowsI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2800-2822 checkGuardRows` — **the rows of a
/// projection's guard** (official `infer_proj`'s `is_prop` tests): each row's
/// term, inferred at the io grade at its own depth and head-normalized, has a
/// sort that is zero wherever `guard_sort` is (`Level.zeroWhereZero`, on the
/// levels read back).  The list recursion is an index recursion here.
pub fn check_guard_rows(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    guard_sort: &Level,
    rows: &Vec<(u64, EIdx)>,
    i: usize,
) -> Result<(), CheckError> {
    if i >= rows.len() {
        Ok(())
    } else {
        let d: u64 = rows[i].0;
        let dom: EIdx = rows[i].1.dup2();
        match knot_infer_io(pers, st, mode, eager, lane, fuel, fe, d, &dom) {
            Err(e) => Err(e),
            Ok(t) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, d, &t) {
                Err(e) => Err(e),
                Ok(w) => if w.tag() == ETAG_SORT {
                    match view_sort(pers, st, &w) {
                        None => fail_dangling_e(),
                        Some(u) => match read_level_m(pers, st, &u) {
                            Err(e) => Err(e),
                            Ok(ul) => {
                                if level::zero_where_zero(guard_sort, &ul) {
                                    check_guard_rows(pers, st, mode, eager, lane, fuel, fe, guard_sort, rows, i + 1)
                                } else {
                                    fail(CheckError::Invalid(code_points(&M_PROP)))
                                }
                            }
                        },
                    }
                } else {
                    fail(CheckError::Invalid(code_points(&M_SORT)))
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1180-1196 projGuardSort
/// con-leche: ConLeche/Cached/CoreC.lean:1346-1357 projGuardSortI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2824-2844 projGuardSort` — **the sort a
/// projection's rows answer to**, at this use: `none` where the guard has
/// nothing to ask.  A stored type that ends in a sort answers at once (`Prop`
/// asks for propositions, any other sort nothing); otherwise the sort is
/// walked to at the use's levels (`former_sort_loop`): never zero asks
/// nothing, a sort that may be zero is the guard sort, and no sort at all is a
/// reject.  The level is read back (deviation 4).
pub fn proj_guard_sort(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    us: &LsIdx,
) -> Result<Option<Level>, CheckError> {
    match former_res_sort(pers, st, &cvt.ty) {
        Err(e) => Err(e),
        Ok(Some(s)) => match read_level_m(pers, st, &s) {
            Err(e) => Err(e),
            Ok(sl) => {
                if level::is_always_zero(&sl) {
                    Ok(Some(level::zero()))
                } else {
                    Ok(None)
                }
            }
        },
        Ok(None) => match inst_lp_fast(pers, st, CORE_WALK_FUEL, &cvt.level_params, us, &cvt.ty) {
            Err(e) => Err(e),
            Ok(ty) => {
                match former_sort_loop(pers, st, mode, eager, lane, fuel, fe, 0, caps.nparams + caps.n_idx, &ty) {
                    Err(e) => Err(e),
                    Ok(Some(s)) => match read_level_m(pers, st, &s) {
                        Err(e) => Err(e),
                        Ok(sl) => {
                            if prop_when::is_never(&level::zeroness_of(&sl)) {
                                Ok(None)
                            } else {
                                Ok(Some(sl))
                            }
                        }
                    },
                    Ok(None) => fail(CheckError::Invalid(code_points(&M_PROJ_NO_SORT))),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:795-805 openPisAtFvars
/// Lean twin: `proof/ConRon/Arena/Core.lean:2846-2862 openPisAtFvars` —
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

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2155-2170 openPisRawGoC
/// Lean twin: `proof/ConRon/Arena/Core.lean:2864-2883 openPisRawGo` — the one-pass
/// opening loop, the residual left raw: `acc` holds the already-created fvars
/// — the list `instantiate_list` takes at cursor 0, in PUSH order on an OWNED
/// vector — and each domain is instantiated by them in one `instantiateList`
/// pass, where `openPisAtFvars` re-instantiates the whole remaining body at
/// every binder.  Returns the fvars, the substitution they make and the raw
/// residual.  The list of fvars RETURNED keeps its cons: it is built on the
/// way out.
pub fn open_pis_raw_go(
    pers: &PersTier,
    st: &mut AState,
    acc: Vec<EIdx>,
    n: u64,
    h: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, Vec<EIdx>, EIdx)>, CheckError> {
    if n == 0 {
        Ok(Some((Vec::new(), acc, h.dup2())))
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
                                match open_pis_raw_go(pers, st, acc2, n - 1, &body, i + 1) {
                                    Err(e) => Err(e),
                                    Ok(Some((fvs, acc3, r))) => {
                                        Ok(Some((cons_eidx(&fv, &fvs), acc3, r)))
                                    }
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

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2172-2179 openPisAtFvarsGoC
/// con-leche: ConLeche/Cached/ExprOpsC.lean:2181-2189 openPisAtFvarsC
/// Lean twin: `proof/ConRon/Arena/Core.lean:2885-2895 openPisAtFvarsF` — the
/// one-pass `openPisAtFvars`: the raw opening, then the residual in one
/// `instantiateList` pass.  No fallback: instantiating at free variables never
/// makes a binder appear, so where the one pass finds no `∀` the sequential
/// opening finds none either.  **The executed one.**
pub fn open_pis_at_fvars_f(
    pers: &PersTier,
    st: &mut AState,
    n: u64,
    e: &EIdx,
    i: u64,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    match open_pis_raw_go(pers, st, Vec::new(), n, e, i) {
        Err(err) => Err(err),
        Ok(Some((fvs, acc, r))) => {
            match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &r, &acc, 0) {
                Err(err) => Err(err),
                Ok(b) => Ok(Some((fvs, b))),
            }
        }
        Ok(None) => Ok(None),
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: hasLooseBVarB"`, as code points.
pub const M_FUEL_HLB: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 104, 97, 115, 76,
    111, 111, 115, 101, 66, 86, 97, 114, 66,
];

/// con-leche: none — extraction rule 5 (DESIGN.md's task #97-P4c): a `HashMap::get` match is its own function
/// Lean twin: `proof/ConRon/Arena/Core.lean:2904-2950 hasLooseBVarBGo`
/// — the `memo[(h, i)]?` probe of the `hasLooseBVarB` walk.  Inline, Aeneas
/// reports *"Could not match the contexts"* on the joined arms.
pub fn hlb_probe(memo: &HashMap<EIdxNat, bool>, k: &EIdxNat) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1506-1573 hasLooseBVarBXP
/// Lean twin: `proof/ConRon/Arena/Core.lean:2897-2902 hasLooseBVarBIns`
/// — record one answer for `(e, i)` in the memo the walk hands back.
pub fn has_loose_bvar_b_ins(
    e: &EIdx,
    i: u64,
    r: (bool, HashMap<EIdxNat, bool>),
) -> (bool, HashMap<EIdxNat, bool>) {
    let mut memo: HashMap<EIdxNat, bool> = r.1;
    memo.insert(eidx_nat_key(e, i), r.0);
    (r.0, memo)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:807-820 Expr.hasLooseBVar
/// con-leche: ConLeche/Kernel/CoreDefs.lean:822-840 Expr.hasLooseBVarB
/// con-leche: ConLeche/Cached/ExprOpsC.lean:1506-1573 hasLooseBVarBXP
/// Lean twin: `proof/ConRon/Arena/Core.lean:2904-2950 hasLooseBVarBGo`
/// — does `bvar i` occur loose in `e`?  The packed-bound cutoff (`bvarB ≤ i`)
/// and a per-call memo, as the cached walk has them: the cutoff stops the walk
/// where the variable CANNOT occur, the memo shares a shared node's answer
/// across the paths that reach it.  The memo is keyed by the node AND the
/// index, because the index shifts under binders.
pub fn has_loose_bvar_b_go(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    i: u64,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_HLB)))
    } else {
        match expr_ops::bvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= i {
                    Ok((false, memo))
                } else {
                    match view(pers, st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(j)) => Ok((i == j, memo)),
                        Ok(ENodeView::FVar(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Sort(_)) => Ok((false, memo)),
                        Ok(ENodeView::Const(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Lit(_)) => Ok((false, memo)),
                        Ok(v) => {
                            let k: EIdxNat = eidx_nat_key(h, i);
                            match hlb_probe(&memo, &k) {
                                Some(r) => Ok((r, memo)),
                                None => match has_loose_bvar_b_node(pers, st, memo, i, fuel - 1, v) {
                                    Err(e) => Err(e),
                                    Ok(r) => Ok(has_loose_bvar_b_ins(h, i, r)),
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1506-1573 hasLooseBVarBXP
/// Lean twin: `proof/ConRon/Arena/Core.lean:2904-2950 hasLooseBVarBGo`
/// — the walk's compound arms, split off so that the `view`'s loans are dead
/// at the memo's join (task #97-P4c's extraction rule 5, and P4a's second).
pub fn has_loose_bvar_b_node(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    i: u64,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &f) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i, fuel, &a),
        },
        ENodeView::Lam(ty, b) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i + 1, fuel, &b),
        },
        ENodeView::ForallE(ty, b) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_b_go(pers, st, m, i + 1, fuel, &b),
        },
        ENodeView::LetE(t, val, b) => match has_loose_bvar_b_go(pers, st, memo, i, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => match has_loose_bvar_b_go(pers, st, m, i, fuel, &val) {
                Err(e) => Err(e),
                Ok((true, m2)) => Ok((true, m2)),
                Ok((false, m2)) => has_loose_bvar_b_go(pers, st, m2, i + 1, fuel, &b),
            },
        },
        ENodeView::Proj(_, _, sub) => has_loose_bvar_b_go(pers, st, memo, i, fuel, &sub),
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1575-1579 hasLooseBVarBC
/// Lean twin: `proof/ConRon/Arena/Core.lean:2952-2955 hasLooseBVarBFast`
/// — the executed `hasLooseBVarB` (one memoized DAG walk).
pub fn has_loose_bvar_b_fast(
    pers: &PersTier,
    st: &mut AState,
    i: u64,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match has_loose_bvar_b_go(pers, st, HashMap::new(), i, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r.0),
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: hasLooseBVarIn"`, as code points.
pub const M_FUEL_HLBI: [u32; 30] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 104, 97, 115, 76,
    111, 111, 115, 101, 66, 86, 97, 114, 73, 110,
];

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1590-1603 hasLooseBVarInP
/// con-leche: ConLeche/Cached/ExprOpsC.lean:1619-1672 hasLooseBVarInXP
/// Lean twin: `proof/ConRon/Arena/Core.lean:2957-3002 hasLooseBVarInGo` — does a loose
/// bound variable of index `d ..< d + w` occur in `e`?  Read only: no node is
/// built.  The packed-bound cutoff (`bvarB ≤ d`: no loose variable at or above
/// `d`) at every node; under a binder the window moves up by one.  The memo is
/// `has_loose_bvar_b_go`'s, keyed by the node and the window's base (`w` is
/// fixed for the walk).
pub fn has_loose_bvar_in_go(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    w: u64,
    d: u64,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_HLBI)))
    } else {
        match expr_ops::bvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= d {
                    Ok((false, memo))
                } else {
                    match view(pers, st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(j)) => Ok((d <= j && j - d < w, memo)),
                        Ok(ENodeView::FVar(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Sort(_)) => Ok((false, memo)),
                        Ok(ENodeView::Const(_, _)) => Ok((false, memo)),
                        Ok(ENodeView::Lit(_)) => Ok((false, memo)),
                        Ok(v) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match hlb_probe(&memo, &k) {
                                Some(r) => Ok((r, memo)),
                                None => match has_loose_bvar_in_node(pers, st, memo, w, d, fuel - 1, v) {
                                    Err(e) => Err(e),
                                    Ok(r) => Ok(has_loose_bvar_b_ins(h, d, r)),
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1619-1672 hasLooseBVarInXP
/// Lean twin: `proof/ConRon/Arena/Core.lean:2957-3002 hasLooseBVarInGo` — the walk's
/// compound arms, split off so that the `view`'s loans are dead at the memo's
/// join (extraction rule 5).
pub fn has_loose_bvar_in_node(
    pers: &PersTier,
    st: &mut AState,
    memo: HashMap<EIdxNat, bool>,
    w: u64,
    d: u64,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match v {
        ENodeView::App(f, a) => match has_loose_bvar_in_go(pers, st, memo, w, d, fuel, &f) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_in_go(pers, st, m, w, d, fuel, &a),
        },
        ENodeView::Lam(ty, b) => match has_loose_bvar_in_go(pers, st, memo, w, d, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_in_go(pers, st, m, w, d + 1, fuel, &b),
        },
        ENodeView::ForallE(ty, b) => match has_loose_bvar_in_go(pers, st, memo, w, d, fuel, &ty) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => has_loose_bvar_in_go(pers, st, m, w, d + 1, fuel, &b),
        },
        ENodeView::LetE(t, val, b) => match has_loose_bvar_in_go(pers, st, memo, w, d, fuel, &t) {
            Err(e) => Err(e),
            Ok((true, m)) => Ok((true, m)),
            Ok((false, m)) => match has_loose_bvar_in_go(pers, st, m, w, d, fuel, &val) {
                Err(e) => Err(e),
                Ok((true, m2)) => Ok((true, m2)),
                Ok((false, m2)) => has_loose_bvar_in_go(pers, st, m2, w, d + 1, fuel, &b),
            },
        },
        ENodeView::Proj(_, _, sub) => has_loose_bvar_in_go(pers, st, memo, w, d, fuel, &sub),
        _ => Ok((false, memo)),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1674-1678 hasLooseBVarInC
/// Lean twin: `proof/ConRon/Arena/Core.lean:3004-3008 hasLooseBVarIn` — the window
/// query (one memoized DAG walk); an empty window asks nothing.
pub fn has_loose_bvar_in(
    pers: &PersTier,
    st: &mut AState,
    d: u64,
    w: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    if w == 0 {
        Ok(false)
    } else {
        let memo: HashMap<EIdxNat, bool> = crate::arena::core_state::take_walk_memo(&mut st.memos.hlbi_c);
        match has_loose_bvar_in_go(pers, st, memo, w, d, CORE_WALK_FUEL, e) {
            Err(er) => Err(er),
            Ok(r) => {
                st.memos.hlbi_c = r.1;
                Ok(r.0)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:842-849 structUsedLater
/// con-leche: ConLeche/Cached/IndPositivity.lean:273-280 structUsedLaterC
/// Lean twin: `proof/ConRon/Arena/Core.lean:3010-3016 structUsedLater`
/// — **field `j` is used by a later field**, the official `infer_proj`'s
/// `has_loose_bvars(binding_body(r))` at step `j`.
pub fn struct_used_later(
    pers: &PersTier,
    st: &mut AState,
    cty: &EIdx,
    n_p: u64,
    j: u64,
) -> Result<bool, CheckError> {
    match expr_ops::strip_pis(pers, st, n_p + j + 1, cty) {
        Err(e) => Err(e),
        Ok(Some(q)) => has_loose_bvar_b_fast(pers, st, 0, &q.1),
        Ok(None) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:851-869 projGuardRowsGo
/// con-leche: ConLeche/Cached/ExprOpsC.lean:2240-2251 projGuardRowsGoC
/// Lean twin: `proof/ConRon/Arena/Core.lean:3019-3043 projGuardRowsGo` — **the rows of
/// a projection's guard: the field loop of the official `infer_proj`.**  `h`
/// is the constructor telescope with its parameters and every field before
/// the current one opened, the current field's variable at depth `d`; `k`
/// fields remain before the projected one.  A field the rest of the telescope
/// uses is a row (its domain at depth `d`) and is opened at its variable; one
/// it does not use is stepped over.  The projected field's domain is the last
/// row.  `None` where the telescope binds too few fields.  The cited list is
/// built front to back, here as an accumulator in push order.
pub fn proj_guard_rows_go(
    pers: &PersTier,
    st: &mut AState,
    k: u64,
    d: u64,
    h: &EIdx,
    out: Vec<(u64, EIdx)>,
) -> Result<Option<Vec<(u64, EIdx)>>, CheckError> {
    if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((dom, body)) => {
                if k == 0 {
                    let mut out2: Vec<(u64, EIdx)> = out;
                    out2.push((d, dom));
                    Ok(Some(out2))
                } else {
                    match has_loose_bvar_b_fast(pers, st, 0, &body) {
                        Err(e) => Err(e),
                        Ok(false) => proj_guard_rows_go(pers, st, k - 1, d + 1, &body, out),
                        Ok(true) => match intern_e_fvar(pers, st, d, dom.dup2()) {
                            Err(e) => Err(e),
                            Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, &fv, 0) {
                                Err(e) => Err(e),
                                Ok(b2) => {
                                    let mut out2: Vec<(u64, EIdx)> = out;
                                    out2.push((d, dom));
                                    proj_guard_rows_go(pers, st, k - 1, d + 1, &b2, out2)
                                }
                            },
                        },
                    }
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2253-2265 projGuardFastC
/// Lean twin: `proof/ConRon/Arena/Core.lean:3045-3064 projGuardFast` — **the
/// projection guard's fast case**, on the RAW field telescope (the parameters
/// not substituted): `Some` the projected field's raw domain where no field's
/// type up to the projected one, and nothing after it, mentions a field before
/// it — then no earlier field is used and the projected field's domain is the
/// one row.  `None` otherwise, and where the telescope binds too few fields.
/// `j` counts the fields passed; every query is the read-only window query
/// `has_loose_bvar_in` over the fields, the parameters above it.
pub fn proj_guard_fast(
    pers: &PersTier,
    st: &mut AState,
    k: u64,
    j: u64,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((dom, body)) => {
                if k == 0 {
                    match has_loose_bvar_in(pers, st, 0, j, h) {
                        Err(e) => Err(e),
                        Ok(true) => Ok(None),
                        Ok(false) => Ok(Some(dom)),
                    }
                } else {
                    match has_loose_bvar_in(pers, st, 0, j, &dom) {
                        Err(e) => Err(e),
                        Ok(true) => Ok(None),
                        Ok(false) => proj_guard_fast(pers, st, k - 1, j + 1, &body),
                    }
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:871-889 projGuardRows
/// con-leche: ConLeche/Cached/ExprOpsC.lean:2267-2282 projGuardRowsC
/// con-leche: ConLeche/Cached/CoreC.lean:1359-1371 checkProjRowsI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3079-3102 projGuardRows` — **what a `.proj`
/// use on a structure that may be a proposition must show**: the domains, at
/// the use's level instantiation and at the constructor telescope's own
/// variables, that must be propositions.  `None` where the stored constructor
/// does not bind what the entry says.  The executed shape is the cached
/// twin's: the constructor's type at the use's levels through the
/// per-declaration memo (`const_ty_at`), its parameters opened with the
/// residual left raw (`open_pis_raw_go`).  Where no field before the
/// projected one is mentioned after it (`proj_guard_fast`), the one row is the
/// projected field's domain, its parameters substituted — the rest of the
/// telescope is read, not rebuilt.  Otherwise the residual is substituted and
/// its fields stepped (`proj_guard_rows_go`).
pub fn proj_guard_rows(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    entry: &IProjEntry,
    us: &LsIdx,
) -> Result<Option<Vec<(u64, EIdx)>>, CheckError> {
    match env::ifenv_find(pers, fe, &entry.ctor) {
        Some(ci) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(ci);
            match const_ty_at(pers, st, &cv, us) {
                Err(e) => Err(e),
                Ok(cty) => match open_pis_raw_go(pers, st, Vec::new(), entry.num_params, &cty, 0) {
                    Err(e) => Err(e),
                    Ok(Some((_, acc, r))) => proj_guard_rows_at(pers, st, entry, &acc, &r),
                    Ok(None) => Ok(None),
                },
            }
        }
        None => Ok(None),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:2267-2282 projGuardRowsC
/// Lean twin: `proof/ConRon/Arena/Core.lean:3066-3077 projGuardRowsAt` — the rows past
/// the parameters' raw opening: the fast case, else the substituted residual
/// stepped.
pub fn proj_guard_rows_at(
    pers: &PersTier,
    st: &mut AState,
    entry: &IProjEntry,
    acc: &Vec<EIdx>,
    r: &EIdx,
) -> Result<Option<Vec<(u64, EIdx)>>, CheckError> {
    match proj_guard_fast(pers, st, entry.idx, 0, r) {
        Err(e) => Err(e),
        Ok(Some(dom)) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, acc, entry.idx) {
            Err(e) => Err(e),
            Ok(d) => {
                let mut out: Vec<(u64, EIdx)> = Vec::new();
                out.push((entry.num_params + entry.idx, d));
                Ok(Some(out))
            }
        },
        Ok(None) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, r, acc, 0) {
            Err(e) => Err(e),
            Ok(r2) => proj_guard_rows_go(pers, st, entry.idx, entry.num_params, &r2, Vec::new()),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1198-1211 checkProjGuard
/// con-leche: ConLeche/Cached/CoreC.lean:1373-1403 checkProjGuardI
/// con-leche: ConLeche/Cached/CoreC.lean:1359-1371 checkProjRowsI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3104-3121 checkProjGuard` — **the official
/// `infer_proj` restriction** at this use (con-leche task #480), computed
/// here from the stored structure and constructor types; nothing about it is
/// stored.  The rows are inferred at the io grade in every body, as official's
/// `infer_type` inside `is_prop`.
pub fn check_proj_guard(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    entry: &IProjEntry,
    us: &LsIdx,
) -> Result<(), CheckError> {
    match env::ifenv_find(pers, fe, &entry.struct_name) {
        Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
            let cvt: IConstantVal = env::i_constant_val_dup(cvt0);
            let caps: IIndCaps = env::i_ind_caps_dup(caps0);
            match proj_guard_sort(pers, st, mode, eager, lane, fuel, fe, &cvt, &caps, us) {
                Err(e) => Err(e),
                Ok(None) => Ok(()),
                Ok(Some(gs)) => match proj_guard_rows(pers, st, fe, entry, us) {
                    Err(e) => Err(e),
                    Ok(Some(rows)) => check_guard_rows(pers, st, mode, eager, lane, fuel, fe, &gs, &rows, 0),
                    Ok(None) => fail(CheckError::Invalid(code_points(&M_PROP))),
                },
            }
        }
        Some(_) => fail(CheckError::Invalid(code_points(&M_PROP))),
        None => fail(CheckError::Invalid(code_points(&M_PROP))),
    }
}

// ---------------------------------------------------------------------------
// Inference (`Core.lean:1057-1268`)
//
// `inferBody` (the full grade) and `inferBodyIO` (official's `infer_only`)
// differ at four clauses since con-leche's task #342: the application's
// per-argument check, the λ's domain-sort run, the ∀/λ telescope loops (the
// io grade's binder clauses are chained) and the `let` (the full grade runs
// official's `infer_let` triple, the io grade infers the body at its value);
// the other six agree verbatim, the projection's included (`inferBodyIOI`'s
// `| _ => inferBodyI r fe depth e` at the io view).  The twin writes both
// out in full, as con-leche does; the port spells each shared clause once
// and calls it from both, the projection with the `io` flag that is the io
// view.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3123-3129 inferLamResult` — the λ
/// clause's result, `.forallE ty (bt.abstract1 depth)`.
pub fn infer_lam_result(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    bt: &EIdx,
    depth: u64,
) -> Result<EIdx, CheckError> {
    match abstract1_fast(pers, st, CORE_WALK_FUEL, bt, depth, 0) {
        Err(e) => Err(e),
        Ok(ab) => intern_e_forall_e(pers, st, ty.dup2(), ab),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO`
/// The `.sort` clause, which both bodies write identically.
pub fn infer_sort(pers: &PersTier, st: &mut AState, u: &LIdx) -> Result<EIdx, CheckError> {
    match intern_l_node(pers, st, LNodeView::Succ(u.dup2())) {
        Err(e) => Err(e),
        Ok(su) => intern_e_sort(pers, st, su),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO`
/// The `.fvar` clause — the scope check at the leaf of a traversal that
/// happens anyway — which both bodies write identically.
pub fn infer_fvar(idx: u64, ty: &EIdx, depth: u64) -> Result<EIdx, CheckError> {
    if idx < depth {
        Ok(ty.dup2())
    } else {
        fail(CheckError::Invalid(code_points(&M_FVAR)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO`
/// The `.const` clause, which both bodies write identically: the stored type
/// read through `constTyAt`, so a constant inferred twice at the same levels
/// pays the level substitution once.
pub fn infer_const(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
    us: &LsIdx,
) -> Result<EIdx, CheckError> {
    match env::ifenv_find(pers, fe, n) {
        None => match unknown_const_error(st, n) {
            Err(e) => Err(e),
            Ok(err) => fail(err),
        },
        Some(ci) => {
            let cv: IConstantVal = env::i_constant_info_to_constant_val(ci);
            match view_ls_len(pers, st, us) {
                None => fail_dangling_ls(),
                Some(usl) => {
                    if usl != cv.level_params.len() {
                        fail(CheckError::Invalid(code_points(&M_LEVELS)))
                    } else {
                        const_ty_at(pers, st, &cv, us)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO`
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// The `.lit (.natVal n)` clause, which both bodies write identically: a
/// numeral entering the checker is bounded by the run's maximum `Nat` size
/// (the cited cached clause, official `infer_lit`).
pub fn infer_lit_nat(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    n: &Nat,
) -> Result<EIdx, CheckError>  {
    match nat_lit_stored(pers, st, fe) {
        Err(e) => Err(e),
        Ok(true) => if nat_size_refused(st, n) {
            fail(CheckError::Invalid(code_points(&M_NAT_NUMERAL_TOO_BIG)))
        } else {
            match pin_nat(st) {
                Err(e) => Err(e),
                Ok(nn) => const_e(pers, st, &nn),
            }
        },
        Ok(false) => fail(CheckError::Invalid(code_points(&M_NAT))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO`
/// The `.lit (.strVal _)` clause, which both bodies write identically.
pub fn infer_lit_str(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<EIdx, CheckError>  {
    match str_lit_stored(pers, st, fe) {
        Err(e) => Err(e),
        Ok(true) => match pin_string(st) {
            Err(e) => Err(e),
            Ok(sn) => const_e(pers, st, &sn),
        },
        Ok(false) => fail(CheckError::NotImplemented(code_points(&M_STR))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody` — the full
/// body's `.forallE` clause: the domain's sort, then the binder-telescope loop
/// (`infer_pis`), which infers the codomain sort and folds `imax` outward.
pub fn infer_forall(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => if w.tag() == ETAG_SORT {
                // Binder-telescope loop (con-leche's task #72, `inferBodyI`'s
                // `.forallE` case): the first binder is peeled here, which is
                // why `infer_pis` starts at `k = 1` with one free variable and
                // a one-entry stack.
                match view_sort(pers, st, &w) {
                    None => fail_dangling_e(),
                    Some(u) => match intern_e_fvar(pers, st, depth, ty.dup2()) {
                        Err(e) => Err(e),
                        Ok(fv) => {
                            let mut fvs: Vec<EIdx> = Vec::new();
                            fvs.push(fv);
                            let mut stk: Vec<LIdx> = Vec::new();
                            stk.push(u);
                            infer_pis(
                                pers, st, mode, eager, lane, fuel, fe, depth, PEEL_FUEL, body, 1,
                                fvs, stk,
                            )
                        }
                    },
                }
            } else {
                fail(CheckError::Invalid(code_points(&M_SORT)))
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3368-3402 inferProj` — the `.proj`
/// clause, shared by both bodies (`inferBodyIOI` dispatches it to
/// `inferBodyI` at the io view, which is the `io` flag here): the subject's
/// type head-normalized, its head a constant with a projection-table entry at
/// field `i`; without one, official's `infer_proj` verdict
/// (`proj_miss_error`); a head that is no constant rejects.
pub fn infer_proj(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth, pe) {
        Err(e) => Err(e),
        Ok(tp) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tp) {
            Err(e) => Err(e),
            Ok(te) => match get_app_fn(pers, st, CORE_WALK_FUEL, &te) {
                Err(e) => Err(e),
                Ok(hd) => if hd.tag() == ETAG_CONST {
                    match view_const(pers, st, &hd) {
                        None => fail_dangling_e(),
                        Some((t, us)) => {
                            match env::ifenv_find_proj(pers, fe, &t, i) {
                                Some(entry) => infer_proj_at(
                                    pers, st, mode, eager, lane, fuel, fe, &te, sn, pe, &t, &us,
                                    &entry,
                                ),
                                None => infer_proj_miss(pers, st, fe, &te, &t, sn, i),
                            }
                        },
                    }
                } else {
                    fail(CheckError::Invalid(code_points(&M_INVALID_PROJ)))
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3368-3402 inferProj` — the
/// `.proj` clause with no table entry at field `i`: `projMissError` at the
/// table's presence and the subject type's argument count.
pub fn infer_proj_miss(
    pers: &PersTier,
    st: &mut AState,
    fe: &IFEnv,
    te: &EIdx,
    t: &NIdx,
    sn: &NIdx,
    i: u64,
) -> Result<EIdx, CheckError> {
    let has_table: bool = env::ifenv_find_table(pers, fe, t).is_some();
    match get_app_args(pers, st, CORE_WALK_FUEL, te) {
        Err(e) => Err(e),
        Ok(targs) => fail(proj_miss_error(pers, fe, has_table, t, sn, i, targs.len() as u64)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody` — the `.proj`
/// clause's body, once the entry has been found: the node must name the
/// subject type's head (official `infer_proj`, con-leche's TASK #271) at the
/// entry's parameter count — two rejects that the annotate pass used to make
/// and inference makes since con-leche task #342 L-CK — then the levels, the
/// projection's guard at this use (`check_proj_guard`) and the instantiated
/// body.
pub fn infer_proj_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    te: &EIdx,
    sn: &NIdx,
    pe: &EIdx,
    t: &NIdx,
    us: &LsIdx,
    entry: &IProjEntry,
) -> Result<EIdx, CheckError> {
    match get_app_args(pers, st, CORE_WALK_FUEL, te) {
        Err(e) => Err(e),
        Ok(targs) => {
            if !t.eq2(sn) {
                fail(CheckError::Invalid(code_points(&M_OTHER_STRUCT)))
            } else if targs.len() as u64 != entry.num_params {
                fail(CheckError::Invalid(code_points(&M_PARAMS)))
            } else {
                match view_ls_len(pers, st, us) {
                    None => fail_dangling_ls(),
                    Some(usl) => {
                        if usl == entry.level_params.len() {
                            match check_proj_guard(pers, st, mode, eager, lane, fuel, fe, entry, us) {
                                Err(e) => Err(e),
                                Ok(()) => proj_entry_type_at(pers, st, entry, us, &targs, pe),
                            }
                        } else {
                            fail(CheckError::NotImplemented(code_points(&M_NOENTRY)))
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody` — the full
/// body's λ clause: the domain's sort is run (unlike the io grade's), then the
/// binder-telescope loop (`infer_lams`).
pub fn infer_lam(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => if w.tag() == ETAG_SORT {
                // Binder-telescope loop (con-leche's task #72): the first binder
                // is peeled here, which is why `infer_lams` starts at `k = 1`
                // with one free variable and a one-entry stack.  The domain's
                // sort itself is not read: the `.lam` case wants only that the
                // type's whnf IS a sort, which the handle's own tag says.
                match intern_e_fvar(pers, st, depth, ty.dup2()) {
                    Err(e) => Err(e),
                    Ok(fv) => {
                        let mut fvs: Vec<EIdx> = Vec::new();
                        fvs.push(fv);
                        let mut stk: Vec<EIdx> = Vec::new();
                        stk.push(ty.dup2());
                        infer_lams(
                            pers, st, mode, eager, lane, fuel, fe, depth, PEEL_FUEL, body, 1, fvs,
                            stk,
                        )
                    }
                }
            } else {
                fail(CheckError::Invalid(code_points(&M_SORT)))
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — the io
/// body's λ clause, chained: no domain-sort run (official's `infer_lambda` at
/// `infer_only`), the binder opened at a fresh free variable, the body's type
/// inferred through this lane (`io`, the knot's `ioView`), and the result.
pub fn infer_lam_open(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    io: bool,
) -> Result<EIdx, CheckError> {
    match intern_e_fvar(pers, st, depth, ty.dup2()) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
            Err(e) => Err(e),
            Ok(ob) => match knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth + 1, &ob) {
                Err(e) => Err(e),
                Ok(bt) => infer_lam_result(pers, st, ty, &bt, depth),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody` — the full
/// body's `let` clause, official's `infer_let` (con-leche task #342 S0): the
/// `let`'s type is a type, the value's type matches it, then the body with the
/// value substituted — the ζ reduct, as Lean's kernel infers it.
pub fn infer_let(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    v: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match ensure_sort(pers, st, mode, eager, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(_) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, v) {
                Err(e) => Err(e),
                Ok(tv) => match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &tv, ty) {
                    Err(e) => Err(e),
                    Ok(false) => fail(CheckError::Invalid(code_points(&M_LET_VALUE))),
                    Ok(true) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, b, v, 0) {
                        Err(e) => Err(e),
                        Ok(ob) => knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, &ob),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — the io
/// body's `let` clause, official's `infer_let` at `infer_only` (con-leche task
/// #342 R-C): the body at its value, no check of the type or the value.
pub fn infer_let_io(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    v: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match instantiate1_fast(pers, st, CORE_WALK_FUEL, b, v, 0) {
        Err(e) => Err(e),
        Ok(ob) => knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth, &ob),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1213-1219 defeqArg
/// con-leche: ConLeche/Cached/CoreC.lean:1237-1241 defeqArgI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3290-3296 defeqArg` — **the argument check
/// of a full-grade application** (official `infer_app`): the type of an
/// `eagerReduce _ _` argument is compared with the domain in the eager tower
/// (`knot_defeq_e`), every other argument's in the knot's own.
pub fn defeq_arg(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    ta: &EIdx,
    ty: &EIdx,
) -> Result<bool, CheckError> {
    match is_eager_reduce(pers, st, a) {
        Err(e) => Err(e),
        Ok(true) => knot_defeq_e(pers, st, mode, eager, lane, fuel, fe, depth, ta, ty),
        Ok(false) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, ta, ty),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1243-1273 inferSpineI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3298-3326 inferSpine` — the cached
/// tier's application-inference spine loop, the EXECUTED checker's own `.app`
/// clause.
///
/// **The batched instantiation lever** (task #97-P6-9), the telescope half.
/// This walks the RAW telescope structurally with the arguments accumulated in
/// `acc` (the list `instantiate_list` takes at cursor 0, in PUSH order on an
/// OWNED vector — task #97-P6-15) and substitutes each domain, and the
/// residual, in ONE walk.  con-leche proves the identification with the
/// spec-shaped clause (`ConLeche/Verify/BetaSpine.lean`, `inferSpine_sound`).
///
/// The non-`forallE` arm is the twin's: substitute, `whnf`, and restart the
/// accumulator.  Every argument is checked against its domain, at the full
/// grade.
pub fn infer_spine(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    acc: Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, &acc, 0)
    } else {
        let a: EIdx = args[i].dup2();
        if ty.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, ty) {
                None => fail_dangling_e(),
                Some((dom, body)) => {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, &acc, 0) {
                        Err(e) => Err(e),
                        Ok(dom2) => {
                            match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, &a) {
                                Err(e) => Err(e),
                                Ok(ta) => match defeq_arg(
                                    pers, st, mode, eager, lane, fuel, fe, depth, &a, &ta, &dom2,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(false) => {
                                        fail(CheckError::Invalid(code_points(&M_APP_MISMATCH)))
                                    }
                                    Ok(true) => {
                                        let mut acc2: Vec<EIdx> = acc;
                                        acc2.push(a);
                                        infer_spine(
                                            pers, st, mode, eager, lane, fuel, fe, depth, &body, acc2,
                                            args, i + 1,
                                        )
                                    }
                                },
                            }
                        }
                    }
                },
            }
        } else {
            match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, &acc, 0) {
                Err(e) => Err(e),
                Ok(ty2) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &ty2) {
                    Err(e) => Err(e),
                    Ok(w) => if w.tag() == ETAG_FORALL_E {
                        match view_bind(pers, st, &w) {
                            None => fail_dangling_e(),
                            Some((dom, body)) => {
                                match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, &a) {
                                    Err(e) => Err(e),
                                    Ok(ta) => match defeq_arg(
                                        pers, st, mode, eager, lane, fuel, fe, depth, &a, &ta, &dom,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(false) => {
                                            fail(CheckError::Invalid(code_points(&M_APP_MISMATCH)))
                                        }
                                        Ok(true) => {
                                            let mut acc2: Vec<EIdx> = Vec::new();
                                            acc2.push(a);
                                            infer_spine(
                                                pers, st, mode, eager, lane, fuel, fe, depth, &body,
                                                acc2, args, i + 1,
                                            )
                                        }
                                    },
                                }
                            },
                        }
                    } else {
                        fail(CheckError::Invalid(code_points(&M_FN)))
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3328-3335 inferApp` — the `.app`
/// clause of the cached inference body: the spine's head is inferred once and
/// its Π-telescope is walked against the whole spine.
pub fn infer_app(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match head_and_args(pers, st, e) {
        Err(er) => Err(er),
        Ok(hv) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, &hv.0) {
            Err(er) => Err(er),
            Ok(tf) => {
                let acc: Vec<EIdx> = Vec::new();
                infer_spine(pers, st, mode, eager, lane, fuel, fe, depth, &tf, acc, &hv.1, 0)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The inference binder-telescope loops (con-leche's task #72,
// `Cached/CoreC.lean:910-1023`) — task #97-P6-12.
//
// con-leche's cached tier peels the whole chain: each domain is opened against
// the free variables accumulated so far in ONE `instantiate_list`, the
// residual leaf is opened once and inferred once, and the rebuild closes each
// domain with ONE `abstract_range`.  The identification with the chained spec
// bodies is `ConLeche/Verify/BinderLoop.lean` (`inferLams_sound`,
// `inferPis_sound`).
//
// The two shapes that are the arena's rather than con-leche's: the stack is a
// `Vec` pushed OUTERMOST-first and consumed by a count `n` counting down,
// where con-leche conses a `List` innermost-first and consumes its head — so
// `stk[j]` is the binder at level `d + j` and `j` is exactly the
// `abstract_range` width its domain wants; and `fvs` is built with
// `Vec::push` and read by `instantiate_list` at cursor 0 FROM THE END (task
// #97-P6-15).
//
// **Only the full grade loops.**  con-leche's `inferBodyIOI` keeps BOTH binder
// clauses chained on purpose, so `infer_lam_open` / `infer_forall_io` are the
// io body's binder clauses.  Task #119 (con-leche task #342): the stacks carry
// no binder datum and the leaf runs no codomain check.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:210-221 inferLamsOutI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3155-3166 inferLamsOut` — the
/// outward rebuild of the λ telescope loop: fold the stack innermost binder
/// first, rebuilding one `∀` node per entry.  `stk[j]` is the binder at level
/// `d + j` and its opened domain may mention the `j` free variables below it,
/// so `abstract_range ty d j` closes it.  The intermediate `∀`-node inferences
/// of the chained body are value-determined and cannot fail.
pub fn infer_lams_out(
    pers: &PersTier,
    st: &mut AState,
    d: u64,
    stk: &Vec<EIdx>,
    n: usize,
    cur: &EIdx,
) -> Result<EIdx, CheckError> {
    if n == 0 {
        Ok(cur.dup2())
    } else {
        let j: usize = n - 1;
        match abstract_range_fast(pers, st, CORE_WALK_FUEL, &stk[j], d, j as u64, 0) {
            Err(e) => Err(e),
            Ok(ty_abs) => match intern_e_forall_e(pers, st, ty_abs, cur.dup2()) {
                Err(e) => Err(e),
                Ok(nd) => infer_lams_out(pers, st, d, stk, j, &nd),
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1405-1419 inferLamsLeafI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3168-3176 inferLamsLeaf` — the leaf
/// phase of the λ telescope loop: bulk-open the residual body against the whole
/// accumulated free-variable vector, infer it ONCE, close the leaf with ONE
/// `abstract_range`, then rebuild outward.
pub fn infer_lams_leaf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: Vec<EIdx>,
    stk: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, &fvs, 0) {
        Err(e) => Err(e),
        Ok(ob) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, d + k, &ob) {
            Err(e) => Err(e),
            Ok(bt) => match abstract_range_fast(pers, st, CORE_WALK_FUEL, &bt, d, k, 0) {
                Err(e) => Err(e),
                Ok(cur) => {
                    let n: usize = stk.len();
                    infer_lams_out(pers, st, d, stk, n, &cur)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1421-1442 inferLamsI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3178-3202 inferLams` — the
/// λ-telescope inference loop: peel the raw λ-chain, checking each opened
/// domain to be a type on the way in. `k >= 1` counts the opened binders (the
/// first is peeled by `infer_lam`'s own clause) and `fvs` holds their free
/// variables, in PUSH order on an OWNED vector (task #97-P6-15).
pub fn infer_lams(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: Vec<EIdx>,
    stk: Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    if peel == 0 || t.tag() != ETAG_LAM {
        infer_lams_leaf(pers, st, mode, eager, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view_bind(pers, st, t) {
            None => fail_dangling_e(),
            Some((ty, body)) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, &fvs, 0) {
                Err(e) => Err(e),
                Ok(tyo) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, d + k, &tyo) {
                    Err(e) => Err(e),
                    Ok(tty) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, d + k, &tty) {
                        Err(e) => Err(e),
                        Ok(w) => {
                            if w.tag() == ETAG_SORT {
                                match intern_e_fvar(pers, st, d + k, tyo.dup2()) {
                                    Err(e) => Err(e),
                                    Ok(fv) => {
                                        let mut fvs2: Vec<EIdx> = fvs;
                                        fvs2.push(fv);
                                        let mut stk2: Vec<EIdx> = stk;
                                        stk2.push(tyo);
                                        infer_lams(
                                            pers, st, mode, eager, lane, fuel, fe, d, peel - 1, &body,
                                            k + 1, fvs2, stk2,
                                        )
                                    }
                                }
                            } else {
                                fail(CheckError::Invalid(code_points(&M_SORT)))
                            }
                        }
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:223-234 inferPisOutI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3204-3213 inferPisOut` — the
/// outward fold of the ∀ telescope loop: fold the accumulated domain sorts by
/// `imax`, innermost binder first, which is exactly the chained `∀`-rule's
/// result value.  It reads no per-node datum (con-leche task #272: a walk of
/// the growing right spine was `O(k²)`).
pub fn infer_pis_out(
    pers: &PersTier,
    st: &mut AState,
    stk: &Vec<LIdx>,
    n: usize,
    v: &LIdx,
) -> Result<LIdx, CheckError> {
    if n == 0 {
        Ok(v.dup2())
    } else {
        let j: usize = n - 1;
        match intern_l_node(pers, st, LNodeView::Imax(stk[j].dup2(), v.dup2())) {
            Err(e) => Err(e),
            Ok(v2) => infer_pis_out(pers, st, stk, j, &v2),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1444-1456 inferPisLeafI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3215-3225 inferPisLeaf` — the leaf
/// phase of the ∀ telescope loop: bulk-open the residual body against the whole
/// accumulated free-variable vector, infer its sort ONCE, then fold the domain
/// sorts outward.
pub fn infer_pis_leaf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: Vec<EIdx>,
    stk: &Vec<LIdx>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, &fvs, 0) {
        Err(e) => Err(e),
        Ok(ob) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, d + k, &ob) {
            Err(e) => Err(e),
            Ok(bt) => match ensure_sort(pers, st, mode, eager, lane, fuel, fe, d + k, &bt) {
                Err(e) => Err(e),
                Ok(v) => {
                    let n: usize = stk.len();
                    match infer_pis_out(pers, st, stk, n, &v) {
                        Err(e) => Err(e),
                        Ok(iv) => intern_e_sort(pers, st, iv),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1458-1480 inferPisI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3227-3248 inferPis` — the
/// ∀-telescope inference loop: peel the raw ∀-chain, checking each opened
/// domain to be a type on the way in and accumulating its sort, infer the
/// bulk-opened leaf's sort once, and fold `imax` outward.  The stack carries
/// levels and no expression at all.
pub fn infer_pis(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: Vec<EIdx>,
    stk: Vec<LIdx>,
) -> Result<EIdx, CheckError> {
    if peel == 0 || t.tag() != ETAG_FORALL_E {
        infer_pis_leaf(pers, st, mode, eager, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view_bind(pers, st, t) {
            None => fail_dangling_e(),
            Some((ty, body)) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, &fvs, 0) {
                Err(e) => Err(e),
                Ok(tyo) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, d + k, &tyo) {
                    Err(e) => Err(e),
                    Ok(tty) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, d + k, &tty) {
                        Err(e) => Err(e),
                        Ok(w) => {
                            if w.tag() == ETAG_SORT {
                                match view_sort(pers, st, &w) {
                                    None => fail_dangling_e(),
                                    Some(u) => match intern_e_fvar(pers, st, d + k, tyo.dup2()) {
                                        Err(e) => Err(e),
                                        Ok(fv) => {
                                            let mut fvs2: Vec<EIdx> = fvs;
                                            fvs2.push(fv);
                                            let mut stk2: Vec<LIdx> = stk;
                                            stk2.push(u);
                                            infer_pis(
                                                pers, st, mode, eager, lane, fuel, fe, d, peel - 1,
                                                &body, k + 1, fvs2, stk2,
                                            )
                                        }
                                    },
                                }
                            } else {
                                fail(CheckError::Invalid(code_points(&M_SORT)))
                            }
                        }
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1221-1321 inferBody
/// con-leche: ConLeche/Cached/CoreC.lean:1482-1588 inferBodyI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3404-3467 inferBody` — the
/// full-grade inference body (official's `infer_type_core` with
/// `infer_only = false`).
pub fn infer_body(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Sort(u)) => infer_sort(pers, st, &u),
        Ok(ENodeView::FVar(idx, ty)) => infer_fvar(idx, &ty, depth),
        Ok(ENodeView::Const(n, us)) => infer_const(pers, st, fe, &n, &us),
        Ok(ENodeView::Lit(Literal::NatVal(n))) => infer_lit_nat(pers, st, fe, &n),
        Ok(ENodeView::Lit(Literal::StrVal(_))) => infer_lit_str(pers, st, fe),
        Ok(ENodeView::ForallE(ty, body)) => {
            infer_forall(pers, st, mode, eager, lane, fuel, fe, depth, &ty, &body)
        }
        Ok(ENodeView::Lam(ty, body)) => {
            infer_lam(pers, st, mode, eager, lane, fuel, fe, depth, &ty, &body)
        }
        Ok(ENodeView::App(_, _)) => infer_app(pers, st, mode, eager, lane, fuel, fe, depth, e),
        Ok(ENodeView::Proj(sn, i, pe)) => {
            infer_proj(pers, st, mode, eager, lane, false, fuel, fe, depth, &sn, i, &pe)
        }
        Ok(ENodeView::LetE(ty, v, b)) => {
            infer_let(pers, st, mode, eager, lane, fuel, fe, depth, &ty, &v, &b)
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_INFER)))
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — **the io
/// inference body**, official's `infer_type_core` with `infer_only = true`
/// (con-leche tasks #161, #170, #346): the application's arguments are not
/// checked against their domains, the λ's domain is not checked to be a type,
/// and a `let` infers its body at its value with no check of the type or the
/// value.  The binder clauses are chained.
///
/// The `io` flag is the twin's `CoreFnsA.ioView`: it says whether this body's
/// `r.infer` is the knot's `inferIO` slot (`coreKnot`'s io slot passes
/// `ioView (coreKnot … fuel)`) or its `infer` slot (`coreKnotIO` passes the
/// plain record).
pub fn infer_body_io(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Sort(u)) => infer_sort(pers, st, &u),
        Ok(ENodeView::FVar(idx, ty)) => infer_fvar(idx, &ty, depth),
        Ok(ENodeView::Const(n, us)) => infer_const(pers, st, fe, &n, &us),
        Ok(ENodeView::Lit(Literal::NatVal(n))) => infer_lit_nat(pers, st, fe, &n),
        Ok(ENodeView::Lit(Literal::StrVal(_))) => infer_lit_str(pers, st, fe),
        Ok(ENodeView::ForallE(ty, body)) => {
            infer_forall_io(pers, st, mode, eager, lane, io, fuel, fe, depth, &ty, &body)
        }
        Ok(ENodeView::Lam(ty, body)) => {
            infer_lam_open(pers, st, mode, eager, lane, fuel, fe, depth, &ty, &body, io)
        }
        Ok(ENodeView::App(_, _)) => {
            infer_app_io_at(pers, st, mode, eager, lane, io, fuel, fe, depth, e)
        }
        Ok(ENodeView::Proj(sn, i, pe)) => {
            infer_proj(pers, st, mode, eager, lane, io, fuel, fe, depth, &sn, i, &pe)
        }
        Ok(ENodeView::LetE(_, v, b)) => {
            infer_let_io(pers, st, mode, eager, lane, io, fuel, fe, depth, &v, &b)
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_INFER)))
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — the io
/// body's ∀ clause, chained: the domain's sort through this lane, then
/// `infer_forall_io_at`.
pub fn infer_forall_io(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => if w.tag() == ETAG_SORT {
                match view_sort(pers, st, &w) {
                    None => fail_dangling_e(),
                    Some(u) => infer_forall_io_at(
                        pers, st, mode, eager, lane, io, fuel, fe, depth, ty, body, &u,
                    ),
                }
            } else {
                fail(CheckError::Invalid(code_points(&M_SORT)))
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — the io
/// body's ∀ clause, once the domain's sort is known: the opened codomain's
/// sort and `imax`.
pub fn infer_forall_io_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    u: &LIdx,
) -> Result<EIdx, CheckError> {
    match intern_e_fvar(pers, st, depth, ty.dup2()) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
            Err(e) => Err(e),
            Ok(ob) => match knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth + 1, &ob) {
                Err(e) => Err(e),
                Ok(tb) => match ensure_sort(pers, st, mode, eager, lane, fuel, fe, depth + 1, &tb) {
                    Err(e) => Err(e),
                    Ok(v) => match intern_l_node(pers, st, LNodeView::Imax(u.dup2(), v.dup2())) {
                        Err(e) => Err(e),
                        Ok(iu) => intern_e_sort(pers, st, iu),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1323-1409 inferBodyIO
/// con-leche: ConLeche/Cached/CoreC.lean:1590-1640 inferBodyIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3469-3542 inferBodyIO` — the io
/// body's `.app` clause, with `r.infer` resolved through this lane.
pub fn infer_app_io_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match head_and_args(pers, st, e) {
        Err(er) => Err(er),
        Ok(hv) => {
            match knot_infer_at(pers, st, mode, eager, lane, io, fuel, fe, depth, &hv.0) {
                Err(er) => Err(er),
                Ok(tf) => {
                    let acc: Vec<EIdx> = Vec::new();
                    infer_spine_io(pers, st, mode, eager, lane, fuel, fe, depth, &tf, acc, &hv.1, 0)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1275-1295 inferSpineIOI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3337-3358 inferSpineIO` — **the
/// io-grade spine walk**, official's `infer_only` (con-leche task #342, #346):
/// the function's type is walked through the arguments with no argument
/// inference and no domain comparison.  A syntactic `.forallE` is its own
/// whnf; anything else is instantiated and whnf'd before the next step.
pub fn infer_spine_io(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    acc: Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, &acc, 0)
    } else {
        let a: EIdx = args[i].dup2();
        if ty.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, ty) {
                None => fail_dangling_e(),
                Some((_, body)) => {
                    let mut acc2: Vec<EIdx> = acc;
                    acc2.push(a);
                    infer_spine_io(pers, st, mode, eager, lane, fuel, fe, depth, &body, acc2, args, i + 1)
                }
            }
        } else {
            match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, &acc, 0) {
                Err(e) => Err(e),
                Ok(ty2) => match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, &ty2) {
                    Err(e) => Err(e),
                    Ok(w) => {
                        if w.tag() == ETAG_FORALL_E {
                            match view_bind(pers, st, &w) {
                                None => fail_dangling_e(),
                                Some((_, body)) => {
                                    let mut acc2: Vec<EIdx> = Vec::new();
                                    acc2.push(a);
                                    infer_spine_io(
                                        pers, st, mode, eager, lane, fuel, fe, depth, &body, acc2, args,
                                        i + 1,
                                    )
                                }
                            }
                        } else {
                            fail(CheckError::Invalid(code_points(&M_FN)))
                        }
                    }
                },
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Definitional equality (`Core.lean:2342-2593`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1411-1424 boolTrueShortcut
/// Lean twin: `proof/ConRon/Arena/Core.lean:3548-3553 boolTrueShortcut` — **the
/// eq-true shortcut** (the divergence audit's E2): the left side is fully
/// head-normalised and the verdict is `true` iff the reduct is `Bool.true`.
pub fn bool_true_shortcut(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
) -> Result<bool, CheckError> {
    match knot_whnf(pers, st, mode, eager, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(w) => is_bool_true(pers, st, &w),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1426-1455 defeqSpine
/// Lean twin: `proof/ConRon/Arena/Core.lean:3555-3581 defeqSpine` —
/// levels-and-spine congruence for two applications of the *same* stored
/// constant (the lazy delta same-head short-circuit, official's
/// `try_eq_const_app`).  The arguments are compared **last to first**, as
/// official `is_def_eq_args` walks `app_arg`/`app_fn` from the outermost
/// application inwards (`tests/e2e/src/spine_arg_order.lean`): the spines are
/// reversed with `eidx_rev` and handed to `def_eq_list`.
pub fn defeq_spine(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(ha) => if ha.tag() == ETAG_CONST {
            match view_const(pers, st, &ha) {
                None => fail_dangling_e(),
                Some((n, us)) => match get_app_fn(pers, st, CORE_WALK_FUEL, b) {
                    Err(e) => Err(e),
                    Ok(hb) => if hb.tag() == ETAG_CONST {
                        match view_const(pers, st, &hb) {
                            None => fail_dangling_e(),
                            Some((n2, us2)) => match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                                Err(e) => Err(e),
                                Ok(aa) => match get_app_args(pers, st, CORE_WALK_FUEL, b) {
                                    Err(e) => Err(e),
                                    Ok(bb) => {
                                        if n.eq2(&n2) && aa.len() == bb.len() {
                                            match lvls_eq(pers, st, &us, &us2) {
                                                Err(e) => Err(e),
                                                Ok(Some(true)) => {
                                                    // last to first, as
                                                    // official `is_def_eq_args`
                                                    let ra: Vec<EIdx> = eidx_rev(&aa, aa.len(), Vec::with_capacity(aa.len()));
                                                    let rb: Vec<EIdx> = eidx_rev(&bb, bb.len(), Vec::with_capacity(bb.len()));
                                                    def_eq_list(
                                                        pers, st, mode, eager, lane, fuel, fe, depth, &ra, &rb, 0,
                                                    )
                                                }
                                                Ok(_) => Ok(false),
                                            }
                                        } else {
                                            Ok(false)
                                        }
                                    }
                                },
                            },
                        }
                    } else {
                        Ok(false)
                    },
                },
            }
        } else {
            Ok(false)
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction
/// Lean twin: `proof/ConRon/Arena/Core.lean:3583-3591 defeqNoFvars` — the
/// literal-acceleration guard: *both* sides free of free variables, mirroring
/// the official kernel's `lazy_delta_reduction`.  The arena reads the `O(1)`
/// eager per-node fvar range where the specification walks.
pub fn defeq_no_fvars(
    pers: &PersTier,
    st: &mut AState,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError>  {
    match has_fvar_fast(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(true) => Ok(false),
        Ok(false) => match has_fvar_fast(pers, st, CORE_WALK_FUEL, b) {
            Err(e) => Err(e),
            Ok(y) => Ok(!y),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction
/// Lean twin: `proof/ConRon/Arena/Core.lean:3593-3599 lazyFoldOk` — **the literal
/// fold's guard**: the eager flag (official `m_eager_reduce`)
/// or both sides free of free variables — official's
/// `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`.  Under the flag the
/// sides are not walked.
pub fn lazy_fold_ok(
    pers: &PersTier,
    st: &mut AState,
    eager: bool,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if eager {
        Ok(true)
    } else {
        defeq_no_fvars(pers, st, a, b)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1457-1460 bindersFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:3603-3607 bindersFuel` — descent
/// budget of the binder-telescope comparison (`defeq_binders`): `2^62`.
/// Exhaustion is not an error: the level reached is compared as the innermost
/// one, which is always sound.
pub const BINDERS_FUEL: u64 = 4611686018427387904; // 2^62

/// con-leche: ConLeche/Kernel/Core.lean:1462-1469 defeqBindersInner
/// con-leche: ConLeche/Cached/CoreC.lean:1648-1657 defeqBindersInnerI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3609-3620 defeqBindersInner` — the
/// innermost level of `defeq_binders`: the opened bodies, and for two
/// λ-telescopes (`lam`) at the verified mode their FULL-grade types (the λ
/// check).
pub fn defeq_binders_inner(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    lam: bool,
    depth: u64,
    b1: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth + 1, b1, b2) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => {
            if lam && verified_checks(mode) {
                match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth + 1, b1) {
                    Err(e) => Err(e),
                    Ok(t1) => match knot_infer(pers, st, mode, eager, lane, fuel, fe, depth + 1, b2) {
                        Err(e) => Err(e),
                        Ok(t2) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth + 1, &t1, &t2),
                    },
                }
            } else {
                Ok(true)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1471-1475 defeqDomain
/// con-leche: ConLeche/Cached/CoreC.lean:1659-1665 defeqDomainI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3622-3632 defeqDomain` — one
/// level's domains in `defeq_binders`: the same RAW domain handle is `true`;
/// otherwise the left domain, opened over the variables so far in one
/// `instantiate_list` (`fvs`, push order), against the opened right one `dom2`.
pub fn defeq_domain(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    fvs: &Vec<EIdx>,
    ty1: &EIdx,
    ty2: &EIdx,
    dom2: &EIdx,
) -> Result<bool, CheckError> {
    if ty1.eq2(ty2) {
        Ok(true)
    } else {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty1, fvs, 0) {
            Err(e) => Err(e),
            Ok(dom1) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &dom1, dom2),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1477-1500 defeqBinders
/// con-leche: ConLeche/Cached/CoreC.lean:1667-1683 defeqBindersI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3634-3664 defeqBinders` —
/// **binder-telescope congruence** (the official kernel's
/// `is_def_eq_binding`): two ∀-telescopes (`!lam`) or two λ-telescopes (`lam`)
/// are peeled together while both bodies are binders of that kind
/// (`binder_pair`).  The bodies stay RAW: `fvs` holds the variables of the
/// levels above, in push order (outermost first), and every opening is one
/// `instantiate_list` over it.  Per level the right domain is opened (`dom2`),
/// the domains are compared by `defeq_domain`, and the variable
/// `fvar (depth, dom2)` is pushed.  At the innermost level both bodies are
/// opened once and compared by `defeq_binders_inner`.
pub fn defeq_binders(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    lam: bool,
    bfuel: u64,
    depth: u64,
    fvs: Vec<EIdx>,
    ty1: &EIdx,
    body1: &EIdx,
    ty2: &EIdx,
    body2: &EIdx,
) -> Result<bool, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty2, &fvs, 0) {
        Err(e) => Err(e),
        Ok(dom2) => match defeq_domain(pers, st, mode, eager, lane, fuel, fe, depth, &fvs, ty1, ty2, &dom2) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match intern_e_fvar(pers, st, depth, dom2) {
                Err(e) => Err(e),
                Ok(fv) => {
                    let mut fvs2: Vec<EIdx> = fvs;
                    fvs2.push(fv);
                    let bp: Result<Option<(EIdx, EIdx, EIdx, EIdx)>, CheckError> = if bfuel == 0 {
                        Ok(None)
                    } else {
                        binder_pair(pers, st, lam, body1, body2)
                    };
                    match bp {
                        Err(e) => Err(e),
                        Ok(Some((ty1b, body1b, ty2b, body2b))) => defeq_binders(
                            pers, st, mode, eager, lane, fuel, fe, lam, bfuel - 1, depth + 1, fvs2, &ty1b,
                            &body1b, &ty2b, &body2b,
                        ),
                        Ok(None) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, body1, &fvs2, 0) {
                            Err(e) => Err(e),
                            Ok(o1) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, body2, &fvs2, 0) {
                                Err(e) => Err(e),
                                Ok(o2) => defeq_binders_inner(
                                    pers, st, mode, eager, lane, fuel, fe, lam, depth, &o1, &o2,
                                ),
                            },
                        },
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1502-1524 quickDefEq
/// con-leche: ConLeche/Cached/CoreC.lean:1685-1701 quickDefEqI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3666-3692 quickDefEq` — **the easy
/// cases** (the official kernel's `quick_is_def_eq`): the syntactic fast path,
/// and the pairs decided on the spot — two sorts, two literals, two `∀`s and
/// two `λ`s (binder-telescope congruence, `defeq_binders`).
/// `None` is "not an easy case".  Only a pair of equal tags among those four
/// kinds is viewed.
pub fn quick_defeq(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<Option<bool>, CheckError> {
    if a.eq2(b) {
        Ok(Some(true))
    } else {
        let ta: u32 = a.tag();
        if ta != b.tag() {
            Ok(None)
        } else if ta == ETAG_SORT || ta == ETAG_LIT || ta == ETAG_FORALL_E || ta == ETAG_LAM {
            match view(pers, st, a) {
                Err(e) => Err(e),
                Ok(va) => match view(pers, st, b) {
                    Err(e) => Err(e),
                    Ok(vb) => match (va, vb) {
                        (ENodeView::Sort(u), ENodeView::Sort(v)) => {
                            match lvl_eq(pers, st, &u, &v) {
                                Err(e) => Err(e),
                                Ok(o) => match lift_fueled(o) {
                                    Err(e) => Err(e),
                                    Ok(ok) => Ok(Some(ok)),
                                },
                            }
                        }
                        (ENodeView::Lit(l1), ENodeView::Lit(l2)) => {
                            Ok(Some(expr::literal_beq(&l1, &l2)))
                        }
                        (ENodeView::ForallE(ty1, body1), ENodeView::ForallE(ty2, body2)) => {
                            match defeq_binders(
                                pers, st, mode, eager, lane, fuel, fe, false, BINDERS_FUEL, depth, Vec::new(),
                                &ty1, &body1, &ty2, &body2,
                            ) {
                                Err(e) => Err(e),
                                Ok(ok) => Ok(Some(ok)),
                            }
                        }
                        (ENodeView::Lam(ty1, body1), ENodeView::Lam(ty2, body2)) => {
                            match defeq_binders(
                                pers, st, mode, eager, lane, fuel, fe, true, BINDERS_FUEL, depth, Vec::new(),
                                &ty1, &body1, &ty2, &body2,
                            ) {
                                Err(e) => Err(e),
                                Ok(ok) => Ok(Some(ok)),
                            }
                        }
                        (_, _) => Ok(None),
                    },
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1526-1530 Expr.isNatZero
/// Lean twin: `proof/ConRon/Arena/Core.lean:3694-3708 isNatZero` — `Nat.zero` or the
/// literal `0` (official `is_nat_zero`).
pub fn is_nat_zero(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<bool, CheckError> {
    if e.tag() == ETAG_LIT {
        match view(pers, st, e) {
            Err(er) => Err(er),
            Ok(ENodeView::Lit(Literal::NatVal(n))) => Ok(nat::is_zero(&n)),
            Ok(_) => Ok(false),
        }
    } else if e.tag() == ETAG_CONST {
        match view_const(pers, st, e) {
            None => fail_dangling_e(),
            Some((c, us)) => match empty_levels(st) {
                Err(er) => Err(er),
                Ok(el) => match pin_nat_zero(st) {
                    Err(er) => Err(er),
                    Ok(nz) => Ok(c.eq2(&nz) && us.eq2(&el)),
                },
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1532-1537 Expr.natPred?
/// Lean twin: `proof/ConRon/Arena/Core.lean:3710-3732 natPred?` — the predecessor of a
/// successor form (official `is_nat_succ`): a nonzero literal (its predecessor
/// literal interned), or `Nat.succ x`.
pub fn nat_pred(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<Option<EIdx>, CheckError> {
    if e.tag() == ETAG_LIT {
        match view(pers, st, e) {
            Err(er) => Err(er),
            Ok(ENodeView::Lit(Literal::NatVal(n))) => {
                if nat::is_zero(&n) {
                    Ok(None)
                } else {
                    let k: Nat = nat::pred(&n);
                    match intern_e_lit(pers, st, expr::literal_nat(k)) {
                        Err(er) => Err(er),
                        Ok(l) => Ok(Some(l)),
                    }
                }
            }
            Ok(_) => Ok(None),
        }
    } else if e.tag() == ETAG_APP {
        match view_app(pers, st, e) {
            None => fail_dangling_e(),
            Some((f, x)) => {
                if f.tag() == ETAG_CONST {
                    match view_const(pers, st, &f) {
                        None => fail_dangling_e(),
                        Some((c, us)) => match empty_levels(st) {
                            Err(er) => Err(er),
                            Ok(el) => match pin_nat_succ(st) {
                                Err(er) => Err(er),
                                Ok(ns) => {
                                    if c.eq2(&ns) && us.eq2(&el) {
                                        Ok(Some(x))
                                    } else {
                                        Ok(None)
                                    }
                                }
                            },
                        },
                    }
                } else {
                    Ok(None)
                }
            }
        }
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1539-1551 defeqOffset
/// con-leche: ConLeche/Cached/CoreC.lean:1703-1713 defeqOffsetI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3734-3752 defeqOffset` — **offsets** (the
/// official kernel's `is_def_eq_offset`): two zeros are equal, two successor
/// forms compare their predecessors; two literals are left to `quick_defeq`.
pub fn defeq_offset(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<Option<bool>, CheckError> {
    match is_nat_zero(pers, st, a) {
        Err(e) => Err(e),
        Ok(za) => match is_nat_zero(pers, st, b) {
            Err(e) => Err(e),
            Ok(zb) => {
                if za && zb {
                    Ok(Some(true))
                } else if a.tag() == ETAG_LIT && b.tag() == ETAG_LIT {
                    Ok(None)
                } else {
                    match nat_pred(pers, st, a) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(None),
                        Ok(Some(x)) => match nat_pred(pers, st, b) {
                            Err(e) => Err(e),
                            Ok(None) => Ok(None),
                            Ok(Some(y)) => {
                                match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &x, &y) {
                                    Err(e) => Err(e),
                                    Ok(ok) => Ok(Some(ok)),
                                }
                            }
                        },
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1553-1557 Expr.headIsProj
/// Lean twin: `proof/ConRon/Arena/Core.lean:3754-3758 headIsProj` — is the head of
/// the application spine a projection?
pub fn head_is_proj(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => Ok(h.tag() == ETAG_PROJ),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1559-1567 tryUnfoldProjApp
/// con-leche: ConLeche/Cached/CoreC.lean:1715-1722 tryUnfoldProjAppI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3760-3769 tryUnfoldProjApp` — official
/// `try_unfold_proj_app`: a projection-headed term through the FULL `whnfCore`;
/// `Some` whenever that changed it.
pub fn try_unfold_proj_app(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match head_is_proj(pers, st, e) {
        Err(er) => Err(er),
        Ok(false) => Ok(None),
        Ok(true) => match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, false, depth, e) {
            Err(er) => Err(er),
            Ok(e2) => {
                if e2.eq2(e) {
                    Ok(None)
                } else {
                    Ok(Some(e2))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:3771-3777 DeltaStepA` — the outcome of one
/// lazy-delta step (official `reduction_status`), over handles.
pub enum DeltaStepA {
    /// con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep
    /// Continue with the reduced pair.
    Cont(EIdx, EIdx),
    /// con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep
    /// Definitionally equal.
    Eq,
    /// con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep
    /// Not definitionally equal.
    Diff,
    /// con-leche: ConLeche/Kernel/Core.lean:1569-1576 DeltaStep
    /// Neither side unfolds.
    Unknown,
}

/// con-leche: ConLeche/Kernel/Core.lean:1578-1583 deltaQuick
/// con-leche: ConLeche/Cached/CoreC.lean:1724-1730 deltaQuickI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3779-3787 deltaQuick` — the end of a
/// lazy-delta step: `quick_defeq` on the new pair.
pub fn delta_quick(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<DeltaStepA, CheckError> {
    match quick_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
        Err(e) => Err(e),
        Ok(Some(true)) => Ok(DeltaStepA::Eq),
        Ok(Some(false)) => Ok(DeltaStepA::Diff),
        Ok(None) => Ok(DeltaStepA::Cont(a.dup2(), b.dup2())),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:3789-3846 lazyDeltaStep` — one side
/// unfolded: the CHEAP `whnfCore` of the unfolding, then `delta_quick` with the
/// sides in their places (`flipped`: the unfolded side is `b`).
pub fn lazy_delta_one(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    u: &EIdx,
    other: &EIdx,
    flipped: bool,
) -> Result<DeltaStepA, CheckError> {
    match unfold_definition(pers, st, fe, u) {
        Err(e) => Err(e),
        Ok(None) => Ok(DeltaStepA::Unknown),
        Ok(Some(u2)) => match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, &u2) {
            Err(e) => Err(e),
            Ok(u3) => {
                if flipped {
                    delta_quick(pers, st, mode, eager, lane, fuel, fe, depth, other, &u3)
                } else {
                    delta_quick(pers, st, mode, eager, lane, fuel, fe, depth, &u3, other)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:3789-3846 lazyDeltaStep` — one side
/// unfoldable: a projection application on the OTHER side is reduced first
/// (official `try_unfold_proj_app`), else the unfoldable side unfolds.
/// `flipped`: the unfoldable side is `b`.
pub fn lazy_delta_side(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    u: &EIdx,
    other: &EIdx,
    flipped: bool,
) -> Result<DeltaStepA, CheckError> {
    match try_unfold_proj_app(pers, st, mode, eager, lane, fuel, fe, depth, other) {
        Err(e) => Err(e),
        Ok(Some(o2)) => {
            if flipped {
                delta_quick(pers, st, mode, eager, lane, fuel, fe, depth, &o2, u)
            } else {
                delta_quick(pers, st, mode, eager, lane, fuel, fe, depth, u, &o2)
            }
        }
        Ok(None) => lazy_delta_one(pers, st, mode, eager, lane, fuel, fe, depth, u, other, flipped),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:3789-3846 lazyDeltaStep` — both sides
/// unfold: the CHEAP `whnfCore` of each unfolding, then `delta_quick`.
pub fn lazy_delta_unfold_both(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<DeltaStepA, CheckError> {
    match unfold_definition(pers, st, fe, a) {
        Err(e) => Err(e),
        Ok(ua) => match unfold_definition(pers, st, fe, b) {
            Err(e) => Err(e),
            Ok(ub) => match (ua, ub) {
                (Some(a2), Some(b2)) => {
                    match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, &a2) {
                        Err(e) => Err(e),
                        Ok(a3) => {
                            match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, &b2)
                            {
                                Err(e) => Err(e),
                                Ok(b3) => {
                                    delta_quick(pers, st, mode, eager, lane, fuel, fe, depth, &a3, &b3)
                                }
                            }
                        }
                    }
                }
                (_, _) => Ok(DeltaStepA::Unknown),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:3789-3846 lazyDeltaStep` — both sides
/// unfoldable: the hint comparison decides which side unfolds; at equal hints
/// the same-head spine shortcut (equal *regular* hints only), then both.
pub fn lazy_delta_both(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<DeltaStepA, CheckError> {
    match head_hint(pers, st, fe, a) {
        Err(e) => Err(e),
        Ok(ha) => match head_hint(pers, st, fe, b) {
            Err(e) => Err(e),
            Ok(hb) => {
                if crate::kernel::env::reducibility_hint_lt(&hb, &ha) {
                    lazy_delta_one(pers, st, mode, eager, lane, fuel, fe, depth, a, b, false)
                } else if crate::kernel::env::reducibility_hint_lt(&ha, &hb) {
                    lazy_delta_one(pers, st, mode, eager, lane, fuel, fe, depth, b, a, true)
                } else {
                    match same_const_heads(pers, st, a, b) {
                        Err(e) => Err(e),
                        Ok(sch) => {
                            let sp = if crate::kernel::env::reducibility_hint_same_regular(&ha, &hb)
                                && sch
                            {
                                defeq_spine(pers, st, mode, eager, lane, fuel, fe, depth, a, b)
                            } else {
                                Ok(false)
                            };
                            match sp {
                                Err(e) => Err(e),
                                Ok(true) => Ok(DeltaStepA::Eq),
                                Ok(false) => lazy_delta_unfold_both(
                                    pers, st, mode, eager, lane, fuel, fe, depth, a, b,
                                ),
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1585-1646 lazyDeltaStep
/// con-leche: ConLeche/Cached/CoreC.lean:1732-1780 lazyDeltaStepI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3789-3846 lazyDeltaStep` — **one
/// lazy-delta step** (the official kernel's `lazy_delta_reduction_step`):
/// `unfoldableHead` decides, and only the chosen side is unfolded.
pub fn lazy_delta_step(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<DeltaStepA, CheckError> {
    match unfoldable_head(pers, st, fe, a) {
        Err(e) => Err(e),
        Ok(ua) => match unfoldable_head(pers, st, fe, b) {
            Err(e) => Err(e),
            Ok(ub) => {
                if !ua && !ub {
                    Ok(DeltaStepA::Unknown)
                } else if ua && !ub {
                    lazy_delta_side(pers, st, mode, eager, lane, fuel, fe, depth, a, b, false)
                } else if !ua && ub {
                    lazy_delta_side(pers, st, mode, eager, lane, fuel, fe, depth, b, a, true)
                } else {
                    lazy_delta_both(pers, st, mode, eager, lane, fuel, fe, depth, a, b)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1648-1653 LazyRes
/// Lean twin: `proof/ConRon/Arena/Core.lean:3848-3852 LazyResA` — the outcome of the
/// lazy-delta loop, over handles: a verdict, or the pair it got stuck on.
pub enum LazyResA {
    /// con-leche: ConLeche/Kernel/Core.lean:1648-1653 LazyRes
    /// The loop decided.
    Verdict(bool),
    /// con-leche: ConLeche/Kernel/Core.lean:1648-1653 LazyRes
    /// Neither side unfolds any more: the pair reached.
    Unknown(EIdx, EIdx),
}

/// con-leche: ConLeche/Kernel/Core.lean:1655-1661 defeqLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:3854-3857 defeqLoopFuel` — step budget of
/// the two lazy-delta loops.  Exhaustion is an internal error, never a
/// verdict.  Effectively unbounded since con-leche task #330: `2^62`.
pub const DEFEQ_LOOP_FUEL: u64 = 4611686018427387904; // 2^62

/// con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction
/// Lean twin: `proof/ConRon/Arena/Core.lean:3859-3887 lazyDeltaReduction` — the
/// loop's literal acceleration, guarded on both sides being fvar-free; its
/// reduct restarts the comparison (`defeq`).  `None`: neither side folds.
pub fn lazy_delta_nat(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<Option<bool>, CheckError> {
    match lazy_fold_ok(pers, st, eager, a, b) {
        Err(e) => Err(e),
        Ok(nf) => {
            let ra = if nf {
                reduce_nat(pers, st, mode, eager, lane, fuel, fe, depth, a)
            } else {
                Ok(None)
            };
            match ra {
                Err(e) => Err(e),
                Ok(Some(a2)) => match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &a2, b) {
                    Err(e) => Err(e),
                    Ok(v) => Ok(Some(v)),
                },
                Ok(None) => {
                    let rb = if nf {
                        reduce_nat(pers, st, mode, eager, lane, fuel, fe, depth, b)
                    } else {
                        Ok(None)
                    };
                    match rb {
                        Err(e) => Err(e),
                        Ok(Some(b2)) => {
                            match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a, &b2) {
                                Err(e) => Err(e),
                                Ok(v) => Ok(Some(v)),
                            }
                        }
                        Ok(None) => Ok(None),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1663-1698 lazyDeltaReduction
/// con-leche: ConLeche/Cached/CoreC.lean:1782-1807 lazyDeltaReductionI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3859-3887 lazyDeltaReduction` — **the
/// lazy-delta loop** (the official kernel's `lazy_delta_reduction`): per
/// iteration the offset check, the literal acceleration, then one
/// `lazy_delta_step`, each unfolding one iteration on the loop's own budget
/// `n`.
pub fn lazy_delta_reduction(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<LazyResA, CheckError> {
    if n == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_DEFEQ_LOOP)))
    } else {
        match defeq_offset(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
            Err(e) => Err(e),
            Ok(Some(v)) => Ok(LazyResA::Verdict(v)),
            Ok(None) => match lazy_delta_nat(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
                Err(e) => Err(e),
                Ok(Some(v)) => Ok(LazyResA::Verdict(v)),
                Ok(None) => match lazy_delta_step(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
                    Err(e) => Err(e),
                    Ok(DeltaStepA::Cont(a2, b2)) => lazy_delta_reduction(
                        pers, st, mode, eager, lane, fuel, fe, depth, n - 1, &a2, &b2,
                    ),
                    Ok(DeltaStepA::Eq) => Ok(LazyResA::Verdict(true)),
                    Ok(DeltaStepA::Diff) => Ok(LazyResA::Verdict(false)),
                    Ok(DeltaStepA::Unknown) => Ok(LazyResA::Unknown(a.dup2(), b.dup2())),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1700-1718 lazyDeltaProjReduction
/// Lean twin: `proof/ConRon/Arena/Core.lean:3889-3909 lazyDeltaProjReduction` — the
/// projection loop's exit: the projection tried on both scrutinees and the
/// projected fields compared; failing that, the scrutinees themselves.
pub fn lazy_delta_proj_fields(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match reduce_proj_core(pers, st, mode, eager, lane, fuel, fe, depth, sn, i, a) {
        Err(e) => Err(e),
        Ok(Some(x)) => match reduce_proj_core(pers, st, mode, eager, lane, fuel, fe, depth, sn, i, b) {
            Err(e) => Err(e),
            Ok(Some(y)) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &x, &y),
            Ok(None) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a, b),
        },
        Ok(None) => knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a, b),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1700-1718 lazyDeltaProjReduction
/// con-leche: ConLeche/Cached/CoreC.lean:1809-1824 lazyDeltaProjReductionI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3889-3909 lazyDeltaProjReduction` —
/// **`a.i =?= b.i` by its scrutinees** (the official kernel's
/// `lazy_delta_proj_reduction`): lazy-delta steps on the two scrutinees, on
/// the loop's own budget `n`.
pub fn lazy_delta_proj_reduction(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    n: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if n == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PROJ_LOOP)))
    } else {
        match lazy_delta_step(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
            Err(e) => Err(e),
            Ok(DeltaStepA::Cont(a2, b2)) => lazy_delta_proj_reduction(
                pers, st, mode, eager, lane, fuel, fe, depth, sn, i, n - 1, &a2, &b2,
            ),
            Ok(DeltaStepA::Eq) => Ok(true),
            Ok(DeltaStepA::Diff) => {
                lazy_delta_proj_fields(pers, st, mode, eager, lane, fuel, fe, depth, sn, i, a, b)
            }
            Ok(DeltaStepA::Unknown) => {
                lazy_delta_proj_fields(pers, st, mode, eager, lane, fuel, fe, depth, sn, i, a, b)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1720-1729 defeqProjPair
/// con-leche: ConLeche/Cached/CoreC.lean:1826-1835 defeqProjPairI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3911-3924 defeqProjPair` — the proj/proj
/// check of `is_def_eq_core`: two projections at the same slot go through
/// `lazy_delta_proj_reduction` on their scrutinees.
pub fn defeq_proj_pair(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if a.tag() == ETAG_PROJ && b.tag() == ETAG_PROJ {
        match view(pers, st, a) {
            Err(e) => Err(e),
            Ok(va) => match view(pers, st, b) {
                Err(e) => Err(e),
                Ok(vb) => match (va, vb) {
                    (ENodeView::Proj(s1, i1, e1), ENodeView::Proj(s2, i2, e2)) => {
                        if s1.eq2(&s2) && i1 == i2 {
                            lazy_delta_proj_reduction(
                                pers, st, mode, eager, lane, fuel, fe, depth, &s1, i1,
                                DEFEQ_LOOP_FUEL, &e1, &e2,
                            )
                        } else {
                            Ok(false)
                        }
                    }
                    (_, _) => Ok(false),
                },
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1731-1798 defeqStuck
/// Lean twin: `proof/ConRon/Arena/Core.lean:3926-3995 defeqStuck` — the string arms,
/// merged with their mirror image: a string literal `s` against a unary
/// `String.ofList` application whose function part is `fo`, compared
/// shape-directed (`flipped`: the literal is on the right).  Any other literal
/// falls to `stuck_irrel`, which is the twin's inner match.
pub fn defeq_str_app(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    l: &Literal,
    fo: &EIdx,
    a2: &EIdx,
    b2: &EIdx,
    flipped: bool,
) -> Result<bool, CheckError> {
    match l {
        Literal::NatVal(_) => stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2),
        Literal::StrVal(s) => {
            let cs: Vec<u32> = expr::str_copy(s);
            if fo.tag() == ETAG_CONST {
                match view_const(pers, st, fo) {
                    None => fail_dangling_e(),
                    Some((c_o, us_o)) => match empty_levels(st) {
                        Err(e) => Err(e),
                        Ok(el) => match pin_string_of_list(st) {
                            Err(e) => Err(e),
                            Ok(sl) => match str_lit_stored(pers, st, fe) {
                                Err(e) => Err(e),
                                Ok(sup) => {
                                    if c_o.eq2(&sl) && us_o.eq2(&el) && sup {
                                        match str_lit_to_constructor(pers, st, &cs) {
                                            Err(e) => Err(e),
                                            Ok(ce) => {
                                                if flipped {
                                                    knot_defeq(
                                                        pers, st, mode, eager, lane, fuel, fe, depth,
                                                        a2, &ce,
                                                    )
                                                } else {
                                                    knot_defeq(
                                                        pers, st, mode, eager, lane, fuel, fe, depth,
                                                        &ce, b2,
                                                    )
                                                }
                                            }
                                        }
                                    } else {
                                        stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                                    }
                                }
                            },
                        },
                    },
                }
            } else {
                stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1731-1798 defeqStuck
/// Lean twin: `proof/ConRon/Arena/Core.lean:3926-3995 defeqStuck` — stuck
/// applications: **spine-wise** congruence (official's `is_def_eq_app`), never
/// a recursion on the partial applications.
pub fn defeq_apps(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match get_app_args(pers, st, CORE_WALK_FUEL, a2) {
        Err(e) => Err(e),
        Ok(aa) => match get_app_args(pers, st, CORE_WALK_FUEL, b2) {
            Err(e) => Err(e),
            Ok(bb) => {
                if aa.len() == bb.len() {
                    match get_app_fn(pers, st, CORE_WALK_FUEL, a2) {
                        Err(e) => Err(e),
                        Ok(fa) => match get_app_fn(pers, st, CORE_WALK_FUEL, b2) {
                            Err(e) => Err(e),
                            Ok(fb) => {
                                match knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &fa, &fb)
                                {
                                    Err(e) => Err(e),
                                    Ok(false) => stuck_irrel(
                                        pers, st, mode, eager, lane, fuel, fe, depth, a2, b2,
                                    ),
                                    Ok(true) => {
                                        match def_eq_list(
                                            pers, st, mode, eager, lane, fuel, fe, depth, &aa, &bb, 0,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(true) => Ok(true),
                                            Ok(false) => stuck_irrel(
                                                pers, st, mode, eager, lane, fuel, fe, depth, a2, b2,
                                            ),
                                        }
                                    }
                                }
                            }
                        },
                    }
                } else {
                    stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1731-1798 defeqStuck
/// con-leche: ConLeche/Cached/CoreC.lean:1837-1885 defeqStuckI
/// Lean twin: `proof/ConRon/Arena/Core.lean:3926-3995 defeqStuck` — **the stuck
/// comparison** (the tail of the official kernel's `is_def_eq_core`): a string
/// literal against `String.ofList`, the same free variable, the same constant
/// at equivalent levels, the application spine, η on a one-sided λ; every
/// failing arm ends in `stuck_irrel`.  The twin's two string arms are merged
/// (`defeq_str_app`).
pub fn defeq_stuck(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match view(pers, st, a2) {
        Err(e) => Err(e),
        Ok(va) => match view(pers, st, b2) {
            Err(e) => Err(e),
            Ok(vb) => match (va, vb) {
                (ENodeView::Lit(l), ENodeView::App(fo, _)) => {
                    defeq_str_app(pers, st, mode, eager, lane, fuel, fe, depth, &l, &fo, a2, b2, false)
                }
                (ENodeView::App(fo, _), ENodeView::Lit(l)) => {
                    defeq_str_app(pers, st, mode, eager, lane, fuel, fe, depth, &l, &fo, a2, b2, true)
                }
                (ENodeView::FVar(i, _), ENodeView::FVar(j, _)) => {
                    if i == j {
                        Ok(true)
                    } else {
                        stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                    }
                }
                (ENodeView::Const(n, us), ENodeView::Const(n2, us2)) => {
                    if n.eq2(&n2) {
                        match lvls_eq(pers, st, &us, &us2) {
                            Err(e) => Err(e),
                            Ok(o) => match lift_fueled(o) {
                                Err(e) => Err(e),
                                Ok(true) => Ok(true),
                                Ok(false) => {
                                    stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                                }
                            },
                        }
                    } else {
                        stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                    }
                }
                (ENodeView::App(_, _), ENodeView::App(_, _)) => {
                    defeq_apps(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2)
                }
                (ENodeView::Lam(ty1, body1), _) => {
                    match eta_cert(pers, st, mode, eager, lane, fuel, fe, depth, &ty1, &body1, b2)
                    {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2),
                    }
                }
                (_, ENodeView::Lam(ty2, body2)) => {
                    match eta_cert(pers, st, mode, eager, lane, fuel, fe, depth, &ty2, &body2, a2)
                    {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2),
                    }
                }
                (_, _) => stuck_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1800-1858 defeqBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:3997-4035 defeqBody` — the tail of the
/// body after the lazy-delta loop came back undecided: the proj/proj check,
/// then the FULL `whnfCore` of both sides (only when one is projection-headed)
/// and, if either changed, a restart; else the stuck comparison.
pub fn defeq_after_lazy(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a1: &EIdx,
    b1: &EIdx,
) -> Result<bool, CheckError> {
    match defeq_proj_pair(pers, st, mode, eager, lane, fuel, fe, depth, a1, b1) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => match head_is_proj(pers, st, a1) {
            Err(e) => Err(e),
            Ok(pa) => match head_is_proj(pers, st, b1) {
                Err(e) => Err(e),
                Ok(pb) => {
                    if !pa && !pb {
                        defeq_stuck(pers, st, mode, eager, lane, fuel, fe, depth, a1, b1)
                    } else {
                        match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, false, depth, a1) {
                            Err(e) => Err(e),
                            Ok(a2) => {
                                match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, false, depth, b1)
                                {
                                    Err(e) => Err(e),
                                    Ok(b2) => {
                                        if a2.eq2(a1) && b2.eq2(b1) {
                                            defeq_stuck(pers, st, mode, eager, lane, fuel, fe, depth, a1, b1)
                                        } else {
                                            knot_defeq(pers, st, mode, eager, lane, fuel, fe, depth, &a2, &b2)
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1800-1858 defeqBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:3997-4035 defeqBody` — the body after the
/// CHEAP head normalization of both sides: `quick_defeq` on the reducts, the
/// lazy-delta loop, and `defeq_after_lazy`.  (Proof irrelevance is no longer
/// here: since con-leche task #333 it runs on the UNREDUCED pair, in
/// `defeq_unreduced`.)
pub fn defeq_after_whnf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match quick_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a2, b2) {
        Err(e) => Err(e),
        Ok(Some(v)) => Ok(v),
        Ok(None) => {
            match lazy_delta_reduction(
                pers, st, mode, eager, lane, fuel, fe, depth, DEFEQ_LOOP_FUEL, a2, b2,
            ) {
                Err(e) => Err(e),
                Ok(LazyResA::Verdict(v)) => Ok(v),
                Ok(LazyResA::Unknown(a3, b3)) => {
                    defeq_after_lazy(pers, st, mode, eager, lane, fuel, fe, depth, &a3, &b3)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1800-1858 defeqBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:3997-4035 defeqBody` — the body
/// past the `Bool.true` shortcut (con-leche task #333): `quick_defeq` and proof
/// irrelevance on the UNREDUCED pair, so that a proof is never head-normalized
/// to be compared; then the CHEAP head normalization of both sides and
/// `defeq_after_whnf`.
pub fn defeq_unreduced(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match quick_defeq(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
        Err(e) => Err(e),
        Ok(Some(v)) => Ok(v),
        Ok(None) => match prop_irrel(pers, st, mode, eager, lane, fuel, fe, depth, a, b) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => {
                match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, a) {
                    Err(e) => Err(e),
                    Ok(a2) => {
                        match knot_whnf_core(pers, st, mode, eager, lane, fuel, fe, true, depth, b) {
                            Err(e) => Err(e),
                            Ok(b2) => defeq_after_whnf(
                                pers, st, mode, eager, lane, fuel, fe, depth, &a2, &b2,
                            ),
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1800-1858 defeqBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:3997-4035 defeqBody` — **the
/// definitional-equality body** (the official kernel's `is_def_eq_core`,
/// clause for clause except con-leche task #333's reordering): the syntactic
/// fast path; the `Bool.true` shortcut; `quick_defeq` and proof irrelevance on
/// the UNREDUCED sides; the CHEAP head normalization of both sides; then
/// `defeq_after_whnf`.
pub fn defeq_body(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if a.eq2(b) {
        Ok(true)
    } else {
        match is_bool_true(pers, st, b) {
            Err(e) => Err(e),
            Ok(ibt) => match has_fvar_fast(pers, st, CORE_WALK_FUEL, a) {
                Err(e) => Err(e),
                Ok(hf) => {
                    // the eager flag fires the shortcut with free
                    // variables present (official `m_eager_reduce`)
                    let sc = if ibt && (eager || !hf) {
                        bool_true_shortcut(pers, st, mode, eager, lane, fuel, fe, depth, a)
                    } else {
                        Ok(false)
                    };
                    match sc {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => {
                            defeq_unreduced(pers, st, mode, eager, lane, fuel, fe, depth, a, b)
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:318-322 peelFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:3149-3153 peelFuel` — the fuel of
/// the two telescope peels, con-leche's number verbatim. Exhaustion is not an
/// error: the loop falls through to its leaf phase with the binders peeled so
/// far, which is con-leche's own `| 0, t, k, fvs, stk => …LeafI` clause.
pub const PEEL_FUEL: u64 = 16777216;

// ---------------------------------------------------------------------------
// The knot (`Core.lean:2721-2859`)
//
// con-leche's `Core.lean`:2897-2936 with the memo probes of
// `ConLeche/Cached/CoreC.lean`:1877-1906 inlined in the slots (the twin's
// deviation 6).  The six slots are six plain mutually recursive functions
// here (the module note's deviation 1), each taking the `lane` that says which
// of the arena's two knots it belongs to.  The eager slot (`knot_defeq_e`)
// runs the knot one level down at `eager` true, so `mode` and `eager` are
// the record's other component.
//
// The twin's detach-before-update (lesson 14) and `@[noinline]` (lesson 15)
// have no Rust counterpart: `&mut` IS the unique reference the detaching
// manufactures, and `@[noinline]` is a Lean reference-count concern.  Each
// recorder is a plain insert, as con-leche's `memoEI`/`memoBI` are: the cap
// they once carried was removed by task #115 (`arena::core_state`'s module
// note).
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1025-1074 whnfCoreBody
/// con-leche: ConLeche/Cached/CoreC.lean:236-244 whnfCoreEasy
/// Lean twin: `proof/ConRon/Arena/Core.lean:2487-2501 whnfCoreStuckTag` — **the
/// head kinds `whnfCoreBody` answers with its own argument**, read off the
/// handle's constructor tag without decoding the node.
///
/// `whnfCoreBody`'s first six clauses are `pure e` (`sort`, `fvar`, `forallE`,
/// `lam`, `const`, `lit`), exactly `whnfCoreEasy`'s kinds; only `app` and
/// `proj` reduce, and `letE`/`bvar` fail.  The knot tests them before the memo
/// in both modes, as the cited one does.  The knot's slot therefore spends a memo probe, a `view` decode, a
/// `dup` and a memo insert to learn the tag it already had in its hand.  On
/// the Mathlib 25 % prefix that is **61.25 M of the 164.95 M `whnfCore` misses
/// (37.1 %) and 9.57 M of the 33.85 M hits (28.3 %)**, and those 61.25 M rows
/// were also 37 % of the biggest per-declaration table.
///
/// The answer is `e` ITSELF, not a handle denoting the same term, so the
/// clause is handle-identical and the memo it bypasses could only ever have
/// answered `e` too.
pub fn whnf_core_stuck_tag(e: &EIdx) -> bool {
    let t: u32 = e.tag();
    if t == ETAG_APP {
        false
    } else if t == ETAG_PROJ {
        false
    } else if t == ETAG_LET_E {
        false
    } else if t == ETAG_BVAR {
        false
    } else {
        true
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1123-1143 whnfStep
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove crates/con-ron-core/src/arena/core.rs_refines, then delete this line
/// con-leche: ConLeche/Cached/CoreC.lean:318-324 whnfEasy
/// Lean twin: `proof/ConRon/Arena/Core.lean:2784-2787 whnfBody` — **the head
/// kinds `whnfBody` answers with its own argument**, again off the tag alone.
/// `whnfEasy`'s kinds plus `lam` (deviation below).
///
/// One iteration of the reduction loop is `whnfCore`, then `reduceNat`, then
/// `unfoldDefinition`, and it stops when the last two decline.  At `sort`,
/// `fvar`, `lam`, `forallE` and `lit`: `whnfCore` is the identity (above);
/// `reduceNat` matches only an `app`, so it is `none`; and `unfoldDefinition`
/// takes the head of the application spine, which for a non-`app` is the node
/// itself, and matches only a `const`, so it is `none` too.  The loop returns
/// its argument at the first step.
///
/// Deviation: `whnfEasy` leaves `lam` to the memo, as official `whnf` does;
/// the memo could only answer a `lam` with itself, so this test returns that
/// answer before the probe.
///
/// **`const` is NOT in this set** — that is exactly the node
/// `unfoldDefinition` unfolds — and `app`/`proj` are not, and `letE`/`bvar`
/// must still reach `whnfCore`'s failure.  On the prefix the five kinds are
/// **23.16 M of the 28.08 M `whnf` misses (82.5 %) and 11.07 M of the 12.41 M
/// hits (89.3 %)**.
pub fn whnf_stuck_tag(e: &EIdx) -> bool {
    let t: u32 = e.tag();
    if t == ETAG_SORT {
        true
    } else if t == ETAG_FVAR {
        true
    } else if t == ETAG_LAM {
        true
    } else if t == ETAG_FORALL_E {
        true
    } else if t == ETAG_LIT {
        true
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4045-4052 whnfCoreSet` — record a
/// `whnfCore` answer.
pub fn whnf_core_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    let _ = st.caches.whnf_core_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4054-4061 whnfCoreCheapSet` — record
/// a CHEAP-mode `whnfCore` answer, in the cheap mode's own table.
pub fn whnf_core_cheap_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    let _ = st.caches.whnf_core_cheap_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4063-4069 whnfSet` — record a
/// `whnf` answer.
pub fn whnf_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    let _ = st.caches.whnf_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4071-4077 inferSet` — record a
/// full-grade `infer` answer.
pub fn infer_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    let _ = st.caches.infer_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:332-345 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4079-4086 inferIOSet` — record an
/// io-grade `infer` answer, in the io grade's OWN table (con-leche's task #170
/// memo ruling).
pub fn infer_io_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    let _ = st.caches.infer_io_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:346-359 memoBI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4088-4095 defeqSet` — record a
/// `defeq` verdict at the ORDERED pair, both signs (con-leche's `defeqC` stores
/// the `Bool` result `r`, which is what makes a negative memo sound).
pub fn defeq_set(st: &mut AState, a: &EIdx, b: &EIdx, r: bool) {
    let k: EIdxPair = eidx_pair(a, b);
    let _ = st.caches.defeq_c.insert(k, r);
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the `whnfCoreC`
/// probe, over a *shared* state borrow so the map's borrow ends before the
/// miss branch writes (`con_ron_core::cached::core_c::whnf_core_probe`'s
/// reason, task #14's rule).
pub fn whnf_core_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.whnf_core_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the
/// `whnfCoreCheapC` probe (the cheap mode's own table).
pub fn whnf_core_cheap_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.whnf_core_cheap_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the `whnfC` probe.
pub fn whnf_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.whnf_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the `inferC` probe.
pub fn infer_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.infer_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:326-344 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the `inferIOC`
/// probe.
pub fn infer_io_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.infer_io_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:346-359 memoBI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — the `defeqC` probe
/// at the ORDERED pair.
pub fn defeq_probe(st: &AState, k: &EIdxPair) -> Option<bool> {
    match st.caches.defeq_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::knot_whnf_core_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — **the
/// `whnfCore` slot.**  At `LANE_FULL` and `LANE_IO` it is the memoized body
/// (`coreKnotIO`'s slot *is* the full knot's, at the same fuel).
pub fn knot_whnf_core(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    _lane: u32,
    fuel: u64,
    fe: &IFEnv,
    cheap: bool,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF_CORE)))
    } else if whnf_core_stuck_tag(e) {
        Ok(e.dup2())
    } else if cheap {
        match whnf_core_cheap_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_core_body(pers, st, mode, eager, LANE_FULL, fuel - 1, fe, true, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    whnf_core_cheap_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    } else {
        match whnf_core_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_core_body(pers, st, mode, eager, LANE_FULL, fuel - 1, fe, false, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    whnf_core_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// con-leche: CHANGED since eb2c5939 — re-port, re-test, re-prove core::knot_whnf_refines, then delete this line
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — the `whnf` slot.
pub fn knot_whnf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    _lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF)))
    } else if whnf_stuck_tag(e) {
        Ok(e.dup2())
    } else {
        match whnf_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_body(pers, st, mode, eager, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    whnf_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// con-leche: ConLeche/Kernel/CoreIO.lean:44-66 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — **the `infer`
/// slot.**  At `LANE_FULL` it is `inferBody` under `inferC`; at `LANE_IO` it is
/// `inferBodyIO` tied to the io knot, unmemoized (the leaf lane).
pub fn knot_infer(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INFER)))
    } else if lane == LANE_IO {
        infer_body_io(pers, st, mode, eager, lane, false, fuel - 1, fe, depth, e)
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body(pers, st, mode, eager, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    infer_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// con-leche: ConLeche/Kernel/CoreIO.lean:44-66 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — **the `inferIO`
/// slot.**  At `LANE_FULL` it is the io body at every mode (con-leche task
/// #346: official's `infer_only`) under its own table (`inferIOC`): a hit in
/// one grade never serves the other (DESIGN.md §8.3, lesson 9).  `LANE_IO`'s
/// is its `infer` slot again.
pub fn knot_infer_io(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INFER)))
    } else if lane == LANE_IO {
        infer_body_io(pers, st, mode, eager, lane, false, fuel - 1, fe, depth, e)
    } else {
        match infer_io_probe(st, e) {
            Some(r) => Ok(r),
            None => {
                match infer_body_io(pers, st, mode, eager, LANE_FULL, true, fuel - 1, fe, depth, e) {
                    Err(er) => Err(er),
                    Ok(r) => {
                        infer_io_set(st, e, &r);
                        Ok(r)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:138-144 CoreFns.ioView
/// con-leche: ConLeche/Cached/CoreC.lean:55-59 CoreFnsI.ioView
/// Lean twin: `proof/ConRon/Arena/Core.lean:270-275 CoreFnsA.ioView` — the knot
/// slot a body's `r.infer` call resolves to: the `infer` slot under the plain
/// record, the `inferIO` slot under its io view.  **This function IS the
/// `ioView` substitution in the port** (`con_ron_core::cached::core_c::
/// infer_at_i`'s own words): the knot is plain functions, so there is no
/// record whose `infer` field can be rebound.
pub fn knot_infer_at(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if io {
        knot_infer_io(pers, st, mode, eager, lane, fuel, fe, depth, e)
    } else {
        knot_infer(pers, st, mode, eager, lane, fuel, fe, depth, e)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:34-51 coreKnotIO` — the `defeq`
/// slot, memoized at the ORDERED pair.
pub fn knot_defeq(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    _lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_DEFEQ)))
    } else {
        let k: EIdxPair = eidx_pair(a, b);
        match defeq_probe(st, &k) {
            Some(r) => Ok(r),
            None => match defeq_body(pers, st, mode, eager, LANE_FULL, fuel - 1, fe, depth, a, b) {
                Err(er) => Err(er),
                Ok(r) => {
                    defeq_set(st, a, b, r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:514-526 CState.enterEager
/// con-leche: ConLeche/Cached/StateC.lean:510-512 CState.modeMemos
/// Lean twin: `proof/ConRon/Arena/Core.lean:4097-4112 enterEager` — **enter the
/// eager tower.**  With the flag clear (`eager` false) the plain memos move out
/// (returned), the stored eager ones move into the six fields, and the eager
/// slot is left empty (`ModeMemos::empty` allocates nothing).  Every table
/// moves, none is copied, so the comparison that follows mutates the eager
/// tables in place.  With the flag set the six fields already hold the eager
/// set: nothing moves.
pub fn enter_eager(st: &mut AState, eager: bool) -> Option<ModeMemos> {
    if eager {
        None
    } else {
        let em: ModeMemos = core::mem::replace(&mut st.caches.eager_memos, ModeMemos::empty());
        Some(ModeMemos {
            whnf_core_c: core::mem::replace(&mut st.caches.whnf_core_c, em.whnf_core_c),
            whnf_core_cheap_c: core::mem::replace(
                &mut st.caches.whnf_core_cheap_c,
                em.whnf_core_cheap_c,
            ),
            whnf_c: core::mem::replace(&mut st.caches.whnf_c, em.whnf_c),
            infer_c: core::mem::replace(&mut st.caches.infer_c, em.infer_c),
            infer_io_c: core::mem::replace(&mut st.caches.infer_io_c, em.infer_io_c),
            defeq_c: core::mem::replace(&mut st.caches.defeq_c, em.defeq_c),
        })
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:528-538 CState.leaveEager
/// con-leche: ConLeche/Cached/StateC.lean:510-512 CState.modeMemos
/// Lean twin: `proof/ConRon/Arena/Core.lean:4114-4128 leaveEager` — **leave the
/// eager tower**: the six fields (now the eager tower's, with what the
/// comparison added) are stored back as the eager set, and the plain memos
/// `saved` return to the six fields; nothing moves when `enter_eager` moved
/// nothing.
pub fn leave_eager(st: &mut AState, saved: Option<ModeMemos>) {
    match saved {
        None => {}
        Some(mm) => {
            let em: ModeMemos = ModeMemos {
                whnf_core_c: core::mem::replace(&mut st.caches.whnf_core_c, mm.whnf_core_c),
                whnf_core_cheap_c: core::mem::replace(
                    &mut st.caches.whnf_core_cheap_c,
                    mm.whnf_core_cheap_c,
                ),
                whnf_c: core::mem::replace(&mut st.caches.whnf_c, mm.whnf_c),
                infer_c: core::mem::replace(&mut st.caches.infer_c, mm.infer_c),
                infer_io_c: core::mem::replace(&mut st.caches.infer_io_c, mm.infer_io_c),
                defeq_c: core::mem::replace(&mut st.caches.defeq_c, mm.defeq_c),
            };
            st.caches.eager_memos = em;
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1862-1897 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1767-1788 coreKnotI
/// con-leche: ConLeche/Cached/StateC.lean:540-558 withEagerMemos
/// Lean twin: `proof/ConRon/Arena/Core.lean:4130-4220 coreKnot` — **the eager slot**:
/// definitional equality in the eager tower, `defeq_body` at `eager` true
/// one level down (the flag holds for the comparison and everything it calls,
/// as official's `flet` scope does), memoized at the ordered pair in the
/// eager tower's own tables: `enter_eager` swaps the stored eager set in,
/// `leave_eager` stores it back with what the comparison added and restores
/// the plain memos (on both exits of the memo: con-leche's
/// `withEagerMemos mode (memoBI …)` with the bind pushed into the probe's
/// two branches).  An eager entry never serves a plain query, nor the other
/// way round; the mode-independent caches are shared.  A nested eager
/// comparison (`eager` already set) runs on the eager set as it is.  On
/// an error the plain memos are not put back, as con-leche's (the state is
/// not read after an error).
pub fn knot_defeq_e(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    eager: bool,
    _lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_DEFEQ)))
    } else {
        let saved: Option<ModeMemos> = enter_eager(st, eager);
        let k: EIdxPair = eidx_pair(a, b);
        match defeq_probe(st, &k) {
            Some(r) => {
                leave_eager(st, saved);
                Ok(r)
            }
            None => {
                match defeq_body(pers, st, mode, true, LANE_FULL, fuel - 1, fe, depth, a, b) {
                    Err(er) => Err(er),
                    Ok(r) => {
                        defeq_set(st, a, b, r);
                        leave_eager(st, saved);
                        Ok(r)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1899-1918 checkFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:4222-4228 checkFuel` — the shared fuel
/// for the checker core, counted in knot levels.  **Effectively unbounded**
/// (`2^62`, as `WHNF_CORE_LOOP_FUEL`): the fuel exists so that the knot is a
/// structural recursion the proofs can induct over, and running out of it is
/// an internal error (exit 3), never an accept.  Each knot level is native
/// recursion, so what bounds the depth is the native stack: every checker
/// thread is spawned with `STACK_BYTES` (1 GiB, `crates/con-ron`'s
/// `driver.rs`, the Lean runtime's default con-leche relies on), and a
/// recursion deeper than it holds hits the thread's guard page, which the
/// Rust runtime turns into `thread … has overflowed its stack` and an abort
/// (exit 134) — an error, never an
/// accept.
pub const CHECK_FUEL: u64 = 4611686018427387904; // 2^62

// ---------------------------------------------------------------------------
// The fueled entry points (`Core.lean:2866-2923`)
//
// `ConLeche/Kernel/TypeChecker.lean`, whose seven (T) declarations live here
// because the arena has ONE knot (the twin's deviation 5): con-leche's
// `pureFns` is `coreKnot mode env id` at `CheckM` with no memo, and the
// arena's `coreKnot` already carries the memos, so `pureFnsA` is the same
// expression over handles.  `pureFnsA` itself has no Rust counterpart — a
// record of functions is what §3.4 rules out — and its place is taken by
// `LANE_FULL`, which every entry below passes.  `whnfCore` and `inferTypeIO`
// have no entry here: every caller goes to `knot_whnf_core` /
// `knot_infer_io` directly, as the twin's callers go to the knot.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TypeChecker.lean:33-35 whnf
/// Lean twin: `proof/ConRon/Arena/Core.lean:4246-4250 whnf` — the full
/// reduction loop (fueled).
pub fn whnf(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_whnf(pers, st, mode, false, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:37-40 inferTypeCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:4252-4256 inferTypeCore` —
/// full-grade type inference (fueled): the declaration front door's entry.
pub fn infer_type_core(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_infer(pers, st, mode, false, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:48-50 isDefEqCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:4258-4262 isDefEqCore` —
/// definitional equality (fueled).
pub fn is_def_eq_core(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    knot_defeq(pers, st, mode, false, LANE_FULL, fuel, fe, depth, a, b)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:52-54 ensureSortCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:4264-4268 ensureSortCore` —
/// `ensureSort` over the knot (fueled).
pub fn ensure_sort_core(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<LIdx, CheckError> {
    ensure_sort(pers, st, mode, false, LANE_FULL, fuel, fe, depth, e)
}

// ---------------------------------------------------------------------------
// The per-declaration bracket (`Core.lean:2925-2958`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:499-506 CState.flushed
/// Lean twin: `proof/ConRon/Arena/Core.lean:4276-4282 flushCaches` — **what
/// the per-declaration bracket does to the caches**: it drops them whole,
/// which is con-leche's own `flushC`, the operation its driver runs at exactly
/// this point.
///
/// Task #97-P4c ported DESIGN.md §8.3's survivor policy instead — keep the
/// rows whose key AND value are persistent — which is sound and strictly more
/// caching; task #97f measured what it costs (`filter` is `O(table)` and the
/// survivors accumulate, so the fold pays `O(declarations × surviving rows)`:
/// 16 % of `Init`'s first 4 380 declarations' cycles, 213 s → 124 s).  The
/// twin's `Caches.dropScratchEntries` stays as the SPECIFICATION of a
/// surviving row, and so does `Caches::drop_scratch_entries` below it with
/// its eleven journals — P3 needs it to state that flushing is sound.
pub fn flush_caches(st: &mut AState) {
    st.caches.reset();
}

/// con-leche: none — **a job's bracket, closed** (DESIGN.md §8.3)
/// Lean twin: `proof/ConRon/Arena/Core.lean:4284-4292 dropScratch` —
/// the twin's `dropScratch` on a store that STAYS frozen (task #98-FREEZE): the
/// caches flushed and the scratch tiers emptied, the flag untouched.  A
/// worker's store is frozen for its whole life, so between two jobs it is
/// frozen with an empty scratch tier where the twin's is scratch-off; nothing
/// is interned there.
pub fn leave_record(st: &mut AState) {
    flush_caches(st);
    st.store.clear_scratch();
}

/// con-leche: none — **a job's bracket, opened** (DESIGN.md §8.3)
/// Lean twin: `proof/ConRon/Arena/Core.lean:4294-4301 enterScratch` —
/// the twin's `enterScratch` on an already frozen store (task #98-FREEZE): the
/// memos cleared and the scratch tiers emptied, the flag untouched.
pub fn enter_record(st: &mut AState) {
    st.memos.reset();
    st.store.clear_scratch();
}

// ---------------------------------------------------------------------------
// The differential test (`proof/ConRon/Arena/CoreTest.lean`)
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    // Task #97-SWAP: this module's tests were a DIFFERENTIAL harness — every
    // one ran the subject here and `con-ron-core`'s `Expr`-tree twin of it on
    // the same fixture and compared the two outcomes, which is how the arena
    // was brought up beside the shipping checker (DESIGN.md §8.6).  The swap
    // deleted the twin: this IS the checker now, and there is nothing left to
    // compare against in-process.  `scripts/diff-e2e.sh` is the differential
    // test from here — 383 fixtures through the whole binary, against
    // con-leche's own verdicts — and it is a gate, not a unit test.
}
