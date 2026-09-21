//! `arena::core` — the checker core of (C), over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Core.lean`, which is
//! `ConLeche/Kernel/Core.lean` clause for clause over handles: the six bodies
//! (`whnf_core`, `whnf`, `infer`, `infer_io`, `defeq`, `annotate`), the
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
//!    thing a body still has to be told, because the arena has three knots:
//!    `coreKnot` (LANE_FULL, memoized), `coreKnotGated` (LANE_GATED,
//!    `arena::core_gated`, no memo) and `coreKnotIO` (LANE_IO,
//!    `arena::core_io`, no memo).  It is told as a `lane: u32`, threaded
//!    beside `mode` through every function whose twin takes `r`.  That is
//!    defunctionalization of the twin's one higher-order argument, and it is
//!    the same move §3.4 already asks for at
//!    `expr_ops::rename_consts_go`'s `f : NIdx → NIdx`.
//!
//!    `CoreFnsA.ioView` — `{ r with infer := r.inferIO }`, the *one* place
//!    the record is rebound — is the extra `io: bool` of `infer_body_io`,
//!    exactly as `con_ron_core::cached::core_c::infer_at_i` spells it ("this
//!    function *is* the `ioView` substitution in the port").  No other body
//!    or helper calls `r.infer`, so no other one carries it.
//! 2. **A continuation argument is the loop's step budget.**  `whnfStep`
//!    takes `k : EIdx → AM EIdx` and `defeqStep` takes `k : Bool → EIdx →
//!    EIdx → AM Bool`; both are only ever applied to the loop one step down,
//!    so `k x` is `whnf_loop(…, n, x)` and `k pi x y` is `defeq_loop(…, n, pi,
//!    x, y)`.  `con_ron_core::cached::core_c::whnf_step_i` does the same, for
//!    the same reason.
//!
//! `coreKnot`'s `wrap : CoreFnsA → CoreFnsA` parameter is dropped: `pureFnsA`
//! is `coreKnot mode fe id` and `id` is its only instantiation in the whole
//! twin.
//!
//! ## Three smaller shapes worth naming
//!
//! * **`defeqStep`'s body is three functions here**, as
//!   `con_ron_core::cached::core_c`'s is (`defeq_step` → `defeq_after_whnf`
//!   → `defeq_struct`): the twin is one `def` whose last arm is a sixteen-way
//!   match on a PAIR of views, and inlining the lazy-delta stage into it
//!   would nest twenty deep.  Every cited clause is still in the twin's
//!   order; the split points are the twin's own `let`-boundaries.
//! * **The twin's `match ← view a', ← view b'` is `match (va, vb)`**, arm for
//!   arm in the twin's order, with the twin's two `(lit, app)` arms merged
//!   into one that dispatches on the literal's kind — the scrutinee pair is
//!   fixed, so merging two arms that differ only in the literal's
//!   constructor changes nothing (the twin's fall-through for the other
//!   constructor is `stuckIrrel`, which is what the merged arm does).
//! * **Messages are `con_ron_core`'s**, code point for code point, with the
//!   twin's interpolation dropped (DESIGN.md §3.1: message strings need not
//!   match a theorem, and matching the *shipping port's* is what lets the
//!   differential test compare whole outcomes including error text).

use crate::arena::core_gated::whnf_core_body_gated;
use crate::arena::core_state::{
    eidx_pair, lidx_pair,
    lsidx_pair, nls_key, nnls_key, EIdxPair, LIdxPair, LsIdxPair, NLsKey, NNLsKey,
    CACHE_CAP,
};
use crate::arena::env;
use crate::arena::env::{
    IConstantInfo, IConstantVal, IFEnv, IIndCaps, IProjEntry, IRecRule, IRecRuleFire,
};
use crate::arena::expr_ops::{
    abstract1_fast, abstract_range_fast, bvar_b, cons_eidx, get_app_args, get_app_fn,
    has_fvar_fast, instantiate1_fast, instantiate_list_fast, inst_lp_fast, inst_spine,
    lam_pw, leaf_guard, loose_bvars_bounded_fast, mk_app_n, mk_app_n_from, pi_result,
    rec_rule_plain, strip_pis,
    take_eidx, wscoped_b_fast,
};
use crate::arena::handle::{
    EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR, ETAG_LAM,
    ETAG_LET_E,
    ETAG_LIT, ETAG_PROJ, ETAG_SORT,
};
use crate::arena::monad::{
    fail, intern_e, intern_l_node, intern_ls_node, intern_n_node, intern_level, intern_name,
    read_level, read_levels, read_name, read_names, view, view_app, view_bind, view_ls, view_ls_len,
    AState, fail_dangling_e, fail_dangling_ls,
};
use crate::arena::prop_read::{is_proof_fast, not_proof_fast, proof_pw, type_sort_pw};
use crate::arena::store::{ENodeView, LNodeView, NNodeView};
use crate::arena::pins::{pin_and, pin_reserved, pin_bool, pin_bool_false, pin_bool_true, pin_char, pin_char_of_nat, pin_empty_levels, pin_list, pin_list_cons, pin_list_nil, pin_nat, pin_nat_add, pin_nat_beq, pin_nat_ble, pin_nat_div, pin_nat_gcd, pin_nat_land, pin_nat_lor, pin_nat_mod, pin_nat_mul, pin_nat_pow, pin_nat_pred, pin_nat_shift_left, pin_nat_shift_right, pin_nat_sub, pin_nat_succ, pin_nat_xor, pin_nat_zero, pin_punit, pin_punit_rec, pin_sorry_ax, pin_sort_one, pin_string, pin_string_of_list, pin_zero_level};
use con_ron_core::kernel::core_k;
use con_ron_core::kernel::core_types::{code_points, code_points_from, CheckError};
use con_ron_core::kernel::env::{CheckMode, ReducibilityHint};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{BinderMeta, Literal};
use con_ron_core::kernel::expr_ops::sub_nat;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::{Dup, Eq2};
use con_ron_core::ron::nat;
use con_ron_core::ron::nat::Nat;
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
/// `"fuel exhausted: level comparison"`, as code points.
pub const M_FUEL_LEVEL_CMP: [u32; 32] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 101,
    118, 101, 108, 32, 99, 111, 109, 112, 97, 114, 105, 115, 111, 110
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
/// `"shift amount beyond u64"`, as code points.
pub const M_SHIFT: [u32; 23] = [
    115, 104, 105, 102, 116, 32, 97, 109, 111, 117, 110, 116, 32, 98, 101, 121, 111, 110,
    100, 32, 117, 54, 52
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"native Nat computation on literals"`, as code points.
pub const M_NATIVE_NAT: [u32; 34] = [
    110, 97, 116, 105, 118, 101, 32, 78, 97, 116, 32, 99, 111, 109, 112, 117, 116, 97, 116,
    105, 111, 110, 32, 111, 110, 32, 108, 105, 116, 101, 114, 97, 108, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"sort-annotation mismatch (eta)"`, as code points.
pub const M_ETA: [u32; 30] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 101, 116, 97, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"iota reduction over a nested auxiliary recursor rule"`, as code points.
pub const M_NESTED_RULE: [u32; 52] = [
    105, 111, 116, 97, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 111, 118, 101,
    114, 32, 97, 32, 110, 101, 115, 116, 101, 100, 32, 97, 117, 120, 105, 108, 105, 97,
    114, 121, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 117, 108, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"whnfCore: `let` in an annotated expression"`, as code points.
pub const M_LET_WHNF: [u32; 42] = [
    119, 104, 110, 102, 67, 111, 114, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105, 110, 32,
    97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112, 114, 101,
    115, 115, 105, 111, 110
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"whnf beyond the supported fragment"`, as code points.
pub const M_BVAR_WHNF: [u32; 34] = [
    119, 104, 110, 102, 32, 98, 101, 121, 111, 110, 100, 32, 116, 104, 101, 32, 115, 117,
    112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109, 101, 110, 116
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
/// `"sort-annotation mismatch (forall-cod)"`, as code points.
pub const M_COD: [u32; 37] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 102, 111, 114, 97, 108, 108, 45, 99, 111, 100, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"sort-annotation mismatch (lam-cod-chain)"`, as code points.
pub const M_CHAIN: [u32; 40] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 99, 104, 97,
    105, 110, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"sort-annotation mismatch (lam-cod-leaf)"`, as code points.
pub const M_LEAF: [u32; 39] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 108, 101, 97,
    102, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"sort-annotation mismatch (defeq-forall)"`, as code points.
pub const M_DEFEQ_PI: [u32; 39] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 102, 111, 114, 97,
    108, 108, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"sort-annotation mismatch (defeq-lam)"`, as code points.
pub const M_DEFEQ_LAM: [u32; 36] = [
    115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
    115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 108, 97, 109, 41
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection table entry used as a constant"`, as code points.
pub const M_TOWER: [u32; 41] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 101,
    110, 116, 114, 121, 32, 117, 115, 101, 100, 32, 97, 115, 32, 97, 32, 99, 111, 110, 115,
    116, 97, 110, 116
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"incorrect number of universe levels"`, as code points.
pub const M_LEVELS: [u32; 35] = [
    105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
    102, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"inferType: `let` in an annotated expression"`, as code points.
pub const M_LET_INFER: [u32; 43] = [
    105, 110, 102, 101, 114, 84, 121, 112, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105,
    110, 32, 97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112,
    114, 101, 115, 115, 105, 111, 110
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
/// `"projection on a non-structure-like type"`, as code points.
pub const M_NONSTRUCTLIKE: [u32; 39] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 110, 32, 97, 32, 110, 111,
    110, 45, 115, 116, 114, 117, 99, 116, 117, 114, 101, 45, 108, 105, 107, 101, 32, 116,
    121, 112, 101
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"projection on a non-structure type"`, as code points.
pub const M_NONSTRUCT: [u32; 34] = [
    112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 110, 32, 97, 32, 110, 111,
    110, 45, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 116, 121, 112, 101
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

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: annotate"`, as code points.
pub const M_FUEL_ANNOTATE: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 110,
    110, 111, 116, 97, 116, 101
];

// ---------------------------------------------------------------------------
// The lanes: the twin's `r : CoreFnsA`, defunctionalized (the module note)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// Lean twin: `proof/ConRon/Arena/Core.lean:2798-2859 coreKnot` — **the
/// executed knot**: the memoized one, `pureFnsA`'s.
pub const LANE_FULL: u32 = 0;

/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:98-118 coreKnotGated` — the P
/// knot: `whnfCore` is the gated body and no slot carries a memo.
pub const LANE_GATED: u32 = 1;

/// con-leche: ConLeche/Kernel/CoreIO.lean:91-119 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:33-47 coreKnotIO` — the io knot
/// (the leaf lane): `infer` and `inferIO` are `inferBodyIO` tied to this knot,
/// unmemoized; every other slot is the full knot's.
pub const LANE_IO: u32 = 2;

// ---------------------------------------------------------------------------
// Fuel for the store walks (`Core.lean:74-86`)
// ---------------------------------------------------------------------------

/// con-leche: none — the fuel every store walk in this module runs at
/// Lean twin: `proof/ConRon/Arena/Core.lean:86 coreWalkFuel`.  DESIGN.md §8.4
/// asks for fuel as an explicit `Nat`; the walks below are over the handle
/// DAG, so any bound above the store's node count is unreachable.
/// `4 000 000 000` is above the representable node count (2^27 per
/// constructor per tier, ten constructors, two tiers) and below `2^63`, so it
/// is one machine word.
pub const CORE_WALK_FUEL: u64 = 4000000000;

// ---------------------------------------------------------------------------
// Reserved names, interned (`Core.lean:88-130`)
// ---------------------------------------------------------------------------

/// con-leche: none — intern a reserved name and hand back its handle
/// Lean twin: `proof/ConRon/Arena/Core.lean:109 pin` — the one place the arena
/// turns a name VALUE into a name HANDLE outside the parser.  DESIGN.md §8.3
/// licenses comparing the result by word: `denoteN` is injective, so index
/// inequality IS structural inequality.
pub fn pin(pers: &PersTier, st: &mut AState, n: &Name) -> Result<NIdx, CheckError> {
    intern_name(pers, st, n)
}

/// con-leche: none — the empty universe-argument list, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:113 emptyLevels` — `us ==
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:117 zeroLevel` — the comparand of
/// every `Level.isEquiv u .zero` in this module.  Task #97-P6-4a: the pin.
pub fn zero_level(st: &AState) -> Result<LIdx, CheckError> {
    pin_zero_level(st)
}

/// con-leche: none — the expression `Sort 1`, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:121-124 sortOne` — the pinned type
/// of `Nat`, `String`, `Char` and `Bool`.  Task #97-P6-4a: the pin, which
/// saves three interns (the level `0`, its successor and the `sort` node) on
/// every call.
pub fn sort_one(st: &AState) -> Result<EIdx, CheckError> {
    pin_sort_one(st)
}

/// con-leche: none — a level-monomorphic constant `.const n []`, interned
/// Lean twin: `proof/ConRon/Arena/Core.lean:128-130 constE`.
pub fn const_e(pers: &PersTier, st: &mut AState, n: &NIdx) -> Result<EIdx, CheckError> {
    match empty_levels(st) {
        Err(e) => Err(e),
        Ok(us) => intern_e(pers, st, ENodeView::Const(n.dup2(), us)),
    }
}

// ---------------------------------------------------------------------------
// The level verdicts, cached (`Core.lean:132-176`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:143-144 lvlEq?` — the verdict probe, as
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

/// con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:141-156 lvlEq?` — `Level.isEquiv`
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
        None => match read_level(pers, st, u) {
            Err(e) => Err(e),
            Ok(lu) => match read_level(pers, st, v) {
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

/// con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv
/// Lean twin: `proof/ConRon/Arena/Core.lean:150-154 lvlEq?` — the record half
/// of the probe, with DESIGN.md §8.3's cap (lesson 10: past `CACHE_CAP` the
/// table is dropped whole) and the journal of the module note in
/// `arena::core_state`.
pub fn lvl_eq_set(st: &mut AState, k: LIdxPair, r: bool) {
    if st.caches.lvl_eq_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.lvl_eq_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.lvl_eq_c.insert(k, r);
}

/// con-leche: ConLeche/Kernel/Level.lean:165-172 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:163-164 lvlsEq?` — the verdict probe, as
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

/// con-leche: ConLeche/Kernel/Level.lean:165-172 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:161-176 lvlsEq?` — pairwise
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
        None => match read_levels(pers, st, us) {
            Err(e) => Err(e),
            Ok(lu) => match read_levels(pers, st, vs) {
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

/// con-leche: ConLeche/Kernel/Level.lean:165-172 isEquivList
/// Lean twin: `proof/ConRon/Arena/Core.lean:170-174 lvlsEq?` — the record half.
pub fn lvls_eq_set(st: &mut AState, k: LsIdxPair, r: bool) {
    if st.caches.lvls_eq_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.lvls_eq_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.lvls_eq_c.insert(k, r);
}

// ---------------------------------------------------------------------------
// The lazy instantiated-constant caches (`Core.lean:178-235`)
// ---------------------------------------------------------------------------

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:191-192 constTyAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn const_ty_probe(st: &AState, k: &NLsKey) -> Option<EIdx> {
    match st.caches.const_ty_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache, `constTyAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:189-200 constTyAt` — a stored
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:195-199 constTyAt` — the record half.
pub fn const_ty_set(st: &mut AState, k: NLsKey, r: &EIdx) {
    if st.caches.const_ty_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.const_ty_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.const_ty_c.insert(k, r.dup2());
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:207-208 constValAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn const_val_probe(st: &AState, k: &NLsKey) -> Option<EIdx> {
    match st.caches.const_val_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's `constValAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:205-217 constValAt` — a stored
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:212-216 constValAt` — the record half.
pub fn const_val_set(st: &mut AState, k: NLsKey, r: &EIdx) {
    if st.caches.const_val_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.const_val_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.const_val_c.insert(k, r.dup2());
}

/// con-leche: none — DESIGN.md §8.3's instantiated-constant cache
/// Lean twin: `proof/ConRon/Arena/Core.lean:225-226 ruleRhsAt` — the probe, as its own
/// function over a *shared* state borrow (see `lvl_eq_probe`).
pub fn rule_rhs_probe(st: &AState, k: &NNLsKey) -> Option<EIdx> {
    match st.caches.rule_rhs_c.get(k) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: none — DESIGN.md §8.3's `ruleRhsAt`
/// Lean twin: `proof/ConRon/Arena/Core.lean:222-235 ruleRhsAt` — an iota
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:229-234 ruleRhsAt` — the record half.
pub fn rule_rhs_set(st: &mut AState, k: NNLsKey, r: &EIdx) {
    if st.caches.rule_rhs_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.rule_rhs_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.rule_rhs_c.insert(k, r.dup2());
}

// ---------------------------------------------------------------------------
// The error (`Core.lean:237-249`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:82-102 unknownConstError
/// Lean twin: `proof/ConRon/Arena/Core.lean:244-249 unknownConstError` — **the
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

// ---------------------------------------------------------------------------
// The bodies' small helpers (`Core.lean:274-412`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:151-154 liftFueled
/// Lean twin: `proof/ConRon/Arena/Core.lean:278-280 liftFueled` — lift a
/// fuel-style partial result; `none` is an internal error.  Monomorphic at
/// `Option bool` and with the `what` parameter baked in, because every call
/// site in the twin passes `"level comparison"` —
/// `con_ron_core::kernel::core_k::lift_fueled`'s own two deviations.
pub fn lift_fueled(o: Option<bool>) -> Result<bool, CheckError> {
    match o {
        Some(a) => Ok(a),
        None => fail(CheckError::Internal(code_points(&M_FUEL_LEVEL_CMP))),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName
/// Lean twin: `proof/ConRon/Arena/Core.lean:284-286 projModelName` — the
/// model-side name of field `i`'s projection for `T`.  `toString i` is
/// `con_ron_core::kernel::core_k::nat_to_dec`, the port's own decimal
/// recursion.
pub fn proj_model_name(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    i: u64,
) -> Result<NIdx, CheckError>  {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    const PROJ_: [u32; 5] = [112, 114, 111, 106, 95];
    match intern_n_node(pers, st, NNodeView::Str(t.dup2(), code_points(&MODEL))) {
        Err(e) => Err(e),
        Ok(m) => {
            let digits: Vec<u32> = core_k::nat_to_dec(i);
            let s: Vec<u32> = code_points_from(&digits, 0, code_points(&PROJ_));
            intern_n_node(pers, st, NNodeView::Str(m, s))
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp
/// Lean twin: `proof/ConRon/Arena/Core.lean:290-296 isCtorApp` — is the
/// expression headed by a stored constructor?
pub fn is_ctor_app(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(c, _)) => match env::ifenv_find(vis, fe, &c) {
                Some(IConstantInfo::CtorInfo(_, _, _)) => Ok(true),
                Some(_) => Ok(false),
                None => Ok(false),
            },
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:55-62 piResultIsProp
/// Lean twin: `proof/ConRon/Arena/Core.lean:300-305 piResultIsProp` — does the
/// syntactic pi telescope end in a (normalized) `Prop`?
pub fn pi_result_is_prop(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<bool, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Sort(u)) => match zero_level(st) {
                Err(er) => Err(er),
                Ok(z) => match lvl_eq(pers, st, &u, &z) {
                    Err(er) => Err(er),
                    Ok(Some(true)) => Ok(true),
                    Ok(_) => Ok(false),
                },
            },
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:64-72 piResultZ
/// Lean twin: `proof/ConRon/Arena/Core.lean:309-314 piResultZ` — **the
/// result-sort zero-ness datum of an inductive's type** (`IndCaps.sortZ`).
pub fn pi_result_z(pers: &PersTier, st: &mut AState, e: &EIdx) -> Result<PropWhen, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Sort(u)) => match read_level(pers, st, &u) {
                Err(er) => Err(er),
                Ok(l) => Ok(level::zeroness_of(&l)),
            },
            Ok(_) => Ok(prop_when::if_all_zero(Vec::new())),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:74-82 piResultNeverZero
/// Lean twin: `proof/ConRon/Arena/Core.lean:319-326 piResultNeverZero` — is the
/// result sort of a stored inductive's type, instantiated at the given levels,
/// provably nonzero (official `is_never_zero`)?
pub fn pi_result_never_zero(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match pi_result(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Sort(u)) => match read_names(pers, st, lps) {
                Err(er) => Err(er),
                Ok(ks) => match read_levels(pers, st, us) {
                    Err(er) => Err(er),
                    Ok(vs) => match read_level(pers, st, &u) {
                        Err(er) => Err(er),
                        Ok(l) => Ok(level::is_never_zero(&level::subst(&ks, &vs, &l))),
                    },
                },
            },
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:84-95 capsNeverZero
/// Lean twin: `proof/ConRon/Arena/Core.lean:330-334 capsNeverZero` — the same
/// question read off the STORED datum, which is what the checker runs.
pub fn caps_never_zero(
    pers: &PersTier,
    st: &mut AState,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    caps: &IIndCaps,
) -> Result<bool, CheckError> {
    match read_names(pers, st, lps) {
        Err(er) => Err(er),
        Ok(ks) => match read_levels(pers, st, us) {
            Err(er) => Err(er),
            Ok(vs) => Ok(prop_when::is_never(&level::subst_pw(&ks, &vs, &caps.sort_z))),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:97-134 isUnitLikeTy
/// Lean twin: `proof/ConRon/Arena/Core.lean:340-353 isUnitLikeTy` — is this
/// (whnf'd) type expression a unit-like inductive type?  con-leche's task #161
/// item C1: the head-name comparison against `PUnit` comes FIRST and
/// short-circuits after one comparison at every other head.
pub fn is_unit_like_ty(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    h: &EIdx,
) -> Result<bool, CheckError>  {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(c, _)) => match pin_punit(st) {
            Err(e) => Err(e),
            Ok(pu) => {
                if !c.eq2(&pu) {
                    Ok(false)
                } else {
                    match env::ifenv_find(vis, fe, &pu) {
                        Some(IConstantInfo::IndInfo(_, _)) => {
                            match pin_punit_rec(st) {
                                Err(e) => Err(e),
                                Ok(pr) => match env::ifenv_find(vis, fe, &pr) {
                                    Some(IConstantInfo::RecInfo(_, m_i, r_p, rules)) => {
                                        if rules.len() == 1 {
                                            if *m_i == *r_p {
                                                Ok(rules[0].nfields == 0)
                                            } else {
                                                Ok(false)
                                            }
                                        } else {
                                            Ok(false)
                                        }
                                    }
                                    Some(_) => Ok(false),
                                    None => Ok(false),
                                },
                            }
                        }
                        Some(_) => Ok(false),
                        None => Ok(false),
                    }
                }
            }
        },
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition
/// Lean twin: `proof/ConRon/Arena/Core.lean:359-372 unfoldDefinition` — unfold
/// the (application of a) definition at the head, one step.  The stored value
/// is instantiated through `const_val_at`, so a constant unfolded twice at the
/// same levels pays the substitution once.
pub fn unfold_definition(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(n, us)) => match env::ifenv_find(vis, fe, &n) {
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
            Ok(_) => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead
/// Lean twin: `proof/ConRon/Arena/Core.lean:377-385 unfoldableHead` — may the
/// delta step unfold `e`'s head (the official kernel's `is_delta`)?  The
/// DECISION, taken before the unfolding is materialized.
pub fn unfoldable_head(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(n, us)) => match env::ifenv_find(vis, fe, &n) {
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
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint
/// Lean twin: `proof/ConRon/Arena/Core.lean:389-395 headHint` — the
/// reducibility hint of the constant at the head of `e`.
pub fn head_hint(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    e: &EIdx,
) -> Result<ReducibilityHint, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(h) => match view(pers, st, &h) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(n, _)) => match env::ifenv_find(vis, fe, &n) {
                Some(IConstantInfo::DefnInfo(_, _, hint)) => {
                    Ok(con_ron_core::kernel::env::reducibility_hint_dup(hint))
                }
                Some(_) => Ok(ReducibilityHint::Opaque),
                None => Ok(ReducibilityHint::Opaque),
            },
            Ok(_) => Ok(ReducibilityHint::Opaque),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads
/// Lean twin: `proof/ConRon/Arena/Core.lean:400-412 sameConstHeads` — are `a`
/// and `b` applications of the *same* constant (the lazy delta same-head
/// short-circuit)?  Both sides must actually be applications.
pub fn same_const_heads(
    pers: &PersTier,
    st: &mut AState,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match view(pers, st, a) {
        Err(e) => Err(e),
        Ok(ENodeView::App(f1, _)) => match view(pers, st, b) {
            Err(e) => Err(e),
            Ok(ENodeView::App(f2, _)) => match get_app_fn(pers, st, CORE_WALK_FUEL, &f1) {
                Err(e) => Err(e),
                Ok(h1) => match view(pers, st, &h1) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(n1, _)) => {
                        match get_app_fn(pers, st, CORE_WALK_FUEL, &f2) {
                            Err(e) => Err(e),
                            Ok(h2) => match view(pers, st, &h2) {
                                Err(e) => Err(e),
                                Ok(ENodeView::Const(n2, _)) => Ok(n1.eq2(&n2)),
                                Ok(_) => Ok(false),
                            },
                        }
                    }
                    Ok(_) => Ok(false),
                },
            },
            Ok(_) => Ok(false),
        },
        Ok(_) => Ok(false),
    }
}

// ---------------------------------------------------------------------------
// `Nat` literals (`Core.lean:414-534`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:194-200 natLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:416-425 natLitToConstructor` — the
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
                    match intern_e(pers, st, ENodeView::Lit(expr::literal_nat(nat::pred(n)))) {
                        Err(e) => Err(e),
                        Ok(l) => intern_e(pers, st, ENodeView::App(sc, l)),
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:429-433 natIndOk` — the stored
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:437-442 natZeroOk` — the stored
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:446-454 natSuccOk` — the stored
/// `Nat.succ` declaration has the expected (annotated) shape.
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
                        Ok(nc) => match view(pers, st, &ty) {
                            Err(e) => Err(e),
                            Ok(ENodeView::ForallE(dom, body, _)) => {
                                if dom.eq2(&nc) {
                                    Ok(body.eq2(&nc))
                                } else {
                                    Ok(false)
                                }
                            }
                            Ok(_) => Ok(false),
                        },
                    },
                }
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported
/// con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF
/// Lean twin: `proof/ConRon/Arena/Core.lean:460-466 natLitSupported` — whether
/// the environment supports `Nat` literals.  One twin for con-leche's two
/// spellings (deviation 1).
pub fn nat_lit_supported(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match nat_ind_ok(st, env::ifenv_find(vis, fe, &nt)) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match pin_nat_zero(st) {
                Err(e) => Err(e),
                Ok(nz) => match nat_zero_ok(pers, st, env::ifenv_find(vis, fe, &nz)) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match pin_nat_succ(st) {
                        Err(e) => Err(e),
                        Ok(ns) => nat_succ_ok(pers, st, env::ifenv_find(vis, fe, &ns)),
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:482 constsResolve` — `(fe.find?
/// n).isSome`, as its own function so the two literal arms below read as the
/// twin's conjunctions do.
pub fn stored(vis: u64, fe: &IFEnv, n: &NIdx) -> bool {
    match env::ifenv_find(vis, fe, n) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:478-483 constsResolve` — the
/// `.lit (.natVal _)` arm's three `find?`s, as its own function
/// (`con_ron_core::kernel::core_k::nat_trio_stored`'s reason: the `String`
/// arm repeats them).
pub fn nat_trio_stored(vis: u64, st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(nt) => match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(nz) => match pin_nat_succ(st) {
                Err(e) => Err(e),
                Ok(ns) => Ok(stored(vis, fe, &nt) && stored(vis, fe, &nz) && stored(vis, fe, &ns)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:484-499 constsResolve` — the
/// `.lit (.strVal _)` arm's seven further `find?`s.
pub fn str_support_stored(vis: u64, st: &mut AState, fe: &IFEnv) -> Result<bool, CheckError> {
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
                                Ok(a7) => Ok(stored(vis, fe, &a1)
                                    && stored(vis, fe, &a2)
                                    && stored(vis, fe, &a3)
                                    && stored(vis, fe, &a4)
                                    && stored(vis, fe, &a5)
                                    && stored(vis, fe, &a6)
                                    && stored(vis, fe, &a7)),
                            },
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
/// Lean twin: `proof/ConRon/Arena/Core.lean:473-514 constsResolve` — do all
/// constants referenced in `e` (including inside `fvar` type annotations)
/// resolve in `fe`?  A full walk over the term, hence fuel; unlike the
/// checker's hot walks it is run once per declaration and carries no memo, as
/// con-leche's does not.
pub fn consts_resolve(
    pers: &PersTier,
    vis: u64,
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
            Ok(ENodeView::Lit(Literal::NatVal(_))) => nat_trio_stored(vis, st, fe),
            // **Both halves run**: the twin's `.strVal` arm `pin`s all ten
            // names and *then* takes one conjunction, so short-circuiting the
            // string half would leave seven names uninterned and the store
            // behind the twin's (see the evaluation-order note in DESIGN.md's
            // task #97-P4c section).
            Ok(ENodeView::Lit(Literal::StrVal(_))) => match nat_trio_stored(vis, st, fe) {
                Err(e) => Err(e),
                Ok(nats) => match str_support_stored(vis, st, fe) {
                    Err(e) => Err(e),
                    Ok(strs) => Ok(nats && strs),
                },
            },
            Ok(ENodeView::Const(n, _)) => Ok(stored(vis, fe, &n)),
            Ok(ENodeView::FVar(_, ty)) => consts_resolve(pers, vis, st, fe, fuel - 1, &ty),
            Ok(ENodeView::App(f, a)) => match consts_resolve(pers, vis, st, fe, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(true) => consts_resolve(pers, vis, st, fe, fuel - 1, &a),
                Ok(false) => Ok(false),
            },
            Ok(ENodeView::Lam(ty, body, _)) => match consts_resolve(pers, vis, st, fe, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(true) => consts_resolve(pers, vis, st, fe, fuel - 1, &body),
                Ok(false) => Ok(false),
            },
            Ok(ENodeView::ForallE(ty, body, _)) => {
                match consts_resolve(pers, vis, st, fe, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(true) => consts_resolve(pers, vis, st, fe, fuel - 1, &body),
                    Ok(false) => Ok(false),
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                match consts_resolve(pers, vis, st, fe, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match consts_resolve(pers, vis, st, fe, fuel - 1, &val) {
                        Err(e) => Err(e),
                        Ok(true) => consts_resolve(pers, vis, st, fe, fuel - 1, &body),
                        Ok(false) => Ok(false),
                    },
                }
            }
            Ok(ENodeView::Proj(s, _, sub)) => {
                if stored(vis, fe, &s) {
                    consts_resolve(pers, vis, st, fe, fuel - 1, &sub)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:262-267 litToCtorIfNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:518-522 litToCtorIfNat` — convert a
/// `Nat`-literal major premise to constructor form, one layer.
pub fn lit_to_ctor_if_nat(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lit(Literal::NatVal(n))) => {
            let m: Nat = nat::clone(&n);
            match nat_lit_supported(pers, vis, st, fe) {
                Err(e) => Err(e),
                Ok(true) => nat_lit_to_constructor(pers, st, &m),
                Ok(false) => Ok(h.dup2()),
            }
        }
        Ok(_) => Ok(h.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit?
/// Lean twin: `proof/ConRon/Arena/Core.lean:527-534 rawNatLit?` — a `Nat`
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:543-550 strLitConsSpine` — the
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
                match intern_e(pers, st, ENodeView::Lit(expr::literal_nat(nat::from_u64(c)))) {
                    Err(e) => Err(e),
                    Ok(lit) => match intern_e(pers, st, ENodeView::App(of_nat.dup2(), lit)) {
                        Err(e) => Err(e),
                        Ok(ch) => match intern_e(pers, st, ENodeView::App(cons.dup2(), ch)) {
                            Err(e) => Err(e),
                            Ok(f) => intern_e(pers, st, ENodeView::App(f, rest)),
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:563-571 strLitToConstructor` — the
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
        Ok(lc_n) => match intern_e(pers, st, ENodeView::Const(lc_n, zs.dup2())) {
            Err(e) => Err(e),
            Ok(lc) => match intern_e(pers, st, ENodeView::App(lc, ch_c.dup2())) {
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
                                                intern_e(pers, st, ENodeView::App(sl, spine))
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor
/// Lean twin: `proof/ConRon/Arena/Core.lean:555-571 strLitToConstructor` — the
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
                                match intern_e(pers, st, ENodeView::Const(ln_n, zs.dup2())) {
                                    Err(e) => Err(e),
                                    Ok(ln) => {
                                        match intern_e(pers, st, ENodeView::App(ln, ch_c.dup2()))
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:575-580 stringTyOk` — the stored
/// `String` declaration has the expected shape.
pub fn string_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            },
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:309-315 charTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:584-589 charTyOk` — the stored
/// `Char` declaration has the expected shape.
pub fn char_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            },
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:594-606 listTyOk` — the stored
/// `List` declaration has the expected (annotated) shape `List.{p} : Type p →
/// Type p`.
pub fn list_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => {
                if cv.level_params.len() != 1 {
                    Ok(false)
                } else {
                    let p: NIdx = cv.level_params[0].dup2();
                    match intern_l_node(pers, st, LNodeView::Param(p)) {
                        Err(e) => Err(e),
                        Ok(pl) => match intern_l_node(pers, st, LNodeView::Succ(pl)) {
                            Err(e) => Err(e),
                            Ok(sp) => match intern_e(pers, st, ENodeView::Sort(sp)) {
                                Err(e) => Err(e),
                                Ok(sort) => match view(pers, st, &cv.ty) {
                                    Err(e) => Err(e),
                                    Ok(ENodeView::ForallE(d, b, _)) => {
                                        if d.eq2(&sort) {
                                            Ok(b.eq2(&sort))
                                        } else {
                                            Ok(false)
                                        }
                                    }
                                    Ok(_) => Ok(false),
                                },
                            },
                        },
                    }
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:620-633 listNilTyOk` — the cited
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
    match view(pers, st, ty) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(d, b, _)) => {
            if !d.eq2(sort) {
                Ok(false)
            } else {
                match view(pers, st, &b) {
                    Err(e) => Err(e),
                    Ok(ENodeView::App(f, a)) => match view(pers, st, &f) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Const(l1, us1)) => match view(pers, st, &a) {
                            Err(e) => Err(e),
                            Ok(ENodeView::BVar(0)) => {
                                if l1.eq2(li) {
                                    Ok(us1.eq2(ps))
                                } else {
                                    Ok(false)
                                }
                            }
                            Ok(_) => Ok(false),
                        },
                        Ok(_) => Ok(false),
                    },
                    Ok(_) => Ok(false),
                }
            }
        }
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:610-634 listNilTyOk` — the stored
/// `List.nil` declaration has the expected (annotated) shape.
pub fn list_nil_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => {
                if cv.level_params.len() != 1 {
                    Ok(false)
                } else {
                    let p: NIdx = cv.level_params[0].dup2();
                    match intern_l_node(pers, st, LNodeView::Param(p)) {
                        Err(e) => Err(e),
                        Ok(pl) => match intern_l_node(pers, st, LNodeView::Succ(pl.dup2())) {
                            Err(e) => Err(e),
                            Ok(sp) => match intern_e(pers, st, ENodeView::Sort(sp)) {
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
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:652-665 listConsTyOk` — the three
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
    match intern_e(pers, st, ENodeView::App(l1.dup2(), b1.dup2())) {
        Err(e) => Err(e),
        Ok(dom3) => match intern_e(pers, st, ENodeView::App(l1.dup2(), b2.dup2())) {
            Err(e) => Err(e),
            Ok(cod3) => match view(pers, st, ty) {
                Err(e) => Err(e),
                Ok(ENodeView::ForallE(d1, r1, _)) => {
                    if !d1.eq2(sort) {
                        Ok(false)
                    } else {
                        match view(pers, st, &r1) {
                            Err(e) => Err(e),
                            Ok(ENodeView::ForallE(d2, r2, _)) => {
                                if !d2.eq2(b0) {
                                    Ok(false)
                                } else {
                                    match view(pers, st, &r2) {
                                        Err(e) => Err(e),
                                        Ok(ENodeView::ForallE(d3, c3, _)) => {
                                            if d3.eq2(&dom3) {
                                                Ok(c3.eq2(&cod3))
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                        Ok(_) => Ok(false),
                                    }
                                }
                            }
                            Ok(_) => Ok(false),
                        }
                    }
                }
                Ok(_) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:642-665 listConsTyOk` — the cited
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
            Ok(sp) => match intern_e(pers, st, ENodeView::Sort(sp)) {
                Err(e) => Err(e),
                Ok(sort) => {
                    let mut pv: Vec<LIdx> = Vec::new();
                    pv.push(pl);
                    match intern_ls_node(pers, st, pv) {
                        Err(e) => Err(e),
                        Ok(ps) => match pin_list(st) {
                            Err(e) => Err(e),
                            Ok(li) => match intern_e(pers, st, ENodeView::BVar(0)) {
                                Err(e) => Err(e),
                                Ok(b0) => match intern_e(pers, st, ENodeView::BVar(1)) {
                                    Err(e) => Err(e),
                                    Ok(b1) => match intern_e(pers, st, ENodeView::BVar(2)) {
                                        Err(e) => Err(e),
                                        Ok(b2) => {
                                            match intern_e(pers, st, ENodeView::Const(li, ps)) {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:638-666 listConsTyOk` — the stored
/// `List.cons` declaration has the expected (annotated) shape.
pub fn list_cons_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => {
                if cv.level_params.len() != 1 {
                    Ok(false)
                } else {
                    let p: NIdx = cv.level_params[0].dup2();
                    list_cons_ty_at(pers, st, &cv.ty, &p)
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:362-371 charOfNatTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:670-681 charOfNatTyOk` — the stored
/// `Char.ofNat` declaration has the expected (annotated) shape `Nat → Char`.
pub fn char_of_nat_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => {
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
                                    Ok(cc) => match view(pers, st, &cv.ty) {
                                        Err(e) => Err(e),
                                        Ok(ENodeView::ForallE(d, b, _)) => {
                                            if d.eq2(&nc) {
                                                Ok(b.eq2(&cc))
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                        Ok(_) => Ok(false),
                                    },
                                },
                            },
                        },
                    }
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:690-701 stringOfListTyOk` — the
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
                    Ok(li) => match intern_e(pers, st, ENodeView::Const(li, zs)) {
                        Err(e) => Err(e),
                        Ok(lc) => match pin_char(st) {
                            Err(e) => Err(e),
                            Ok(ch) => match const_e(pers, st, &ch) {
                                Err(e) => Err(e),
                                Ok(cc) => match intern_e(pers, st, ENodeView::App(lc, cc)) {
                                    Err(e) => Err(e),
                                    Ok(dom) => {
                                        match pin_string(st) {
                                            Err(e) => Err(e),
                                            Ok(stn) => match const_e(pers, st, &stn) {
                                                Err(e) => Err(e),
                                                Ok(sc) => match view(pers, st, ty) {
                                                    Err(e) => Err(e),
                                                    Ok(ENodeView::ForallE(d, b, _)) => {
                                                        if d.eq2(&dom) {
                                                            Ok(b.eq2(&sc))
                                                        } else {
                                                            Ok(false)
                                                        }
                                                    }
                                                    Ok(_) => Ok(false),
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:686-702 stringOfListTyOk` — the
/// stored `String.ofList` declaration has the expected (annotated) shape
/// `List.{0} Char → String`.
pub fn string_of_list_ty_ok(
    pers: &PersTier,
    st: &mut AState,
    ci: Option<&IConstantInfo>,
) -> Result<bool, CheckError> {
    match ci {
        Some(c) => match env::i_constant_info_to_constant_val(pers, &mut st.store, c) {
            Err(e) => Err(e),
            Ok(cv) => {
                if cv.level_params.len() != 0 {
                    Ok(false)
                } else {
                    string_of_list_ty_body(pers, st, &cv.ty)
                }
            }
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported
/// Lean twin: `proof/ConRon/Arena/Core.lean:714-723 strLitSupported` — the last
/// five guards of the cited chain (`List`, `List.nil`, `List.cons`, `Char`,
/// `Char.ofNat`), split off so the nesting stays readable.
pub fn str_lit_supported_rest(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match pin_list(st) {
        Err(e) => Err(e),
        Ok(li) => match list_ty_ok(pers, st, env::ifenv_find(vis, fe, &li)) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match pin_list_nil(st) {
                Err(e) => Err(e),
                Ok(ln) => match list_nil_ty_ok(pers, st, env::ifenv_find(vis, fe, &ln)) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match pin_list_cons(st) {
                        Err(e) => Err(e),
                        Ok(lc) => match list_cons_ty_ok(pers, st, env::ifenv_find(vis, fe, &lc)) {
                            Err(e) => Err(e),
                            Ok(false) => Ok(false),
                            Ok(true) => match pin_char(st) {
                                Err(e) => Err(e),
                                Ok(ch) => match char_ty_ok(pers, st, env::ifenv_find(vis, fe, &ch)) {
                                    Err(e) => Err(e),
                                    Ok(false) => Ok(false),
                                    Ok(true) => {
                                        match pin_char_of_nat(st) {
                                            Err(e) => Err(e),
                                            Ok(co) => char_of_nat_ty_ok(
                                                pers,
                                                st,
                                                env::ifenv_find(vis, fe, &co),
                                            ),
                                        }
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported
/// con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF
/// Lean twin: `proof/ConRon/Arena/Core.lean:708-723 strLitSupported` — whether
/// the environment supports `String` literals: the `Nat` literal guard plus
/// the seven string-support declarations at exactly the expected types.
pub fn str_lit_supported(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match nat_lit_supported(pers, vis, st, fe) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match pin_string(st) {
            Err(e) => Err(e),
            Ok(stn) => match string_ty_ok(pers, st, env::ifenv_find(vis, fe, &stn)) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => match pin_string_of_list(st) {
                    Err(e) => Err(e),
                    Ok(sl) => match string_of_list_ty_ok(pers, st, env::ifenv_find(vis, fe, &sl)) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => str_lit_supported_rest(pers, vis, st, fe),
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Structural-`Nat` literal acceleration (`Core.lean:726-1172`)
//
// con-leche's certified fast path: an operation participates only when its
// defining recurrence equations hold by definitional equality — checked once,
// at install, so *presence in the store is the certificate*.  The nineteen
// reserved names are interned here exactly as the literal guards' are; the
// `ConLeche.Name` values are `con_ron_core::kernel::core_k`'s own, so the two
// crates cannot spell a reserved name differently.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:433 natPredName
/// Lean twin: `proof/ConRon/Arena/Core.lean:735 natPredName`.
pub fn nat_pred_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_pred(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:434 natAddName
/// Lean twin: `proof/ConRon/Arena/Core.lean:737 natAddName`.
pub fn nat_add_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_add(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:435 natSubName
/// Lean twin: `proof/ConRon/Arena/Core.lean:739 natSubName`.
pub fn nat_sub_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_sub(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:436 natMulName
/// Lean twin: `proof/ConRon/Arena/Core.lean:741 natMulName`.
pub fn nat_mul_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_mul(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:437 natPowName
/// Lean twin: `proof/ConRon/Arena/Core.lean:743 natPowName`.
pub fn nat_pow_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_pow(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:438 natBeqName
/// Lean twin: `proof/ConRon/Arena/Core.lean:745 natBeqName`.
pub fn nat_beq_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_beq(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:439 natBleName
/// Lean twin: `proof/ConRon/Arena/Core.lean:747 natBleName`.
pub fn nat_ble_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_ble(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:440 natDivName
/// Lean twin: `proof/ConRon/Arena/Core.lean:749 natDivName`.
pub fn nat_div_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_div(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:441 natModName
/// Lean twin: `proof/ConRon/Arena/Core.lean:751 natModName`.
pub fn nat_mod_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_mod(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:442 natGcdName
/// Lean twin: `proof/ConRon/Arena/Core.lean:753 natGcdName`.
pub fn nat_gcd_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_gcd(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:443 natLandName
/// Lean twin: `proof/ConRon/Arena/Core.lean:755 natLandName`.
pub fn nat_land_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_land(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:444 natLorName
/// Lean twin: `proof/ConRon/Arena/Core.lean:757 natLorName`.
pub fn nat_lor_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_lor(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:445 natXorName
/// Lean twin: `proof/ConRon/Arena/Core.lean:759 natXorName`.
pub fn nat_xor_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_xor(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:446 natShiftLeftName
/// Lean twin: `proof/ConRon/Arena/Core.lean:761 natShiftLeftName`.
pub fn nat_shift_left_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_shift_left(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:447 natShiftRightName
/// Lean twin: `proof/ConRon/Arena/Core.lean:763 natShiftRightName`.
pub fn nat_shift_right_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_nat_shift_right(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:448 boolName
/// Lean twin: `proof/ConRon/Arena/Core.lean:765 boolName`.
pub fn bool_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:449 boolTrueName
/// Lean twin: `proof/ConRon/Arena/Core.lean:767 boolTrueName`.
pub fn bool_true_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool_true(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:450 boolFalseName
/// Lean twin: `proof/ConRon/Arena/Core.lean:769 boolFalseName`.
pub fn bool_false_name(st: &mut AState) -> Result<NIdx, CheckError> {
    pin_bool_false(st)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue
/// Lean twin: `proof/ConRon/Arena/Core.lean:774-781 isBoolTrue` — is `e` the
/// constant `Bool.true` (the official kernel's `is_constant(e, Bool.true)`):
/// the name, no universe levels.
pub fn is_bool_true(pers: &PersTier, st: &mut AState, h: &EIdx) -> Result<bool, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Const(c, us)) => match empty_levels(st) {
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
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// Lean twin: `proof/ConRon/Arena/Core.lean:794-798 quickPair` — the pairs
/// official's `quick_is_def_eq` decides by itself: two sorts, two literals,
/// two ∀s, two λs.
///
/// **The one place the arena compares TAGS and not handles.**  con-leche's
/// clause is a four-arm structural match that reads only the two
/// constructors; DESIGN.md §8.3 makes index inequality structural inequality,
/// so the twin of a match on the CONSTRUCTOR is a comparison of the handle's
/// four tag bits — no `view`, no state, no `Result`.  Comparing the handles
/// themselves would be the twin of `a == b`, a different (and wrong)
/// predicate.
pub fn quick_pair(a: &EIdx, b: &EIdx) -> bool {
    (a.tag() == ETAG_SORT && b.tag() == ETAG_SORT)
        || (a.tag() == ETAG_LIT && b.tag() == ETAG_LIT)
        || (a.tag() == ETAG_FORALL_E && b.tag() == ETAG_FORALL_E)
        || (a.tag() == ETAG_LAM && b.tag() == ETAG_LAM)
}

/// con-leche: none — the `List NIdx` accumulator Lean's list literal hides
/// Lean twin: `proof/ConRon/Arena/Core.lean:802-806 natOpNames` — push one
/// interned name onto a `Vec`, so the name lists below read as the twin's
/// bracket literals do.
pub fn push_nidx(out: Vec<NIdx>, n: &NIdx) -> Vec<NIdx> {
    let mut out = out;
    out.push(n.dup2());
    out
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:473-481 natOpNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:802-806 natOpNames` — the certified
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames
/// con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:810-814 natDivModNames`
/// Lean twin: `proof/ConRon/Arena/Core.lean:993-997 natOpWfNames`
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:993-997 natOpWfNames` — the
/// pin-certified WF-recursive `Nat` operations, as a *safety net*.  The twin's
/// list is `natDivModNames`' element for element.
pub fn nat_op_wf_names(st: &mut AState) -> Result<Vec<NIdx>, CheckError> {
    nat_div_mod_names(st)
}

/// con-leche: none — the fifteen reserved `Nat`-operation handles, interned once
/// Lean twin: `proof/ConRon/Arena/Core.lean:818-823 natOpDeps` — the twin
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:818-823 natOpDeps` — the `let`
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:821-823 natOpDeps` — the last eight
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps
/// Lean twin: `proof/ConRon/Arena/Core.lean:818-839 natOpDeps` — the operations
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:844-846 natAp1` — `ap1 n a`, one of
/// the equation builder's three local lambdas.  DESIGN.md §3.4 forbids the
/// closure, so each is a named function.
pub fn nat_ap1(pers: &PersTier, st: &mut AState, n: &NIdx, a: &EIdx) -> Result<EIdx, CheckError> {
    match const_e(pers, st, n) {
        Err(e) => Err(e),
        Ok(f) => intern_e(pers, st, ENodeView::App(f, a.dup2())),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:849-851 natAp2` — `ap2 n a b`.
pub fn nat_ap2(
    pers: &PersTier,
    st: &mut AState,
    n: &NIdx,
    a: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match nat_ap1(pers, st, n, a) {
        Err(e) => Err(e),
        Ok(f) => intern_e(pers, st, ENodeView::App(f, b.dup2())),
    }
}

/// con-leche: none — the `List (Expr × Expr)` accumulator Lean's list literal hides
/// Lean twin: `proof/ConRon/Arena/Core.lean:872-910 natOpEquations` — push one
/// equation onto the result `Vec`.
pub fn push_eq(out: Vec<(EIdx, EIdx)>, l: &EIdx, r: &EIdx) -> Vec<(EIdx, EIdx)> {
    let mut out = out;
    out.push((l.dup2(), r.dup2()));
    out
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:857-910 natOpEquations` — the
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:857-868 natOpEquations` — the `let`
/// prefix, as its own function.
pub fn nat_eq_ctx(pers: &PersTier, st: &mut AState, d: u64) -> Result<NatEqCtx, CheckError> {
    match pin_nat(st) {
        Err(e) => Err(e),
        Ok(n_n) => match const_e(pers, st, &n_n) {
            Err(e) => Err(e),
            Ok(nat_ty) => match intern_e(pers, st, ENodeView::FVar(d, nat_ty.dup2())) {
                Err(e) => Err(e),
                Ok(x) => match intern_e(pers, st, ENodeView::FVar(d + 1, nat_ty)) {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:865-868 natOpEquations` — the last
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:857-910 natOpEquations` — the
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:872-910 natOpEquations` — the cited
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:891-896 natOpEquations` — the `pow`
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:897-903 natOpEquations` — the `beq`
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// Lean twin: `proof/ConRon/Arena/Core.lean:904-909 natOpEquations` — the `ble`
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult
/// Lean twin: `proof/ConRon/Arena/Core.lean:916-953 natOpResult` — the reduct of
/// op `c` on literal arguments (`pred` ignores the second slot).  `ron::Nat` is
/// con-leche's `Nat` here, and a literal is a `Literal` value in a `lit` node.
///
/// Deviation, and it is `con_ron_core::kernel::core_k::nat_op_result`'s own
/// (task #61): `shiftLeft`/`shiftRight` take a `u64` shift amount, so an
/// amount beyond `u64` cannot be computed at all and the port **fails**
/// there rather than answering `None` — a `Native` claims nothing, where a
/// `None` would be a different verdict.
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
                lit_nat(pers, st, nat::add(a, b))
            } else if c.eq2(&p.su) {
                lit_nat(pers, st, nat::sub(a, b))
            } else if c.eq2(&p.mu) {
                lit_nat(pers, st, nat::mul(a, b))
            } else if c.eq2(&p.po) {
                if nat::blt(&nat::from_u64(16777216), b) {
                    Ok(None)
                } else {
                    match nat::to_u64(b) {
                        Some(e) => lit_nat(pers, st, nat::pow(a, e)),
                        None => Ok(None),
                    }
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
                match nat::to_u64(b) {
                    Some(k) => lit_nat(pers, st, nat::shift_left(a, k)),
                    None => fail(CheckError::Native(code_points(&M_SHIFT))),
                }
            } else if c.eq2(&p.sr) {
                match nat::to_u64(b) {
                    Some(k) => lit_nat(pers, st, nat::shift_right(a, k)),
                    None => fail(CheckError::Native(code_points(&M_SHIFT))),
                }
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult
/// Lean twin: `proof/ConRon/Arena/Core.lean:922 natOpResult` — `internE (.lit
/// (.natVal …))` wrapped in `some`, which every arithmetic arm above ends in.
pub fn lit_nat(pers: &PersTier, st: &mut AState, n: Nat) -> Result<Option<EIdx>, CheckError> {
    match intern_e(pers, st, ENodeView::Lit(expr::literal_nat(n))) {
        Err(e) => Err(e),
        Ok(x) => Ok(Some(x)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult
/// Lean twin: `proof/ConRon/Arena/Core.lean:945-952 natOpResult` — the two
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:958-964 natOpDepsStored` —
/// con-leche writes `(natOpDeps c).all (fun n => …)`; DESIGN.md §3.4's rule for
/// a `List` walk is a named helper, and the `Vec` turns the twin's cons
/// recursion into a cursor.
pub fn nat_op_deps_stored(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    ns: &Vec<NIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= ns.len() {
        Ok(true)
    } else {
        match env::ifenv_find(vis, fe, &ns[i]) {
            Some(IConstantInfo::DefnInfo(cv, _, _)) => {
                if cv.level_params.len() == 0 {
                    nat_op_deps_stored(pers, vis, st, fe, ns, i + 1)
                } else {
                    Ok(false)
                }
            }
            Some(_) => Ok(false),
            None => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:980-988 natOpGuard` — the two
/// `Bool` constructors stored at no level parameters, the guard's tail.
pub fn bool_ctors_lp_empty(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<bool, CheckError>  {
    match bool_true_name(st) {
        Err(e) => Err(e),
        Ok(bt) => match lp_empty(pers, vis, st, fe, &bt) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            Ok(true) => match bool_false_name(st) {
                Err(e) => Err(e),
                Ok(bf) => lp_empty(pers, vis, st, fe, &bf),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
/// Lean twin: `proof/ConRon/Arena/Core.lean:981-988 natOpGuard` — `match
/// fe.find? n with | some ci => cv.levelParams.isEmpty | none => false`, at one
/// name.
pub fn lp_empty(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError>  {
    match env::ifenv_find(vis, fe, n) {
        Some(ci) => match env::i_constant_info_to_constant_val(pers, &mut st.store, ci) {
            Err(e) => Err(e),
            Ok(cv) => Ok(cv.level_params.len() == 0),
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
/// Lean twin: `proof/ConRon/Arena/Core.lean:971-989 natOpGuard` —
/// stored-constant guards for op `c`: the `Nat` basis, every dependency stored
/// as a definition, and (for the `Bool`-valued ops and the `ble`-guarded
/// `div`/`mod`) the `Bool` constructors stored.
pub fn nat_op_guard(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    c: &NIdx,
) -> Result<bool, CheckError>  {
    match nat_lit_supported(pers, vis, st, fe) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match nat_op_deps(st, c) {
            Err(e) => Err(e),
            Ok(deps) => match nat_op_deps_stored(pers, vis, st, fe, &deps, 0) {
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
                                    bool_ctors_lp_empty(pers, vis, st, fe)
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:614-620 Expr.substConst0
/// Lean twin: `proof/ConRon/Arena/Core.lean:1002-1013 substConst0` — substitute
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
                    Ok(a2) => intern_e(pers, st, ENodeView::App(f2, a2)),
                },
            },
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:622-638 Expr.substConstAll
/// Lean twin: `proof/ConRon/Arena/Core.lean:1018-1045 substConstAll` —
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
                    Ok(a2) => intern_e(pers, st, ENodeView::App(f2, a2)),
                },
            },
            Ok(ENodeView::Lam(ty, b, mb)) => match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                    Err(e) => Err(e),
                    Ok(b2) => intern_e(pers, st, ENodeView::Lam(t2, b2, mb)),
                },
            },
            Ok(ENodeView::ForallE(ty, b, mb)) => {
                match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(b2) => intern_e(pers, st, ENodeView::ForallE(t2, b2, mb)),
                    },
                }
            }
            Ok(ENodeView::LetE(ty, v, b)) => match subst_const_all(pers, st, n, r, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(t2) => match subst_const_all(pers, st, n, r, fuel - 1, &v) {
                    Err(e) => Err(e),
                    Ok(v2) => match subst_const_all(pers, st, n, r, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(b2) => intern_e(pers, st, ENodeView::LetE(t2, v2, b2)),
                    },
                },
            },
            Ok(ENodeView::Proj(s, i, e2)) => match subst_const_all(pers, st, n, r, fuel - 1, &e2) {
                Err(er) => Err(er),
                Ok(x) => intern_e(pers, st, ENodeView::Proj(s, i, x)),
            },
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod
/// Lean twin: `proof/ConRon/Arena/Core.lean:1050-1066 natOpCod` — the pinned
/// codomain of a structural-`Nat` operation: `Bool` for the comparisons, `Nat`
/// otherwise.
pub fn nat_op_cod(
    pers: &PersTier,
    vis: u64,
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
                                    bool_ty_ok(pers, vis, st, fe, &bn)
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod
/// Lean twin: `proof/ConRon/Arena/Core.lean:1057-1062 natOpCod` — the stored
/// `Bool` declaration at no level parameters and type `Sort 1`.
pub fn bool_ty_ok(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    bn: &NIdx,
) -> Result<bool, CheckError>  {
    match env::ifenv_find(vis, fe, bn) {
        Some(ci) => match env::i_constant_info_to_constant_val(pers, &mut st.store, ci) {
            Err(e) => Err(e),
            Ok(cv) => match sort_one(st) {
                Err(e) => Err(e),
                Ok(s1) => {
                    if cv.level_params.len() == 0 {
                        Ok(cv.ty.eq2(&s1))
                    } else {
                        Ok(false)
                    }
                }
            },
        },
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:652-667 natOpTyPinned
/// Lean twin: `proof/ConRon/Arena/Core.lean:1072-1088 natOpTyPinned` — the
/// pinned type of a certified `Nat` operation: `Nat → Nat` for the unary
/// `pred`, `Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat → Bool`
/// for the comparisons.
pub fn nat_op_ty_pinned(
    pers: &PersTier,
    vis: u64,
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
                        match view(pers, st, ty) {
                            Err(er) => Err(er),
                            Ok(ENodeView::ForallE(dom, body, _)) => {
                                if dom.eq2(&nc) {
                                    nat_op_cod(pers, vis, st, fe, c, &body)
                                } else {
                                    Ok(false)
                                }
                            }
                            Ok(_) => Ok(false),
                        }
                    } else {
                        match view(pers, st, ty) {
                            Err(er) => Err(er),
                            Ok(ENodeView::ForallE(dom, rest, _)) => match view(pers, st, &rest) {
                                Err(er) => Err(er),
                                Ok(ENodeView::ForallE(dom2, body, _)) => {
                                    if dom.eq2(&nc) && dom2.eq2(&nc) {
                                        nat_op_cod(pers, vis, st, fe, c, &body)
                                    } else {
                                        Ok(false)
                                    }
                                }
                                Ok(_) => Ok(false),
                            },
                            Ok(_) => Ok(false),
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:669-675 natOpStoredOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:1092-1096 natOpStoredOk` — op `n`
/// is stored as a level-monomorphic definition with the pinned type.
pub fn nat_op_stored_ok(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
) -> Result<bool, CheckError> {
    match env::ifenv_find(vis, fe, n) {
        Some(IConstantInfo::DefnInfo(cv, _, _)) => {
            if cv.level_params.len() == 0 {
                let ty: EIdx = cv.ty.dup2();
                nat_op_ty_pinned(pers, vis, st, fe, n, &ty)
            } else {
                Ok(false)
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored
/// con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
/// Lean twin: `proof/ConRon/Arena/Core.lean:1103-1106 natOpStored` — **the
/// reduction-time test for a certified `Nat` operation** (con-leche's task #161
/// item B3): is `c` stored as a definition at all?  The full `natOpGuard` is
/// carried by the install fold invariant.
pub fn nat_op_stored(vis: u64, fe: &IFEnv, c: &NIdx) -> bool {
    match env::ifenv_find(vis, fe, c) {
        Some(IConstantInfo::DefnInfo(_, _, _)) => true,
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:1112-1120 natBinOpName` — the binary
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
/// Lean twin: `proof/ConRon/Arena/Core.lean:1234 iotaIndexOk` — `args.drop k`,
/// as a fresh `Vec` of handle words.
pub fn drop_eidx(xs: &Vec<EIdx>, k: usize) -> Vec<EIdx> {
    drop_eidx_from(xs, k, Vec::new())
}

/// con-leche: none — `List.drop` on a `Vec`; Lean's list tail is shared
/// Lean twin: `proof/ConRon/Arena/Core.lean:1234 iotaIndexOk` — the cursor
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

/// con-leche: none — `List.append` on a `Vec`; Lean's `++` shares the tail
/// Lean twin: `proof/ConRon/Arena/Core.lean:1298 structEtaProjCerts` — `xs ++
/// ys`, consuming `xs` and copying `ys`' spine.
pub fn append_eidx(xs: Vec<EIdx>, ys: &Vec<EIdx>) -> Vec<EIdx> {
    append_eidx_from(xs, ys, 0)
}

/// con-leche: none — `List.append` on a `Vec`; Lean's `++` shares the tail
/// Lean twin: `proof/ConRon/Arena/Core.lean:1298 structEtaProjCerts` — the
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

/// con-leche: none — `xs ++ [y]` on a `Vec`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1295 structEtaProjCerts` — the
/// cited `targs ++ [b]`, which is one `push`.
pub fn snoc_eidx(xs: Vec<EIdx>, y: &EIdx) -> Vec<EIdx> {
    let mut xs = xs;
    xs.push(y.dup2());
    xs
}

/// con-leche: none — `List.getD` on a `Vec`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1890 iotaRec` — `args.getD i b0`,
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

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:1127-1172 reduceNat` — literal
/// acceleration (the official kernel's `reduceNat`, run in the `whnf` loop
/// *before* delta-unfolding).  The divergence audit's D15 is preserved: the
/// FIRST argument is head-normalised and, unless it is a literal, the step
/// fails WITHOUT touching the second.
pub fn reduce_nat(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::App(f, b)) => match view(pers, st, &f) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(c, us)) => {
                reduce_nat_succ(pers, vis, st, mode, lane, fuel, fe, depth, &c, &us, &b)
            }
            Ok(ENodeView::App(g, a)) => match view(pers, st, &g) {
                Err(er) => Err(er),
                Ok(ENodeView::Const(c, us)) => {
                    reduce_nat_bin(pers, vis, st, mode, lane, fuel, fe, depth, &c, &us, &a, &b)
                }
                Ok(_) => Ok(None),
            },
            Ok(_) => Ok(None),
        },
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:1131-1143 reduceNat` — the cited
/// `.app (.const c []) a` arm: `Nat.succ` at a literal argument.
pub fn reduce_nat_succ(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
                    // lifts `(← natLitSupported fe)` out of the condition
                    // `c == ns && …` to a `let` before the `if`.
                    // `natLitSupported` interns, so running it only when
                    // `c == ns` would leave the store a node behind the twin's.
                    Ok(ns) => match nat_lit_supported(pers, vis, st, fe) {
                        Err(er) => Err(er),
                        Ok(nls) => {
                            if c.eq2(&ns) && nls {
                                match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, b) {
                                    Err(er) => Err(er),
                                    Ok(w) => match raw_nat_lit(pers, st, &w) {
                                        Err(er) => Err(er),
                                        Ok(Some(n)) => {
                                            lit_nat(pers, st, nat::add(&n, &nat::one()))
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

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:1144-1170 reduceNat` — the cited
/// `.app (.app (.const c []) a) b` arm: a certified binary operation at two
/// literal arguments, or the WF-recursive safety net's decline.
pub fn reduce_nat_bin(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
                        if bin && nat_op_stored(vis, fe, c) {
                            match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, a) {
                                Err(er) => Err(er),
                                Ok(wa) => match raw_nat_lit(pers, st, &wa) {
                                    Err(er) => Err(er),
                                    Ok(None) => Ok(None),
                                    Ok(Some(n1)) => {
                                        match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, b)
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
                            reduce_nat_wf(pers, vis, st, mode, lane, fuel, fe, depth, c, a, b)
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
/// Lean twin: `proof/ConRon/Arena/Core.lean:1157-1169 reduceNat` — the
/// WF-recursive safety net: a pinned `div`/`mod`/… at two literals is a
/// positively detected unsupported feature, not a reduction.
pub fn reduce_nat_wf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        // Both conjuncts again (see `reduce_nat_succ`): the twin's condition is
        // `wf.contains c && (← natLitSupported fe)`, and the `←` is lifted.
        Ok(wf) => match nat_lit_supported(pers, vis, st, fe) {
            Err(er) => Err(er),
            Ok(nls) => {
                if env::nidx_vec_contains(&wf, c) && nls {
                    match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, a) {
                        Err(er) => Err(er),
                        Ok(wa) => match raw_nat_lit(pers, st, &wa) {
                            Err(er) => Err(er),
                            Ok(None) => Ok(None),
                            Ok(Some(_)) => {
                                match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, b) {
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
        },
    }
}

// ---------------------------------------------------------------------------
// The certification helpers (`Core.lean:1175-1581`)
//
// con-leche's `Core.lean`:865-1310.  Every one of these recurses structurally
// on a LIST (an argument spine, a slot index list), so none of them takes
// fuel; what they call into the store does.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:210-243 iotaCerts
/// Lean twin: `proof/ConRon/Arena/Core.lean:1186-1203 iotaCerts` — certify a
/// spine against a recursor telescope: each argument's inferred type is defeq
/// to the corresponding (instantiated) domain.  **The ι-slot licence**: at a
/// *licensed* walk (`lic = true`) a slot whose ∀-binder datum is `.never` is
/// skipped.  The twin's `List` recursion is a cursor over the `Vec`.
pub fn iota_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    lic: bool,
    h: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    let acc: Vec<EIdx> = Vec::new();
    iota_certs_aux(pers, vis, st, mode, lane, fuel, fe, depth, lic, h, &acc, args, i)
}

/// con-leche: ConLeche/Cached/CoreC.lean:154-193 iotaCertsIAux
/// Lean twin: OWED (task #97-P6-9's ledger) — the cached tier's bulk form of
/// `iotaCerts`.
///
/// **The batched instantiation lever** (task #97-P6-9), the certificate half:
/// peel the RAW telescope while the certified arguments accumulate, and
/// substitute only each binder's DOMAIN (small) instead of copying the whole
/// residual telescope per argument.  `acc` is innermost-first, the list
/// `instantiate_list` takes at cursor 0; the identification with the chain of
/// `instantiate1` the spec-shaped body ran is `Expr.instantiateList_cons`
/// (`ConLeche/Verify/InstList.lean`).
///
/// A raw `bvar` body — whose substitution could expose further `∀`-binders,
/// which is the fold's semantics — substitutes the accumulator and re-enters
/// at the same argument, exactly as the twin does; every other non-`forallE`
/// view is `false`, as it is in the spec.
pub fn iota_certs_aux(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    lic: bool,
    h: &EIdx,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= args.len() {
        Ok(true)
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, body, mb)) => {
                let arg: EIdx = args[i].dup2();
                if lic && prop_when::is_never(&mb.pw) {
                    let acc2: Vec<EIdx> = cons_eidx(&arg, acc);
                    iota_certs_aux(
                        pers, vis, st, mode, lane, fuel, fe, depth, lic, &body, &acc2, args,
                        i + 1,
                    )
                } else {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, acc, 0) {
                        Err(e) => Err(e),
                        Ok(ty2) => {
                            match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &arg) {
                                Err(e) => Err(e),
                                Ok(ta) => match knot_defeq(
                                    pers, vis, st, mode, lane, fuel, fe, depth, &ta, &ty2,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(false) => Ok(false),
                                    Ok(true) => {
                                        let acc2: Vec<EIdx> = cons_eidx(&arg, acc);
                                        iota_certs_aux(
                                            pers, vis, st, mode, lane, fuel, fe, depth, lic,
                                            &body, &acc2, args, i + 1,
                                        )
                                    }
                                },
                            }
                        }
                    }
                }
            }
            Ok(ENodeView::BVar(_)) => {
                if acc.len() == 0 {
                    Ok(false)
                } else {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, h, acc, 0) {
                        Err(e) => Err(e),
                        Ok(ty2) => {
                            let acc2: Vec<EIdx> = Vec::new();
                            iota_certs_aux(
                                pers, vis, st, mode, lane, fuel, fe, depth, lic, &ty2, &acc2,
                                args, i,
                            )
                        }
                    }
                }
            }
            Ok(_) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:702-707 piResidual
/// Lean twin: `proof/ConRon/Arena/Core.lean:1207-1214 piResidual` — peel a
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
        match view(pers, st, e) {
            Err(er) => Err(er),
            Ok(ENodeView::ForallE(_, b, _)) => {
                let a: EIdx = args[i].dup2();
                match instantiate1_fast(pers, st, CORE_WALK_FUEL, &b, &a, 0) {
                    Err(er) => Err(er),
                    Ok(b2) => pi_residual(pers, st, &b2, args, i + 1),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:245-254 defEqList
/// Lean twin: `proof/ConRon/Arena/Core.lean:1218-1223 defEqList` — pairwise
/// definitional equality of two spines.  The twin's `| _, _ => false`
/// catch-all is the length test.
pub fn def_eq_list(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &a, &b) {
            Err(e) => Err(e),
            Ok(true) => def_eq_list(pers, vis, st, mode, lane, fuel, fe, depth, xs, ys, i + 1),
            Ok(false) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:256-272 iotaIndexOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:1227-1235 iotaIndexOk` — the
/// canonical-index comparison of a firing ι redex.
pub fn iota_index_ok(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
                    let rest: Vec<EIdx> = drop_eidx(&args, cn_p as usize);
                    def_eq_list(pers, vis, st, mode, lane, fuel, fe, depth, &rest, idx, 0)
                }
            },
            Ok(None) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:274-305 proofIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1240-1258 proofIrrel` — proof
/// irrelevance certification: both sides' types whnf to the basis unit type,
/// or both sides' types' *sorts* are `Prop`.  con-leche's task #172 B4: every
/// inference here is at the io grade.
pub fn proof_irrel(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(ta) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &ta) {
            Err(e) => Err(e),
            Ok(wta) => match is_unit_like_ty(pers, vis, st, fe, &wta) {
                Err(e) => Err(e),
                Ok(true) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, b) {
                    Err(e) => Err(e),
                    Ok(tb) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tb) {
                        Err(e) => Err(e),
                        Ok(wtb) => is_unit_like_ty(pers, vis, st, fe, &wtb),
                    },
                },
                Ok(false) => prop_sorts_zero(pers, vis, st, mode, lane, fuel, fe, depth, &ta, b),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:274-305 proofIrrel
/// con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1247-1258 proofIrrel`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1272-1283 propIrrel`
/// The `Prop` branch both certifications end in: the *sort* of the type of `a`
/// and the sort of the type of `b` are both `Prop`.  `proofIrrel` reaches it
/// with `ta` already inferred, `propIrrel` with `ta` inferred after its two
/// fast arms have declined, so the twin writes the same eleven lines twice and
/// the port writes them once.
pub fn prop_sorts_zero(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ta: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, ta) {
        Err(e) => Err(e),
        Ok(tta) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tta) {
            Err(e) => Err(e),
            Ok(wa) => match view(pers, st, &wa) {
                Err(e) => Err(e),
                Ok(ENodeView::Sort(u_t)) => match zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => match lvl_eq(pers, st, &u_t, &z) {
                        Err(e) => Err(e),
                        Ok(o) => match lift_fueled(o) {
                            Err(e) => Err(e),
                            Ok(ok_a) => {
                                match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, b) {
                                    Err(e) => Err(e),
                                    Ok(tb) => prop_sorts_zero_right(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth, ok_a, &tb,
                                    ),
                                }
                            }
                        },
                    },
                },
                Ok(_) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:274-305 proofIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1253-1257 proofIrrel` — the right
/// side of `prop_sorts_zero`.
pub fn prop_sorts_zero_right(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ok_a: bool,
    tb: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, tb) {
        Err(e) => Err(e),
        Ok(ttb) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &ttb) {
            Err(e) => Err(e),
            Ok(wb) => match view(pers, st, &wb) {
                Err(e) => Err(e),
                Ok(ENodeView::Sort(v_t)) => match zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => match lvl_eq(pers, st, &v_t, &z) {
                        Err(e) => Err(e),
                        Ok(o) => match lift_fueled(o) {
                            Err(e) => Err(e),
                            Ok(ok_b) => Ok(ok_a && ok_b),
                        },
                    },
                },
                Ok(_) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:307-349 propIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1264-1283 propIrrel` — **the
/// hoisted proof-irrelevance test** (con-leche's task #168, Option U): the
/// `Prop` branch of `proofIrrel` alone, with the head-symbol readers deciding
/// both fast arms before any inference.
pub fn prop_irrel(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
    match not_proof_fast(pers, vis, st, fe, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(na) => match not_proof_fast(pers, vis, st, fe, CORE_WALK_FUEL, b) {
            Err(e) => Err(e),
            Ok(nb) => {
                if na || nb {
                    Ok(false)
                } else {
                    match is_proof_fast(pers, vis, st, fe, CORE_WALK_FUEL, a) {
                        Err(e) => Err(e),
                        Ok(pa) => match is_proof_fast(pers, vis, st, fe, CORE_WALK_FUEL, b) {
                            Err(e) => Err(e),
                            Ok(pb) => {
                                if pa && pb {
                                    Ok(true)
                                } else {
                                    match knot_infer_io(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth, a,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(ta) => prop_sorts_zero(
                                            pers,
                                            vis,
                                            st, mode, lane, fuel, fe, depth, &ta, b,
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

/// con-leche: ConLeche/Kernel/Core.lean:351-374 structEtaProjCerts
/// Lean twin: `proof/ConRon/Arena/Core.lean:1288-1302 structEtaProjCerts` — the
/// per-projection telescope certificates of a structural eta certification at
/// a **projection-function** slot family.  The twin's `List Nat` is
/// `List.range nF` at every call site, so the port is the counted recursion
/// `towerSlotsAllGo` already is.
pub fn struct_eta_proj_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    t: &NIdx,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    lps_t: &Vec<NIdx>,
    n: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(true)
    } else {
        match env::proj_fn_name(pers, &mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(nm) => match env::ifenv_find(vis, fe, &nm) {
                Some(IConstantInfo::RecInfo(cvp, _, _, _)) => {
                    let cvp_lps: Vec<NIdx> = env::nidx_vec_dup(&cvp.level_params);
                    let cvp_ty: EIdx = cvp.ty.dup2();
                    let cvp_name: NIdx = cvp.name.dup2();
                    match strip_pis(pers, st, targs.len() as u64 + 1, &cvp_ty) {
                        Err(e) => Err(e),
                        Ok(None) => Ok(false),
                        Ok(Some(_)) => {
                            if !nidx_vec_beq(&cvp_lps, lps_t) {
                                Ok(false)
                            } else {
                                let cv = IConstantVal {
                                    name: cvp_name,
                                    level_params: cvp_lps,
                                    ty: cvp_ty,
                                };
                                match const_ty_at(pers, st, &cv, us2) {
                                    Err(e) => Err(e),
                                    Ok(ty) => {
                                        let spine: Vec<EIdx> =
                                            snoc_eidx(env::eidx_vec_dup(targs), b);
                                        match iota_certs(
                                            pers,
                                            vis,
                                            st, mode, lane, fuel, fe, depth, false, &ty,
                                            &spine, 0,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(false) => Ok(false),
                                            Ok(true) => struct_eta_proj_certs(
                                                pers,
                                                vis,
                                                st,
                                                mode,
                                                lane,
                                                fuel,
                                                fe,
                                                depth,
                                                t,
                                                us2,
                                                targs,
                                                b,
                                                lps_t,
                                                n - 1,
                                                j + 1,
                                            ),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Some(_) => Ok(false),
                None => Ok(false),
            },
        }
    }
}

/// con-leche: none — `List NIdx` equality; Lean's `deriving DecidableEq` on the level-parameter list
/// Lean twin: `proof/ConRon/Arena/Core.lean:1296 structEtaProjCerts` — the
/// cited `cvp.levelParams = lpsT`, over the `Vec` the port stores it in.
pub fn nidx_vec_beq(a: &Vec<NIdx>, b: &Vec<NIdx>) -> bool {
    if a.len() == b.len() {
        nidx_vec_beq_from(a, b, 0)
    } else {
        false
    }
}

/// con-leche: none — `List NIdx` equality; Lean's `deriving DecidableEq` on the level-parameter list
/// Lean twin: `proof/ConRon/Arena/Core.lean:1296 structEtaProjCerts` — the
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:709-714 towerSlotsAll
/// Lean twin: `proof/ConRon/Arena/Core.lean:1307-1311 towerSlotsAllGo` — the
/// slot walk.  con-leche writes `(List.range nF).all fun j => …`; DESIGN.md
/// §3.4's rule turns the closure into a counted recursion.
pub fn tower_slots_all_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(true)
    } else {
        match env::ifenv_find_proj(pers, vis, &mut st.store, fe, t, j) {
            Err(e) => Err(e),
            Ok(Some(_)) => tower_slots_all_go(pers, vis, st, fe, t, n - 1, j + 1),
            Ok(None) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:709-714 towerSlotsAll
/// con-leche: ConLeche/Kernel/FEnv.lean:97-99 FEnv.towerSlotsAllF
/// Lean twin: `proof/ConRon/Arena/Core.lean:1316-1317 towerSlotsAll` — are all
/// `nF` projection slots of `T` table entries?
pub fn tower_slots_all(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
) -> Result<bool, CheckError> {
    tower_slots_all_go(pers, vis, st, fe, t, n_f, 0)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:716-724 recSlotsAll
/// Lean twin: `proof/ConRon/Arena/Core.lean:1321-1326 recSlotsAllGo` — the
/// projection-function slot walk, as a counted recursion.
pub fn rec_slots_all_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(true)
    } else {
        match env::proj_fn_name(pers, &mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(nm) => match env::ifenv_find(vis, fe, &nm) {
                Some(IConstantInfo::RecInfo(_, _, _, _)) => {
                    rec_slots_all_go(pers, vis, st, fe, t, n - 1, j + 1)
                }
                Some(_) => Ok(false),
                None => Ok(false),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:716-724 recSlotsAll
/// con-leche: ConLeche/Kernel/FEnv.lean:105-110 FEnv.recSlotsAllF
/// Lean twin: `proof/ConRon/Arena/Core.lean:1332-1333 recSlotsAll` — are all
/// `nF` projection slots of `T` recursor-backed projection functions?
pub fn rec_slots_all(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    n_f: u64,
) -> Result<bool, CheckError> {
    rec_slots_all_go(pers, vis, st, fe, t, n_f, 0)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs
/// Lean twin: `proof/ConRon/Arena/Core.lean:1337-1342 projNodesGo` — the
/// `.proj` half of the fabricated projections, as a counted recursion.
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
        match intern_e(pers, st, ENodeView::Proj(t.dup2(), j, b.dup2())) {
            Err(e) => Err(e),
            Ok(p) => match proj_nodes_go(pers, st, t, b, n - 1, j + 1) {
                Err(e) => Err(e),
                Ok(rest) => Ok(cons_eidx(&p, &rest)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs
/// Lean twin: `proof/ConRon/Arena/Core.lean:1346-1353 projAppsGo` — the
/// projection-function half, as a counted recursion.
pub fn proj_apps_go(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    us: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    n: u64,
    j: u64,
) -> Result<Vec<EIdx>, CheckError> {
    if n == 0 {
        Ok(Vec::new())
    } else {
        match env::proj_fn_name(pers, &mut st.store, t, j) {
            Err(e) => Err(e),
            Ok(nm) => match intern_e(pers, st, ENodeView::Const(nm, us.dup2())) {
                Err(e) => Err(e),
                Ok(f) => {
                    let spine: Vec<EIdx> = snoc_eidx(env::eidx_vec_dup(targs), b);
                    match mk_app_n(pers, st, &f, &spine) {
                        Err(e) => Err(e),
                        Ok(p) => match proj_apps_go(pers, st, t, us, targs, b, n - 1, j + 1) {
                            Err(e) => Err(e),
                            Ok(rest) => Ok(cons_eidx(&p, &rest)),
                        },
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs
/// Lean twin: `proof/ConRon/Arena/Core.lean:1358-1361 etaProjs` — the
/// fabricated projections of a structure-eta spine: `.proj T j b` nodes when
/// every slot has a table entry, else the modeled path's projection-function
/// applications.
pub fn eta_projs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    us: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    n_f: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match tower_slots_all(pers, vis, st, fe, t, n_f) {
        Err(e) => Err(e),
        Ok(true) => proj_nodes_go(pers, st, t, b, n_f, 0),
        Ok(false) => proj_apps_go(pers, st, t, us, targs, b, n_f, 0),
    }
}

/// con-leche: ConLeche/Kernel/Basis/Names.lean:109-116 reservedBasisNames
/// Lean twin: `proof/ConRon/Arena/Core.lean:1366-1386 reservedBasisNames` — the
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

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
/// Lean twin: `proof/ConRon/Arena/Core.lean:1425-1443 structEtaCertWith` — the
/// certificate's tail, from `defEqList (aargs.take caps.etaParams) targs` on:
/// the parameter comparison, the TT-lane synthetic-spine certification
/// (con-leche's task #137, skipped unless `mode.ttChecks`) and the field
/// comparison against the fabricated projections.
pub fn struct_eta_cert_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvc: &IConstantVal,
    us: &LsIdx,
    t: &NIdx,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    aargs: &Vec<EIdx>,
    eta_params: u64,
    eta_fields: u64,
) -> Result<bool, CheckError> {
    let head: Vec<EIdx> = take_eidx(aargs, eta_params as usize);
    match def_eq_list(pers, vis, st, mode, lane, fuel, fe, depth, &head, targs, 0) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => {
            let tt = if con_ron_core::kernel::env::tt_checks(mode) {
                match const_ty_at(pers, st, cvc, us) {
                    Err(e) => Err(e),
                    Ok(ty_c) => match eta_projs(pers, vis, st, fe, t, us2, targs, b, eta_fields) {
                        Err(e) => Err(e),
                        Ok(projs) => {
                            let spine: Vec<EIdx> =
                                append_eidx(env::eidx_vec_dup(targs), &projs);
                            iota_certs(
                                pers,
                                vis,
                                st, mode, lane, fuel, fe, depth, false, &ty_c, &spine, 0,
                            )
                        }
                    },
                }
            } else {
                Ok(true)
            };
            match tt {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => match eta_projs(pers, vis, st, fe, t, us2, targs, b, eta_fields) {
                    Err(e) => Err(e),
                    Ok(projs) => {
                        let rest: Vec<EIdx> = drop_eidx(aargs, eta_params as usize);
                        def_eq_list(pers, vis, st, mode, lane, fuel, fe, depth, &rest, &projs, 0)
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
/// Lean twin: `proof/ConRon/Arena/Core.lean:1414-1443 structEtaCertWith` — the
/// twin's `famT`: the type-former telescope certificate, a certificate FAMILY
/// gated on `mode.certs` (task #97f, P2f).  Its own function so the gate's
/// `.trusted` arm does not compute `constTyAt` either — the twin's `if
/// mode.certs then iotaCerts … (← constTyAt cvT us') targs else pure true` has
/// the lookup INSIDE the branch.
pub fn struct_eta_cert_fam(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvt: &IConstantVal,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if !con_ron_core::kernel::env::certs(mode) {
        Ok(true)
    } else {
        match const_ty_at(pers, st, cvt, us2) {
            Err(e) => Err(e),
            Ok(ty_t) => {
                iota_certs(pers, vis, st, mode, lane, fuel, fe, depth, false, &ty_t, targs, 0)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
/// Lean twin: `proof/ConRon/Arena/Core.lean:1414-1443 structEtaCertWith` — the
/// certificate's middle, from the level comparison on: the structure's own
/// telescope certificate, the per-slot certificates (which a tabled family
/// does not have) and the tail above.
pub fn struct_eta_cert_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvc: &IConstantVal,
    cvt: &IConstantVal,
    us: &LsIdx,
    t: &NIdx,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
    b: &EIdx,
    aargs: &Vec<EIdx>,
    eta_params: u64,
    eta_fields: u64,
) -> Result<bool, CheckError> {
    match lvls_eq(pers, st, us, us2) {
        Err(e) => Err(e),
        Ok(o) => match lift_fueled(o) {
            Err(e) => Err(e),
            Ok(false) => Ok(false),
            // the type-former telescope certificate and the per-slot ones are
            // certificate FAMILIES (official's `try_eta_struct_core` runs
            // neither), so `mode.certs` gates them both (task #97f, P2f;
            // `Cached/CoreC.lean:437` and `:440`).  At `.trusted` the two type
            // lookups do not happen either: they are read nowhere else.
            Ok(true) => match struct_eta_cert_fam(
                pers,
                vis,
                st, mode, lane, fuel, fe, depth, cvt, us2, targs,
            ) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => {
                    let percerts = if !con_ron_core::kernel::env::certs(mode) {
                        Ok(true)
                    } else {
                        match tower_slots_all(pers, vis, st, fe, t, eta_fields) {
                            Err(e) => Err(e),
                            Ok(true) => Ok(true),
                            Ok(false) => struct_eta_proj_certs(
                                pers,
                                vis,
                                st,
                                mode,
                                lane,
                                fuel,
                                fe,
                                depth,
                                t,
                                us2,
                                targs,
                                b,
                                &cvt.level_params,
                                eta_fields,
                                0,
                            ),
                        }
                    };
                    match percerts {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => struct_eta_cert_tail(
                            pers,
                            vis,
                            st, mode, lane, fuel, fe, depth, cvc, us, t, us2, targs, b,
                            aargs, eta_params, eta_fields,
                        ),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
/// Lean twin: `proof/ConRon/Arena/Core.lean:1399-1444 structEtaCertWith` — the
/// certificate's head: the stuck side's whnf'd type must be a stored,
/// eta-capable, non-reserved inductive at the candidate's own constructor,
/// with matching arities and level parameters.
pub fn struct_eta_cert_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        Ok(hd) => match view(pers, st, &hd) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(t, us2)) => match env::ifenv_find(vis, fe, &t) {
                Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
                    let cvt: IConstantVal = env::i_constant_val_dup(cvt0);
                    let caps: IIndCaps = env::i_ind_caps_dup(caps0);
                    match get_app_args(pers, st, CORE_WALK_FUEL, wtb) {
                        Err(e) => Err(e),
                        Ok(targs) => match reserved_basis_names(st) {
                            Err(e) => Err(e),
                            Ok(reserved) => match view_ls(pers, st, &us2) {
                                Err(e) => Err(e),
                                Ok(uslen) => {
                                    let slots =
                                        match tower_slots_all(pers, vis, st, fe, &t, caps.eta_fields) {
                                            Err(e) => Err(e),
                                            Ok(true) => Ok(true),
                                            Ok(false) => {
                                                rec_slots_all(pers, vis, st, fe, &t, caps.eta_fields)
                                            }
                                        };
                                    match slots {
                                        Err(e) => Err(e),
                                        Ok(sl) => {
                                            if caps.eta
                                                && caps.eta_ctor.eq2(c)
                                                && !env::nidx_vec_contains(&reserved, &t)
                                                && !env::nidx_vec_contains(&reserved, c)
                                                && targs.len() as u64 == caps.eta_params
                                                && uslen.len() == cvt.level_params.len()
                                                && nidx_vec_beq(
                                                    &cvc.level_params,
                                                    &cvt.level_params,
                                                )
                                                && sl
                                            {
                                                struct_eta_cert_certs(
                                                    pers,
                                                    vis,
                                                    st,
                                                    mode,
                                                    lane,
                                                    fuel,
                                                    fe,
                                                    depth,
                                                    cvc,
                                                    &cvt,
                                                    us,
                                                    &t,
                                                    &us2,
                                                    &targs,
                                                    b,
                                                    aargs,
                                                    caps.eta_params,
                                                    caps.eta_fields,
                                                )
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                    }
                                }
                            },
                        },
                    }
                }
                Some(_) => Ok(false),
                None => Ok(false),
            },
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
/// Lean twin: `proof/ConRon/Arena/Core.lean:1391-1448 structEtaCertWith` — the
/// structure-eta certificate against a *given* weak-head-normal type of the
/// stuck side.
pub fn struct_eta_cert_with(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        Ok(hd) => match view(pers, st, &hd) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(c, us)) => match env::ifenv_find(vis, fe, &c) {
                Some(IConstantInfo::CtorInfo(cvc0, cn_p, cn_f)) => {
                    let cvc: IConstantVal = env::i_constant_val_dup(cvc0);
                    let want: u64 = *cn_p + *cn_f;
                    match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                        Err(e) => Err(e),
                        Ok(aargs) => {
                            if aargs.len() as u64 == want {
                                struct_eta_cert_at(
                                    pers,
                                    vis,
                                    st, mode, lane, fuel, fe, depth, &cvc, &c, &us, b,
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
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape
/// Lean twin: `proof/ConRon/Arena/Core.lean:1454-1462 etaCtorShape` — the
/// constructor shape official's `try_eta_struct_core` tests before inferring
/// anything: the candidate's head is a stored constructor applied to exactly
/// its parameters and fields.
pub fn eta_ctor_shape(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    a: &EIdx,
) -> Result<bool, CheckError>  {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(hd) => match view(pers, st, &hd) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(c, _)) => match env::ifenv_find(vis, fe, &c) {
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
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:450-473 structEtaCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1467-1473 structEtaCert` —
/// structural eta certification for a stored eta-capable structure.  The
/// constructor-shape test comes FIRST (the divergence audit's D13).
pub fn struct_eta_cert(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match eta_ctor_shape(pers, vis, st, fe, a) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, b) {
            Err(e) => Err(e),
            Ok(tb) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tb) {
                Err(e) => Err(e),
                Ok(wtb) => {
                    struct_eta_cert_with(pers, vis, st, mode, lane, fuel, fe, depth, a, b, &wtb)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1489-1498 structUnitCert` — the
/// certificate's tail, once the family's capabilities have been read: the two
/// whnf'd types are defeq and the structure's telescope is certified.
pub fn struct_unit_cert_tail(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvt: &IConstantVal,
    us2: &LsIdx,
    targs: &Vec<EIdx>,
    wta: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, b) {
        Err(e) => Err(e),
        Ok(tb) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tb) {
            Err(e) => Err(e),
            Ok(wtb) => match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, wta, &wtb) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                // the type-former telescope certificate is a certificate
                // FAMILY (official's `is_def_eq_unit_like` stops at the defeq
                // above), so `mode.certs` gates it — the twin's `if mode.certs
                // then iotaCerts … (← constTyAt cvT us') targs else pure true`,
                // lookup inside the branch (task #97f, P2f;
                // `Cached/CoreC.lean:508`)
                Ok(true) => {
                    if !con_ron_core::kernel::env::certs(mode) {
                        Ok(true)
                    } else {
                        match const_ty_at(pers, st, cvt, us2) {
                            Err(e) => Err(e),
                            Ok(ty_t) => iota_certs(
                                pers,
                                vis,
                                st, mode, lane, fuel, fe, depth, false, &ty_t, targs, 0,
                            ),
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1478-1500 structUnitCert` —
/// unit-likeness certification: `a` and `b` inhabit the same stored unit-like
/// family.
pub fn struct_unit_cert(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(ta) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &ta) {
            Err(e) => Err(e),
            Ok(wta) => match get_app_fn(pers, st, CORE_WALK_FUEL, &wta) {
                Err(e) => Err(e),
                Ok(hd) => match view(pers, st, &hd) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t, us2)) => match env::ifenv_find(vis, fe, &t) {
                        Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
                            let cvt: IConstantVal = env::i_constant_val_dup(cvt0);
                            let caps: IIndCaps = env::i_ind_caps_dup(caps0);
                            match get_app_args(pers, st, CORE_WALK_FUEL, &wta) {
                                Err(e) => Err(e),
                                Ok(targs) => match reserved_basis_names(st) {
                                    Err(e) => Err(e),
                                    Ok(reserved) => match view_ls(pers, st, &us2) {
                                        Err(e) => Err(e),
                                        Ok(uslen) => {
                                            if caps.unitlike
                                                && !env::nidx_vec_contains(&reserved, &t)
                                                && targs.len() as u64 == caps.unit_params
                                                && uslen.len() == cvt.level_params.len()
                                            {
                                                struct_unit_cert_tail(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, &cvt,
                                                    &us2, &targs, &wta, b,
                                                )
                                            } else {
                                                Ok(false)
                                            }
                                        }
                                    },
                                },
                            }
                        }
                        Some(_) => Ok(false),
                        None => Ok(false),
                    },
                    Ok(_) => Ok(false),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1504-1518 etaCert` — eta
/// certification for a one-sided λ against a stuck term `b`.
pub fn eta_cert(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty1: &EIdx,
    body1: &EIdx,
    m1: &BinderMeta,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, b) {
        Err(e) => Err(e),
        Ok(tb) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tb) {
            Err(e) => Err(e),
            Ok(w) => match view(pers, st, &w) {
                Err(e) => Err(e),
                Ok(ENodeView::ForallE(ty2, _, m2)) => {
                    match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &ty2, ty1) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            eta_cert_body(pers, vis, st, mode, lane, fuel, fe, depth, ty1, body1, m1,
                                &m2, b)
                        }
                    }
                }
                Ok(_) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:505-530 etaCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1509-1516 etaCert` — the cited
/// certificate's body, once the domains agree: open the λ at a fresh free
/// variable, compare against `b` applied to it, then compare the annotations.
pub fn eta_cert_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty1: &EIdx,
    body1: &EIdx,
    m1: &BinderMeta,
    m2: &BinderMeta,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match intern_e(pers, st, ENodeView::FVar(depth, ty1.dup2())) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body1, &fv, 0) {
            Err(e) => Err(e),
            Ok(lhs) => match intern_e(pers, st, ENodeView::App(b.dup2(), fv.dup2())) {
                Err(e) => Err(e),
                Ok(rhs) => {
                    match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth + 1, &lhs, &rhs) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            if con_ron_core::kernel::env::verified_checks(mode)
                                && !prop_when::beq(&m1.pw, &m2.pw)
                            {
                                fail(CheckError::NotImplemented(code_points(&M_ETA)))
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

/// con-leche: ConLeche/Kernel/Core.lean:532-542 stuckIrrel
/// Lean twin: `proof/ConRon/Arena/Core.lean:1523-1528 stuckIrrel` — the
/// fallback for structurally distinct stuck terms: structural eta in either
/// direction, unit-likeness, else proof irrelevance.
pub fn stuck_irrel(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match struct_eta_cert(pers, vis, st, mode, lane, fuel, fe, depth, a, b) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => match struct_eta_cert(pers, vis, st, mode, lane, fuel, fe, depth, b, a) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => match struct_unit_cert(pers, vis, st, mode, lane, fuel, fe, depth, a, b) {
                Err(e) => Err(e),
                Ok(true) => Ok(true),
                Ok(false) => proof_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a, b),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:751-759 etaFabArgs
/// Lean twin: `proof/ConRon/Arena/Core.lean:1534-1537 etaFabArgs` — the
/// eta-rescue fabrication's argument spine: the reduced type's arguments
/// followed by the installed projection functions applied to the stuck major.
pub fn eta_fab_args(
    pers: &PersTier,
    st: &mut AState,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    major: &EIdx,
    n_f: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match proj_apps_go(pers, st, t, ust, targs, major, n_f, 0) {
        Err(e) => Err(e),
        Ok(ps) => Ok(append_eidx(env::eidx_vec_dup(targs), &ps)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:761-766 etaFabArgsE
/// Lean twin: `proof/ConRon/Arena/Core.lean:1541-1544 etaFabArgsE` —
/// `etaFabArgs` at the entry kind: the projections are `etaProjs`'.
pub fn eta_fab_args_e(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    major: &EIdx,
    n_f: u64,
) -> Result<Vec<EIdx>, CheckError> {
    match eta_projs(pers, vis, st, fe, t, ust, targs, major, n_f) {
        Err(e) => Err(e),
        Ok(ps) => Ok(append_eidx(env::eidx_vec_dup(targs), &ps)),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:768-794 ProjEntry.fireOk
/// Lean twin: `proof/ConRon/Arena/Core.lean:1550-1557 IProjEntry.fireOk` —
/// **the tower-fire guard**: at a `Prop`-declared structure the field's guard
/// level must be a proposition at this instantiation; at every other family
/// the rule fires unconditionally.
pub fn proj_entry_fire_ok(
    pers: &PersTier,
    st: &mut AState,
    entry: &IProjEntry,
    us: &LsIdx,
) -> Result<bool, CheckError> {
    match zero_level(st) {
        Err(e) => Err(e),
        Ok(z) => match lvl_eq(pers, st, &entry.struct_sort, &z) {
            Err(e) => Err(e),
            Ok(Some(true)) => match read_names(pers, st, &entry.level_params) {
                Err(e) => Err(e),
                Ok(ks) => match read_levels(pers, st, us) {
                    Err(e) => Err(e),
                    Ok(vs) => match read_level(pers, st, &entry.field_sort) {
                        Err(e) => Err(e),
                        Ok(fs) => {
                            let s = level::subst(&ks, &vs, &fs);
                            match level::is_equiv(&s, &level::zero()) {
                                Some(true) => Ok(true),
                                Some(false) => Ok(false),
                                None => Ok(false),
                            }
                        }
                    },
                },
            },
            Ok(_) => Ok(true),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
/// Lean twin: `proof/ConRon/Arena/Core.lean:1561-1571 andRescueSlotsGo` — the
/// two-slot walk, as a counted recursion (con-leche's `(List.range 2).all`).
/// The cited `(← e.fireOk ust)` conjunct is lifted by Lean's `do` out of the
/// condition, so it runs whatever the three arity tests say, and so does this.
pub fn and_rescue_slots_go(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    an: &NIdx,
    ctor: &NIdx,
    n_p: u64,
    ust: &LsIdx,
    n: u64,
    j: u64,
) -> Result<bool, CheckError> {
    if n == 0 {
        Ok(true)
    } else {
        match env::ifenv_find_proj(pers, vis, &mut st.store, fe, an, j) {
            Err(e) => Err(e),
            Ok(Some(entry)) => match proj_entry_fire_ok(pers, st, &entry, ust) {
                Err(e) => Err(e),
                Ok(fok) => {
                    if entry.ctor.eq2(ctor)
                        && entry.num_params == n_p
                        && entry.num_fields == 2
                        && fok
                    {
                        and_rescue_slots_go(pers, vis, st, fe, an, ctor, n_p, ust, n - 1, j + 1)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(None) => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
/// con-leche: ConLeche/Kernel/CoreDefs.lean:811-813 andRescueSlots
/// con-leche: ConLeche/Kernel/FEnv.lean:101-103 FEnv.andRescueSlotsF
/// Lean twin: `proof/ConRon/Arena/Core.lean:1578-1581 andRescueSlots` — **the
/// pinned `And`'s projection slots, ready to fire.**  One twin for con-leche's
/// three spellings (deviation 1).
pub fn and_rescue_slots(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    ctor: &NIdx,
    n_p: u64,
    ust: &LsIdx,
) -> Result<bool, CheckError> {
    match pin_and(st) {
        Err(e) => Err(e),
        Ok(an) => and_rescue_slots_go(pers, vis, st, fe, &an, ctor, n_p, ust, 2, 0),
    }
}

// ---------------------------------------------------------------------------
// The stuck-major rescue and the ι step (`Core.lean:1584-1936`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1591-1593 fvarLeavesSubset` — the
/// fabrication's fvar-leaf containment, `fab.fvarLeaves.all (fun l =>
/// major.fvarLeaves.contains l)`, as a named recursion (DESIGN.md §3.4).
pub fn fvar_leaves_subset(xs: &Vec<(u64, EIdx)>, ys: &Vec<(u64, EIdx)>) -> bool {
    fvar_leaves_subset_from(xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1591-1593 fvarLeavesSubset` — the
/// cursor recursion behind `fvar_leaves_subset`.
pub fn fvar_leaves_subset_from(
    xs: &Vec<(u64, EIdx)>,
    ys: &Vec<(u64, EIdx)>,
    i: usize,
) -> bool {
    if i >= xs.len() {
        true
    } else if leaf_contains(ys, xs[i].0, &xs[i].1, 0) {
        fvar_leaves_subset_from(xs, ys, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `List.contains` on the `fvarLeaves` list; Lean's `BEq (Nat × EIdx)`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1593 fvarLeavesSubset` — is the
/// pair `(i, ty)` one of `ys`?  Handle equality is the structural comparison
/// the cited `BEq` performs (DESIGN.md §8.3).
pub fn leaf_contains(ys: &Vec<(u64, EIdx)>, i: u64, ty: &EIdx, j: usize) -> bool {
    if j >= ys.len() {
        false
    } else if ys[j].0 == i && ys[j].1.eq2(ty) {
        true
    } else {
        leaf_contains(ys, i, ty, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// con-leche: ConLeche/Cached/CoreC.lean:544-569 majorToCtorI
/// Lean twin: `proof/ConRon/Arena/Core.lean:1621-1624 fabScopeOk` — the scope
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
/// and those are what runs here.  `fvar_leaves_subset` above stays as the
/// specification of what `leaf_guard` decides.
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

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1635-1646 majorToCtor` — the K
/// rescue's certificate chain, once the fabricated major is built: the scope
/// guard, the synthetic-spine certification (con-leche's task #71), the
/// official `to_cnstr_when_K` type check and proof irrelevance.
pub fn major_to_ctor_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    ust: &LsIdx,
    spine: &Vec<EIdx>,
    fab: &EIdx,
    tmaj: &EIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match fab_scope_ok(pers, st, depth, fab, major) {
        Err(e) => Err(e),
        Ok(false) => Ok(major.dup2()),
        // the synthetic-spine certification (con-leche's task #71) is a
        // certificate FAMILY, gated on `mode.certs` (task #97f, P2f;
        // `Cached/CoreC.lean:576` and `:654`), and so is the `proofIrrel`
        // below the official `to_cnstr_when_K` type check (`:588`, `:658`).
        // The type check itself runs at both modes.
        Ok(true) => match iota_certs_fam(pers, vis, st, mode, lane, fuel, fe, depth, cvj, ust, spine) {
            Err(e) => Err(e),
            Ok(false) => Ok(major.dup2()),
            Ok(true) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, fab) {
                Err(e) => Err(e),
                Ok(tfab) => match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, tmaj, &tfab)
                {
                    Err(e) => Err(e),
                    Ok(false) => Ok(major.dup2()),
                    Ok(true) => {
                        let ir = if !con_ron_core::kernel::env::certs(mode) {
                            Ok(true)
                        } else {
                            proof_irrel(pers, vis, st, mode, lane, fuel, fe, depth, fab, major)
                        };
                        match ir {
                            Err(e) => Err(e),
                            Ok(true) => Ok(fab.dup2()),
                            Ok(false) => Ok(major.dup2()),
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1635-1646 majorToCtor` — the
/// twin's `famK`/`famE`/`famA`: the synthetic-spine certificate, a certificate
/// FAMILY gated on `mode.certs` (task #97f, P2f).  Its own function so the
/// gate's `.trusted` arm does not compute `constTyAt` either — the twin has
/// the lookup INSIDE the branch — and because the three rescues spell it.
pub fn iota_certs_fam(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    ust: &LsIdx,
    spine: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if !con_ron_core::kernel::env::certs(mode) {
        Ok(true)
    } else {
        match const_ty_at(pers, st, cvj, ust) {
            Err(e) => Err(e),
            Ok(tyj) => iota_certs(pers, vis, st, mode, lane, fuel, fe, depth, false, &tyj, spine, 0),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1624-1648 majorToCtor` — the
/// K-flagged branch (`to_cnstr_when_K`): the major's whnf'd type is the rule's
/// own inductive, and the fabricated major is its constructor at the type's
/// leading parameters.
pub fn major_to_ctor_k(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => match view(pers, st, &hd0) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t2, ust)) => match view_ls(pers, st, &ust) {
                        Err(e) => Err(e),
                        Ok(ustl) => {
                            if t2.eq2(t) && cvj.level_params.len() == ustl.len() {
                                match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                                    Err(e) => Err(e),
                                    Ok(targs) => {
                                        if cn_p <= targs.len() as u64 {
                                            let spine: Vec<EIdx> =
                                                take_eidx(&targs, cn_p as usize);
                                            match intern_e(
                                                pers,
                                                st,
                                                ENodeView::Const(ctor.dup2(), ust.dup2()),
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(hd) => {
                                                    match mk_app_n(pers, st, &hd, &spine) {
                                                        Err(e) => Err(e),
                                                        Ok(fab) => major_to_ctor_certs(
                                                            pers,
                                                            vis,
                                                            st, mode, lane, fuel, fe,
                                                            depth, cvj, &ust, &spine,
                                                            &fab, &tmaj, major,
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
                    Ok(_) => Ok(major.dup2()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1662-1673 majorToCtor` — the η
/// rescue's certificate chain, with the structure-eta certificate and the
/// 0-field fallback for the pinned basis `PUnit`.
pub fn major_to_ctor_eta_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    ust: &LsIdx,
    fab_args: &Vec<EIdx>,
    fab: &EIdx,
    tmaj: &EIdx,
    major: &EIdx,
    eta_fields: u64,
) -> Result<EIdx, CheckError> {
    match fab_scope_ok(pers, st, depth, fab, major) {
        Err(e) => Err(e),
        Ok(false) => Ok(major.dup2()),
        // the synthetic-spine certificate, a family (task #97f, P2f;
        // `Cached/CoreC.lean:621`).  The structure-eta certificate below it is
        // the VERDICT, not a family, and runs at both modes.
        Ok(true) => {
            match iota_certs_fam(pers, vis, st, mode, lane, fuel, fe, depth, cvj, ust, fab_args) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(major.dup2()),
                    Ok(true) => {
                        match struct_eta_cert_with(
                            pers,
                            vis,
                            st, mode, lane, fuel, fe, depth, fab, major, tmaj,
                        ) {
                            Err(e) => Err(e),
                            Ok(true) => Ok(fab.dup2()),
                            Ok(false) => {
                                if eta_fields == 0 {
                                    match proof_irrel(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth, fab, major,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(true) => Ok(fab.dup2()),
                                        Ok(false) => Ok(major.dup2()),
                                    }
                                } else {
                                    Ok(major.dup2())
                                }
                            }
                        }
                    }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1649-1675 majorToCtor` — the
/// η-capable branch: the fabricated major is the structure's constructor at
/// the type's parameters and the installed projections of the stuck major.
/// The *instantiated* non-`Prop` test is con-leche's task #61.
pub fn major_to_ctor_eta(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => match view(pers, st, &hd0) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t2, ust)) => match view_ls(pers, st, &ust) {
                        Err(e) => Err(e),
                        Ok(ustl) => match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                            Err(e) => Err(e),
                            Ok(targs) => {
                                match caps_never_zero(pers, st, &cvt.level_params, &ust, caps) {
                                    Err(e) => Err(e),
                                    Ok(nz) => {
                                        if t2.eq2(t)
                                            && targs.len() as u64 == caps.eta_params
                                            && ustl.len() == cvt.level_params.len()
                                            && nz
                                        {
                                            major_to_ctor_eta_build(
                                                pers,
                                                vis,
                                                st, mode, lane, fuel, fe, depth, cvj,
                                                caps, t, &ust, &targs, &tmaj, major,
                                            )
                                        } else {
                                            Ok(major.dup2())
                                        }
                                    }
                                }
                            }
                        },
                    },
                    Ok(_) => Ok(major.dup2()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1659-1661 majorToCtor` — the η
/// branch's fabrication: the argument spine and the constructor application.
pub fn major_to_ctor_eta_build(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    caps: &IIndCaps,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    tmaj: &EIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match eta_fab_args_e(pers, vis, st, fe, t, ust, targs, major, caps.eta_fields) {
        Err(e) => Err(e),
        Ok(fab_args) => {
            match intern_e(pers, st, ENodeView::Const(caps.eta_ctor.dup2(), ust.dup2())) {
                Err(e) => Err(e),
                Ok(hd) => match mk_app_n(pers, st, &hd, &fab_args) {
                    Err(e) => Err(e),
                    Ok(fab) => major_to_ctor_eta_certs(
                        pers,
                        vis,
                        st,
                        mode,
                        lane,
                        fuel,
                        fe,
                        depth,
                        cvj,
                        ust,
                        &fab_args,
                        &fab,
                        tmaj,
                        major,
                        caps.eta_fields,
                    ),
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1677-1704 majorToCtor` — **THE
/// `And`-ONLY η RESCUE** (the user ruling: `And` and nothing else): the
/// fabricated major is `And.intro` at the two `.proj` nodes of the stuck one.
pub fn major_to_ctor_and(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, major) {
        Err(e) => Err(e),
        Ok(tm) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tm) {
            Err(e) => Err(e),
            Ok(tmaj) => match get_app_fn(pers, st, CORE_WALK_FUEL, &tmaj) {
                Err(e) => Err(e),
                Ok(hd0) => match view(pers, st, &hd0) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t2, ust)) => match view_ls(pers, st, &ust) {
                        Err(e) => Err(e),
                        Ok(ustl) => match get_app_args(pers, st, CORE_WALK_FUEL, &tmaj) {
                            Err(e) => Err(e),
                            Ok(targs) => {
                                match and_rescue_slots(pers, vis, st, fe, ctor, cn_p, &ust) {
                                    Err(e) => Err(e),
                                    Ok(ars) => {
                                        if t2.eq2(t)
                                            && targs.len() as u64 == cn_p
                                            && cvj.level_params.len() == ustl.len()
                                            && ars
                                        {
                                            major_to_ctor_and_build(
                                                pers,
                                                vis,
                                                st, mode, lane, fuel, fe, depth, cvj,
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
                    Ok(_) => Ok(major.dup2()),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1688-1701 majorToCtor` — the `And`
/// branch's fabrication and its certificate chain.
pub fn major_to_ctor_and_build(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    ctor: &NIdx,
    t: &NIdx,
    ust: &LsIdx,
    targs: &Vec<EIdx>,
    tmaj: &EIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match intern_e(pers, st, ENodeView::Proj(t.dup2(), 0, major.dup2())) {
        Err(e) => Err(e),
        Ok(p0) => match intern_e(pers, st, ENodeView::Proj(t.dup2(), 1, major.dup2())) {
            Err(e) => Err(e),
            Ok(p1) => {
                let fab_args: Vec<EIdx> =
                    snoc_eidx(snoc_eidx(env::eidx_vec_dup(targs), &p0), &p1);
                match intern_e(pers, st, ENodeView::Const(ctor.dup2(), ust.dup2())) {
                    Err(e) => Err(e),
                    Ok(hd) => match mk_app_n(pers, st, &hd, &fab_args) {
                        Err(e) => Err(e),
                        Ok(fab) => major_to_ctor_certs(
                            pers,
                            vis,
                            st, mode, lane, fuel, fe, depth, cvj, ust, &fab_args, &fab,
                            tmaj, major,
                        ),
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1624-1704 majorToCtor` — the
/// three-way branch on the rule's stamped bits, once the rule's constructor
/// and its inductive have been found.
pub fn major_to_ctor_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cvj: &IConstantVal,
    cn_p: u64,
    ctor: &NIdx,
    k: bool,
    eta: bool,
    cvt: &IConstantVal,
    caps: &IIndCaps,
    t: &NIdx,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    if k {
        major_to_ctor_k(pers, vis, st, mode, lane, fuel, fe, depth, cvj, cn_p, ctor, t, major)
    } else if eta {
        major_to_ctor_eta(pers, vis, st, mode, lane, fuel, fe, depth, cvj, cvt, caps, t, major)
    } else {
        match pin_and(st) {
            Err(e) => Err(e),
            Ok(an) => {
                if t.eq2(&an) {
                    major_to_ctor_and(
                        pers,
                        vis,
                        st, mode, lane, fuel, fe, depth, cvj, cn_p, ctor, t, major,
                    )
                } else {
                    Ok(major.dup2())
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1612-1708 majorToCtor` — **the
/// stuck-major rescue** (`to_cnstr_when_K` and `to_cnstr_when_structure`): a
/// recursor's major premise that does not whnf to a constructor application
/// may still be *replaced* by one — K-flagged, η-capable, or the pinned `And`.
/// An uncertified major stays put.
pub fn major_to_ctor(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    _rec_name: &NIdx,
    rules: &Vec<IRecRule>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    match is_ctor_app(pers, vis, st, fe, major) {
        Err(e) => Err(e),
        Ok(true) => Ok(major.dup2()),
        Ok(false) => {
            if rules.len() != 1 {
                Ok(major.dup2())
            } else {
                let ctor: NIdx = rules[0].ctor.dup2();
                let k: bool = rules[0].k;
                let eta: bool = rules[0].eta;
                match env::ifenv_find(vis, fe, &ctor) {
                    Some(IConstantInfo::CtorInfo(cvj0, cn_p0, _)) => {
                        let cvj: IConstantVal = env::i_constant_val_dup(cvj0);
                        let cn_p: u64 = *cn_p0;
                        match pi_result(pers, st, CORE_WALK_FUEL, &cvj.ty) {
                            Err(e) => Err(e),
                            Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
                                Err(e) => Err(e),
                                Ok(hd) => match view(pers, st, &hd) {
                                    Err(e) => Err(e),
                                    Ok(ENodeView::Const(t, _)) => {
                                        match env::ifenv_find(vis, fe, &t) {
                                            Some(IConstantInfo::IndInfo(cvt0, caps0)) => {
                                                let cvt: IConstantVal =
                                                    env::i_constant_val_dup(cvt0);
                                                let caps: IIndCaps =
                                                    env::i_ind_caps_dup(caps0);
                                                major_to_ctor_at(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth,
                                                    &cvj, cn_p, &ctor, k, eta, &cvt,
                                                    &caps, &t, major,
                                                )
                                            }
                                            Some(_) => Ok(major.dup2()),
                                            None => Ok(major.dup2()),
                                        }
                                    }
                                    Ok(_) => Ok(major.dup2()),
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

/// con-leche: ConLeche/Kernel/Core.lean:728-740 litMajorToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1713-1721 litMajorToCtor` — convert
/// a literal major premise to constructor form: a `Nat` literal one layer, a
/// `String` literal to its *reduced* constructor form.
pub fn lit_major_to_ctor(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lit(Literal::StrVal(s))) => {
            let cs: Vec<u32> = expr::str_copy(&s);
            match str_lit_supported(pers, vis, st, fe) {
                Err(e) => Err(e),
                Ok(false) => Ok(h.dup2()),
                Ok(true) => match str_lit_to_constructor(pers, st, &cs) {
                    Err(e) => Err(e),
                    Ok(c) => knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &c),
                },
            }
        }
        Ok(_) => lit_to_ctor_if_nat(pers, vis, st, fe, h),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:742-756 projLitToCtor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1725-1733 projLitToCtor` — convert
/// a string-literal projection scrutinee to its *reduced* constructor form.
pub fn proj_lit_to_ctor(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lit(Literal::StrVal(s))) => {
            let cs: Vec<u32> = expr::str_copy(&s);
            match str_lit_supported(pers, vis, st, fe) {
                Err(e) => Err(e),
                Ok(false) => Ok(h.dup2()),
                Ok(true) => match str_lit_to_constructor(pers, st, &cs) {
                    Err(e) => Err(e),
                    Ok(c) => knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &c),
                },
            }
        }
        Ok(_) => Ok(h.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:815-830 recRuleKOf
/// Lean twin: `proof/ConRon/Arena/Core.lean:1738-1747 recRuleKOf` — **the K bit
/// at install** (`RecRule.k`): the rule's constructor has no fields and
/// belongs to an inductive stored with the K capability.
pub fn rec_rule_k_of(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    ctor: &NIdx,
) -> Result<bool, CheckError> {
    match env::ifenv_find(vis, fe, ctor) {
        Some(IConstantInfo::CtorInfo(cvj, _, cn_f0)) => {
            let ty: EIdx = cvj.ty.dup2();
            let cn_f: u64 = *cn_f0;
            match pi_result(pers, st, CORE_WALK_FUEL, &ty) {
                Err(e) => Err(e),
                Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
                    Err(e) => Err(e),
                    Ok(hd) => match view(pers, st, &hd) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Const(t, _)) => match env::ifenv_find(vis, fe, &t) {
                            Some(IConstantInfo::IndInfo(_, caps)) => {
                                Ok(caps.rule_k && cn_f == 0)
                            }
                            Some(_) => Ok(false),
                            None => Ok(false),
                        },
                        Ok(_) => Ok(false),
                    },
                },
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:832-858 recRuleEtaOf
/// Lean twin: `proof/ConRon/Arena/Core.lean:1753-1765 recRuleEtaOf` — **the
/// η-rescue bit at install** (`RecRule.eta`).  `Name.isProjFnShape` is a
/// predicate on a `ConLeche.Name`, so the recursor's name is read back for it —
/// an install-time path, never a reduction-time one.
pub fn rec_rule_eta_of(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    rec_name: &NIdx,
    ctor: &NIdx,
) -> Result<bool, CheckError> {
    match env::ifenv_find(vis, fe, ctor) {
        Some(IConstantInfo::CtorInfo(cvj, _, _)) => {
            let ty: EIdx = cvj.ty.dup2();
            let cvj_lps: Vec<NIdx> = env::nidx_vec_dup(&cvj.level_params);
            match pi_result(pers, st, CORE_WALK_FUEL, &ty) {
                Err(e) => Err(e),
                Ok(pr) => match get_app_fn(pers, st, CORE_WALK_FUEL, &pr) {
                    Err(e) => Err(e),
                    Ok(hd) => match view(pers, st, &hd) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Const(t, _)) => match env::ifenv_find(vis, fe, &t) {
                            Some(IConstantInfo::IndInfo(cvt, caps)) => {
                                let eta: bool = caps.eta;
                                let eta_ctor: NIdx = caps.eta_ctor.dup2();
                                let cvt_lps: Vec<NIdx> =
                                    env::nidx_vec_dup(&cvt.level_params);
                                match read_name(pers, st, rec_name) {
                                    Err(e) => Err(e),
                                    Ok(rn) => Ok(eta
                                        && eta_ctor.eq2(ctor)
                                        && !level::name_is_proj_fn_shape(&rn)
                                        && nidx_vec_beq(&cvj_lps, &cvt_lps)),
                                }
                            }
                            Some(_) => Ok(false),
                            None => Ok(false),
                        },
                        Ok(_) => Ok(false),
                    },
                },
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:860-870 recRuleBits
/// Lean twin: `proof/ConRon/Arena/Core.lean:1770-1773 recRuleBits` — **stamp a
/// rule's two rescue bits at install** — the one place the K and η-rescue
/// conditions are decided.  Lean's `{ rl with … }` is a rebuilt record here.
pub fn rec_rule_bits(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    rec_name: &NIdx,
    rl: IRecRule,
) -> Result<IRecRule, CheckError> {
    match rec_rule_k_of(pers, vis, st, fe, &rl.ctor) {
        Err(e) => Err(e),
        Ok(k) => match rec_rule_eta_of(pers, vis, st, fe, rec_name, &rl.ctor) {
            Err(e) => Err(e),
            Ok(eta) => Ok(IRecRule {
                ctor: rl.ctor,
                nfields: rl.nfields,
                ctor_params: rl.ctor_params,
                fire: rl.fire,
                rhs: rl.rhs,
                k,
                eta,
                params_blind: rl.params_blind,
            }),
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:909-921 projFnRule
/// Lean twin: `proof/ConRon/Arena/Core.lean:1778-1785 projFnRule` — **the
/// stored rule of an installed projection function**: the degenerate
/// recursor's single rule, with the two rescue bits stamped by `recRuleBits`.
pub fn proj_fn_rule(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    t: &NIdx,
    ctor_name: &NIdx,
    pty: &EIdx,
    n_p: u64,
    n_f: u64,
    i: u64,
    rhs_a: &EIdx,
) -> Result<IRecRule, CheckError> {
    match rec_rule_plain(pers, st, CORE_WALK_FUEL, pty, n_p, n_p, n_p) {
        Err(e) => Err(e),
        Ok(plain) => match env::proj_fn_name(pers, &mut st.store, t, i) {
            Err(e) => Err(e),
            Ok(nm) => {
                let fire = if plain {
                    IRecRuleFire::Plain
                } else {
                    IRecRuleFire::Inert
                };
                let rl = IRecRule {
                    ctor: ctor_name.dup2(),
                    nfields: n_f,
                    ctor_params: n_p,
                    fire,
                    rhs: rhs_a.dup2(),
                    k: false,
                    eta: false,
                    params_blind: false,
                };
                rec_rule_bits(pers, vis, st, fe, &nm, rl)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:939-946 recRuleK
/// Lean twin: `proof/ConRon/Arena/Core.lean:1789-1792 recRuleK` — is a recursor
/// K-flagged?  The stored bit of its single rule; pure, as con-leche's is.
pub fn rec_rule_k(rules: &Vec<IRecRule>) -> bool {
    if rules.len() == 1 {
        rules[0].k
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:758-795 prepareMajor
/// Lean twin: `proof/ConRon/Arena/Core.lean:1798-1807 prepareMajor` — the major
/// premise's preparation before a rule fires, in the official kernel's order:
/// at a K-flagged recursor the K rescue runs on the **raw** major, elsewhere
/// the major is head-normalized first.
pub fn prepare_major(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    rec_name: &NIdx,
    rules: &Vec<IRecRule>,
    major: &EIdx,
) -> Result<EIdx, CheckError> {
    if rec_rule_k(rules) {
        match major_to_ctor(pers, vis, st, mode, lane, fuel, fe, depth, rec_name, rules, major) {
            Err(e) => Err(e),
            Ok(major_k) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &major_k) {
                Err(e) => Err(e),
                Ok(major0) => {
                    lit_major_to_ctor(pers, vis, st, mode, lane, fuel, fe, depth, &major0)
                }
            },
        }
    } else {
        match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, major) {
            Err(e) => Err(e),
            Ok(major0) => {
                match lit_major_to_ctor(pers, vis, st, mode, lane, fuel, fe, depth, &major0) {
                    Err(e) => Err(e),
                    Ok(major1) => major_to_ctor(
                        pers,
                        vis,
                        st, mode, lane, fuel, fe, depth, rec_name, rules, &major1,
                    ),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:1812-1819 substLevelsAt` — the
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
        match read_level(pers, st, &us[i]) {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:1824-1831 substParamLevels` — the
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
        match read_name(pers, st, &ps[i]) {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:1836-1843 instSpinePins` — the
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
                let head: Vec<EIdx> = take_eidx(args, r_p as usize);
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:1848-1864 recFireComparands` — the
/// level and constructor-parameter comparands a firing rule's checks compare
/// the major's constructor levels and parameters against.
pub fn rec_fire_comparands(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    cvj_lps: &Vec<NIdx>,
    args: &Vec<EIdx>,
    r_p: u64,
) -> Result<(LsIdx, Vec<EIdx>), CheckError> {
    match &rl.fire {
        IRecRuleFire::Nested(lvls, pins) => {
            let lvls2: Vec<LIdx> = env::lidx_vec_dup(lvls);
            let pins2: Vec<EIdx> = env::eidx_vec_dup(pins);
            match read_names(pers, st, lps) {
                Err(e) => Err(e),
                Ok(ks) => match read_levels(pers, st, us) {
                    Err(e) => Err(e),
                    Ok(vs) => {
                        match subst_levels_at(pers, st, &ks, &vs, &lvls2, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(ls) => match intern_ls_node(pers, st, ls) {
                                Err(e) => Err(e),
                                Ok(lsh) => {
                                    match inst_spine_pins(
                                        pers,
                                        st,
                                        lps,
                                        us,
                                        args,
                                        r_p,
                                        &pins2,
                                        0,
                                        Vec::new(),
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(ps) => Ok((lsh, ps)),
                                    }
                                }
                            },
                        }
                    }
                },
            }
        }
        IRecRuleFire::Inert => {
            rec_fire_comparands_plain(pers, st, rl, lps, us, cvj_lps, args)
        }
        IRecRuleFire::Plain => {
            rec_fire_comparands_plain(pers, st, rl, lps, us, cvj_lps, args)
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:948-968 recFireComparands
/// Lean twin: `proof/ConRon/Arena/Core.lean:1859-1864 recFireComparands` — the
/// cited `| _ =>` arm: the canonical rule's comparands.  Spelled once and
/// called from the two non-`nested` constructors, which is what Lean's
/// wildcard is.
pub fn rec_fire_comparands_plain(
    pers: &PersTier,
    st: &mut AState,
    rl: &IRecRule,
    lps: &Vec<NIdx>,
    us: &LsIdx,
    cvj_lps: &Vec<NIdx>,
    args: &Vec<EIdx>,
) -> Result<(LsIdx, Vec<EIdx>), CheckError> {
    match read_names(pers, st, lps) {
        Err(e) => Err(e),
        Ok(ks) => match read_levels(pers, st, us) {
            Err(e) => Err(e),
            Ok(vs) => match subst_param_levels(pers, st, &ks, &vs, cvj_lps, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(ls) => match intern_ls_node(pers, st, ls) {
                    Err(e) => Err(e),
                    Ok(lsh) => Ok((lsh, take_eidx(args, rl.ctor_params as usize))),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1869-1871 findRule` — the rule
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

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1905-1929 iotaRec` — the firing
/// rule's certificate chain: the level comparison, the parameter comparison,
/// the two *licensed* telescope runs, the canonical-index comparison and the
/// right-hand side's application.
pub fn iota_rec_fire(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    cvj: &IConstantVal,
    rl: &IRecRule,
    rec_c: &NIdx,
    us: &LsIdx,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
    major: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match rec_fire_comparands(pers, st, rl, &cv.level_params, us, &cvj.level_params, args, r_p) {
        Err(e) => Err(e),
        Ok(cmp) => match lvls_eq(pers, st, usj, &cmp.0) {
            Err(e) => Err(e),
            Ok(o) => match lift_fueled(o) {
                Err(e) => Err(e),
                Ok(false) => Ok(None),
                Ok(true) => {
                    let p_ok = if env::i_rec_rule_compare_params(rl) {
                        iota_rec_params(
                            pers,
                            vis,
                            st, mode, lane, fuel, fe, depth, rl, rec_c, margs, &cmp.1,
                        )
                    } else {
                        Ok(true)
                    };
                    match p_ok {
                        Err(e) => Err(e),
                        Ok(false) => Ok(None),
                        Ok(true) => iota_rec_certs(
                            pers,
                            vis,
                            st, mode, lane, fuel, fe, depth, cv, cvj, rl, rec_c, us, usj,
                            m_i, r_p, args, margs, major,
                        ),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1943-1959 iotaRec` — the
/// parameter comparison.  It is **verdict-relevant** for a nested rule (the
/// comparands ARE the pins) and for a projection-function rule, and a
/// certificate FAMILY for every other plain rule: `Cached/CoreC.lean:797`'s
/// `certUnlessI` with exactly that `keep` (task #97f, P2f).  The
/// projection-shape test reads the recursor's name BACK and runs con-leche's
/// own pure predicate, as the twin does — this module sits below
/// `arena::checker_base`, whose `nidx_is_proj_fn_shape` is the same test on a
/// handle.
pub fn iota_rec_params(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    rl: &IRecRule,
    rec_c: &NIdx,
    margs: &Vec<EIdx>,
    comparands: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    let keep: Result<bool, CheckError> = match rl.fire {
        IRecRuleFire::Nested(_, _) => Ok(true),
        _ => match read_name(pers, st, rec_c) {
            Err(e) => Err(e),
            Ok(n) => Ok(con_ron_core::kernel::level::name_is_proj_fn_shape(&n)),
        },
    };
    match keep {
        Err(e) => Err(e),
        Ok(k) => {
            if con_ron_core::kernel::env::certs(mode) || k {
                let head: Vec<EIdx> = take_eidx(margs, rl.ctor_params as usize);
                def_eq_list(pers, vis, st, mode, lane, fuel, fe, depth, &head, comparands, 0)
            } else {
                Ok(true)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1960-1980 iotaRec` — **ONE
/// certificate family**: the two *licensed* telescope runs and the
/// canonical-index comparison.  Nothing here is read outside the family, so
/// the whole block is what `.trusted` omits, the two type lookups included
/// (task #97f, P2f; `Cached/CoreC.lean:814`).  Then the reduct.
pub fn iota_rec_certs(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    cvj: &IConstantVal,
    rl: &IRecRule,
    rec_c: &NIdx,
    us: &LsIdx,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
    major: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match iota_rec_fam(
        pers,
        vis,
        st, mode, lane, fuel, fe, depth, cv, cvj, rl, us, usj, m_i, r_p, args, margs,
        major,
    ) {
        Err(e) => Err(e),
        Ok(false) => Ok(None),
        Ok(true) => iota_rec_reduct(pers, st, cv, rl, rec_c, us, r_p, args, margs),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1960-1980 iotaRec` — the family
/// itself, gated on `mode.certs`.
#[allow(clippy::too_many_arguments)]
pub fn iota_rec_fam(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
    cvj: &IConstantVal,
    rl: &IRecRule,
    us: &LsIdx,
    usj: &LsIdx,
    m_i: u64,
    r_p: u64,
    args: &Vec<EIdx>,
    margs: &Vec<EIdx>,
    major: &EIdx,
) -> Result<bool, CheckError> {
    if !con_ron_core::kernel::env::certs(mode) {
        Ok(true)
    } else {
        let lic: bool = con_ron_core::kernel::env::beta_gate(mode);
        match const_ty_at(pers, st, cv, us) {
            Err(e) => Err(e),
            Ok(ty_r) => {
                let spine: Vec<EIdx> = snoc_eidx(take_eidx(args, m_i as usize), major);
                match iota_certs(pers, vis, st, mode, lane, fuel, fe, depth, lic, &ty_r, &spine, 0) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match const_ty_at(pers, st, cvj, usj) {
                        Err(e) => Err(e),
                        Ok(ty_c) => {
                            match iota_certs(
                                pers,
                                vis,
                                st, mode, lane, fuel, fe, depth, lic, &ty_c, margs, 0,
                            ) {
                                Err(e) => Err(e),
                                Ok(false) => Ok(false),
                                Ok(true) => {
                                    let idx: Vec<EIdx> = drop_eidx(
                                        &take_eidx(args, m_i as usize),
                                        r_p as usize,
                                    );
                                    iota_index_ok(
                                        pers,
                                        vis,
                                        st,
                                        mode,
                                        lane,
                                        fuel,
                                        fe,
                                        depth,
                                        m_i,
                                        r_p,
                                        rl.ctor_params,
                                        &ty_c,
                                        margs,
                                        &idx,
                                    )
                                }
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1921-1924 iotaRec` — the ι reduct:
/// the rule's right-hand side at the recursor's levels, applied to the
/// recursor's leading arguments and the constructor's fields.
pub fn iota_rec_reduct(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
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
            let tail: Vec<EIdx> = drop_eidx(margs, rl.ctor_params as usize);
            let spine: Vec<EIdx> = append_eidx(take_eidx(args, r_p as usize), &tail);
            match mk_app_n(pers, st, &rhs, &spine) {
                Err(e) => Err(e),
                Ok(x) => Ok(Some(x)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1891-1931 iotaRec` — the major's
/// side of the step: it whnfs to a fully applied constructor with a matching
/// rule, and a matched *inert* rule is a positive detection of an unsupported
/// feature.
pub fn iota_rec_major(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    cv: &IConstantVal,
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
        Ok(hd) => match view(pers, st, &hd) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(cj, usj)) => match env::ifenv_find(vis, fe, &cj) {
                Some(IConstantInfo::CtorInfo(cvj0, _, _)) => {
                    let cvj: IConstantVal = env::i_constant_val_dup(cvj0);
                    match find_rule(rules, &cj, 0) {
                        None => Ok(None),
                        Some(k) => {
                            let rl: IRecRule = env::i_rec_rule_dup(&rules[k]);
                            match get_app_args(pers, st, CORE_WALK_FUEL, major) {
                                Err(e) => Err(e),
                                Ok(margs) => {
                                    if margs.len() as u64 != rl.ctor_params + rl.nfields {
                                        Ok(None)
                                    } else {
                                        match rl.fire {
                                            IRecRuleFire::Inert => {
                                                fail(CheckError::NotImplemented(
                                                    code_points(&M_NESTED_RULE),
                                                ))
                                            }
                                            _ => iota_rec_fire(
                                                pers,
                                                vis,
                                                st, mode, lane, fuel, fe, depth, cv,
                                                &cvj, &rl, rec_c, us, &usj, m_i, r_p,
                                                args, &margs, major,
                                            ),
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                Some(_) => Ok(None),
                None => Ok(None),
            },
            Ok(_) => Ok(None),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: `proof/ConRon/Arena/Core.lean:1878-1936 iotaRec` — **one iota
/// step**: the expression is a stored recursor applied to exactly its
/// telescope, the major premise whnfs to a fully applied constructor with a
/// matching rule, and the spine is certified against the recursor's own
/// (pinned, annotated) type.
pub fn iota_rec(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok(hd) => match get_app_args(pers, st, CORE_WALK_FUEL, e) {
            Err(er) => Err(er),
            Ok(args) => {
                let n: usize = args.len();
                iota_rec_at(pers, vis, st, mode, lane, fuel, fe, depth, &hd, &args, n)
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// Lean twin: OWED (task #97-P6-9's ledger) — `iotaRec` with its two spine
/// walks HOISTED: the head and the argument vector are the caller's, and `n`
/// says how many of `sargs` the expression `e` applies.
///
/// `whnf_app` (task #97-P6-9) has both already — it walked the spine once —
/// and the spec-shaped body it replaces called `iotaRec` on every prefix of
/// the spine, so `getAppFn`+`getAppArgs` were walked once per argument: a
/// quadratic that neither checker's shape needs.  The arity test moves in
/// front of the level-list read for the same reason (both are pure tests of
/// the same conjunction, and the arity one is O(1) here).
pub fn iota_rec_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    hd: &EIdx,
    sargs: &Vec<EIdx>,
    n: usize,
) -> Result<Option<EIdx>, CheckError> {
    {
        match view(pers, st, hd) {
            Err(er) => Err(er),
            Ok(ENodeView::Const(c, us)) => match env::ifenv_find(vis, fe, &c) {
                Some(IConstantInfo::RecInfo(cv0, m_i0, r_p0, rules0)) => {
                    let m_i: u64 = *m_i0;
                    // **The arity test hoisted over the copies** (task
                    // #97-P6-10), the move this function's note already makes
                    // for the level-list read.  `whnf_app` asks `iota_rec_at`
                    // at every reduction step and the answer is `none` at the
                    // wrong arity, so copying the recursor's `IConstantVal`
                    // and its whole rule vector first — Lean shares both by
                    // value; the Rust copies (DESIGN.md §3.2) — is work for a
                    // branch that reads neither.  Both are pure tests of the
                    // same conjunction and this one is `O(1)`.
                    if n as u64 != m_i + 1 {
                        Ok(None)
                    } else {
                        let cv: IConstantVal = env::i_constant_val_dup(cv0);
                        let r_p: u64 = *r_p0;
                        let rules: Vec<IRecRule> = env::i_rec_rules_dup(rules0);
                        let args: Vec<EIdx> = take_eidx(sargs, n);
                        match view_ls_len(pers, st, &us) {
                            None => fail_dangling_ls(),
                            Some(usl) => {
                                if args.len() as u64 == m_i + 1
                                    && usl == cv.level_params.len()
                                {
                                    match intern_e(pers, st, ENodeView::BVar(0)) {
                                        Err(er) => Err(er),
                                        Ok(b0) => {
                                            let maj0: EIdx = get_d_eidx(&args, m_i, &b0);
                                            match prepare_major(
                                                pers,
                                                vis,
                                                st, mode, lane, fuel, fe, depth, &c,
                                                &rules, &maj0,
                                            ) {
                                                Err(er) => Err(er),
                                                Ok(major) => iota_rec_major(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, &cv,
                                                    &rules, &c, &us, m_i, r_p, &args,
                                                    &major,
                                                ),
                                            }
                                        }
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
                        }
                    }
                }
                Some(_) => Ok(None),
                None => Ok(None),
            },
            Ok(_) => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// The projection certificate and the reduction bodies (`Core.lean:1939-2087`)
// ---------------------------------------------------------------------------

/// con-leche: none — `List.reverse` on a `Vec`; Lean's list reverse is a value
/// Lean twin: `proof/ConRon/Arena/Core.lean:1951 IProjEntry.typeAt` — the cited
/// `targs.reverse`.
pub fn rev_eidx(xs: &Vec<EIdx>) -> Vec<EIdx> {
    rev_eidx_from(xs, xs.len(), Vec::new())
}

/// con-leche: none — `List.reverse` on a `Vec`; Lean's list reverse is a value
/// Lean twin: `proof/ConRon/Arena/Core.lean:1951 IProjEntry.typeAt` — the
/// cursor recursion behind `rev_eidx`, counting down.
pub fn rev_eidx_from(xs: &Vec<EIdx>, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i == 0 {
        out
    } else {
        let mut out = out;
        out.push(xs[i - 1].dup2());
        rev_eidx_from(xs, i - 1, out)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt
/// Lean twin: `proof/ConRon/Arena/Core.lean:1948-1951 IProjEntry.typeAt` —
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
            let vs: Vec<EIdx> = cons_eidx(pe, &rev_eidx(targs));
            instantiate_list_fast(pers, st, CORE_WALK_FUEL, &b, &vs, 0)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:912-947 projCert
/// Lean twin: `proof/ConRon/Arena/Core.lean:1957-1963 projCert` — **the
/// structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)` fires
/// only after its constructor spine is certified against `C`'s stored type at
/// the redex's own levels.
pub fn proj_cert(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    lic: bool,
    c: &NIdx,
    us: &LsIdx,
    args: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    match env::ifenv_find(vis, fe, c) {
        Some(IConstantInfo::CtorInfo(cvc0, _, _)) => {
            let cvc: IConstantVal = env::i_constant_val_dup(cvc0);
            match const_ty_at(pers, st, &cvc, us) {
                Err(e) => Err(e),
                Ok(ty) => iota_certs(pers, vis, st, mode, lane, fuel, fe, depth, lic, &ty, args, 0),
            }
        }
        Some(_) => Ok(false),
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:949-961 projCertAt
/// Lean twin: `proof/ConRon/Arena/Core.lean:1968-1970 projCertAt` — **the fire
/// certificate as the mode runs it**: the P core certifies the constructor
/// spine; the parity core is the official kernel's, which certifies nothing.
pub fn proj_cert_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    verified: bool,
    lic: bool,
    c: &NIdx,
    us: &LsIdx,
    args: &Vec<EIdx>,
) -> Result<bool, CheckError> {
    if verified {
        proj_cert(pers, vis, st, mode, lane, fuel, fe, depth, lic, c, us, args)
    } else {
        Ok(true)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:981-1013 betaGateFires
/// Lean twin: `proof/ConRon/Arena/Core.lean:1976-1977 betaGateFires` — **THE β
/// SITE'S GATE**: at `mode.betaGate` a λ-binder whose *validated* annotation
/// datum is `.never` licenses skipping the certificate.  Mode-and-datum only,
/// so it is decidable before the certificate would have started.
pub fn beta_gate_fires(mode: &CheckMode, pw: &PropWhen) -> bool {
    con_ron_core::kernel::env::beta_gate(mode) && prop_when::is_never(pw)
}

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2011-2034 whnfCoreBody`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:67-88 whnfCoreBodyGated`
/// The `.proj` clause, which the plain and the gated body share verbatim: the
/// projection rule, with its scrutinee's string-literal expansion and its fire
/// certificate.  The twin writes the same twenty-four lines in both modules;
/// the port writes them once and both bodies call it.
pub fn whnf_core_proj(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, pe) {
        Err(e) => Err(e),
        Ok(e0) => match proj_lit_to_ctor(pers, vis, st, mode, lane, fuel, fe, depth, &e0) {
            Err(e) => Err(e),
            Ok(ep) => match env::ifenv_find_proj(pers, vis, &mut st.store, fe, sn, i) {
                Err(e) => Err(e),
                Ok(Some(entry)) => {
                    whnf_core_proj_at(pers, vis, st, mode, lane, fuel, fe, depth, sn, i, &ep, &entry)
                }
                Ok(None) => intern_e(pers, st, ENodeView::Proj(sn.dup2(), i, ep)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2017-2034 whnfCoreBody` — the
/// projection rule at a tower entry: the scrutinee's head must be the entry's
/// constructor at the right arities, and the fire certificate must hold.
pub fn whnf_core_proj_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    ep: &EIdx,
    entry: &IProjEntry,
) -> Result<EIdx, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, ep) {
        Err(e) => Err(e),
        Ok(hd) => match view(pers, st, &hd) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(c, us)) => match get_app_args(pers, st, CORE_WALK_FUEL, ep) {
                Err(e) => Err(e),
                Ok(args) => match view_ls_len(pers, st, &us) {
                    None => fail_dangling_ls(),
                    Some(usl) => match proj_entry_fire_ok(pers, st, entry, &us) {
                        Err(e) => Err(e),
                        Ok(fok) => {
                            if c.eq2(&entry.ctor)
                                && i < entry.num_fields
                                && args.len() as u64
                                    == entry.num_params + entry.num_fields
                                && usl == entry.level_params.len()
                                && fok
                            {
                                whnf_core_proj_fire(
                                    pers,
                                    vis,
                                    st, mode, lane, fuel, fe, depth, sn, i, ep, entry,
                                    &c, &us, &args,
                                )
                            } else {
                                intern_e(pers, st, ENodeView::Proj(sn.dup2(), i, ep.dup2()))
                            }
                        }
                    },
                },
            },
            Ok(_) => intern_e(pers, st, ENodeView::Proj(sn.dup2(), i, ep.dup2())),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2026-2032 whnfCoreBody` — the fire
/// itself: the selected field, behind the mode's certificate.
pub fn whnf_core_proj_fire(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    ep: &EIdx,
    entry: &IProjEntry,
    c: &NIdx,
    us: &LsIdx,
    args: &Vec<EIdx>,
) -> Result<EIdx, CheckError> {
    match intern_e(pers, st, ENodeView::BVar(0)) {
        Err(e) => Err(e),
        Ok(b0) => {
            let arg: EIdx = get_d_eidx(args, entry.num_params + i, &b0);
            let verified: bool = con_ron_core::kernel::env::verified_checks(mode);
            let lic: bool = con_ron_core::kernel::env::beta_gate(mode);
            match proj_cert_at(
                pers,
                vis,
                st, mode, lane, fuel, fe, depth, verified, lic, c, us, args,
            ) {
                Err(e) => Err(e),
                Ok(true) => knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &arg),
                Ok(false) => intern_e(pers, st, ENodeView::Proj(sn.dup2(), i, ep.dup2())),
            }
        }
    }
}

/// con-leche: none — `getAppFn` and `getAppArgsC` in one descent, plus the
/// spine's own application NODES (the arena's upward cutoff needs them)
/// Lean twin: OWED (task #97-P6-9's ledger) — `Expr.getAppFn e`,
/// `Expr.getAppArgsC e` and the list of prefixes `e` is built from.
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
/// Lean twin: OWED (task #97-P6-9's ledger) — the cursor recursion behind
/// `get_app_spine`.
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
/// Lean twin: OWED (task #97-P6-9's ledger) — the head and the argument vector
/// of a term, as `whnf_app` needs them for its ι step.
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

/// con-leche: ConLeche/Cached/CoreC.lean:857-900 whnfAppI
/// Lean twin: OWED (task #97-P6-9's ledger) — the cached tier's bulk-β
/// argument loop, the EXECUTED checker's own `.app` clause.
///
/// **The batched instantiation lever** (task #97-P6-9, DESIGN §8's ruling
/// before §8.7).  The spec-shaped body this replaces re-entered the knot once
/// per argument, so a λ-chain of `n` binders applied to `n` arguments cost `n`
/// substitution walks and interned `n − 1` intermediate λ nodes; this loop
/// consumes the whole spine against the whnf'd head `v` and hands a
/// consecutive run of λ binders to `beta_peel`, which substitutes the
/// accumulated argument vector in ONE `instantiate_list` walk.  con-leche
/// makes the same move between its PURE and its CACHED tier and proves the two
/// equal: `ConLeche/Verify/BetaSpine.lean`'s `whnfApp_sound` /
/// `whnfApp_sound_body`, whose per-argument decomposition is
/// `Expr.instantiateList_cons` (`ConLeche/Verify/InstList.lean`).
///
/// Three things travel with `v`, and all three are bookkeeping the spec-shaped
/// body got for free from its own recursion:
///   * `same` — `v` still IS the function part of `nodes[i]`, which is task
///     #97-P6-5's upward cutoff (`intern_app_rebuilt`);
///   * `hd` and `vargs` — `v = mkAppN hd vargs`, so that the ι step is
///     `iota_rec_at` and not a fresh `getAppFn`/`getAppArgs` walk per argument
///     (the spec shape's is quadratic in the spine);
///   * `i` — the cursor into `args`, which is the twin's list pattern.
pub fn whnf_app(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        Ok(v.dup2())
    } else {
        let a: EIdx = args[i].dup2();
        let node: EIdx = nodes[i].dup2();
        match view(pers, st, v) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(ty, body, mb)) => {
                // **THE β SITE'S GATE** (task #97f, P2f): the EXECUTED core
                // reads `CheckMode.betaSkip` (`Cached/CoreC.lean:876`/`:918`), which
                // is `beta_gate_fires` weakened by `!mode.certs` — the β
                // certificate is a certificate FAMILY, skipped wholesale at
                // `.trusted`.  The two agree at `.verified`, the mode the
                // bridge is stated at.
                if con_ron_core::kernel::env::beta_skip(mode, &mb.pw) {
                    let acc: Vec<EIdx> = cons_eidx(&a, &Vec::new());
                    beta_peel(
                        pers, vis, st, mode, lane, fuel, fe, depth, &body, &acc, args, nodes,
                        i + 1,
                    )
                } else {
                    // con-leche's task #172 B4: the certificate's inference
                    // runs at the io grade.
                    match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &a) {
                        Err(e) => Err(e),
                        Ok(ta) => {
                            match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &ta, &ty) {
                                Err(e) => Err(e),
                                Ok(true) => {
                                    let acc: Vec<EIdx> = cons_eidx(&a, &Vec::new());
                                    beta_peel(
                                        pers, vis, st, mode, lane, fuel, fe, depth, &body, &acc,
                                        args, nodes, i + 1,
                                    )
                                }
                                // The certificate failed: the redex is stuck.
                                // ι cannot fire under a λ head, so the twin's
                                // `mkAppNM fa rest` re-applies the rest without
                                // another ι attempt, and so does this.
                                Ok(false) => {
                                    match intern_app_rebuilt(pers, st, &node, same, v, &a) {
                                        Err(e) => Err(e),
                                        Ok(fa) => mk_app_n_from(pers, st, &fa, args, i + 1),
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // The stuck step: `whnf_core_stuck_app`'s two lines, opened up so
            // that the head and the argument vector can be carried rather than
            // re-walked — applying one more argument to a spine does NOT move
            // its head, and its argument vector is one `push`.
            Ok(_) => match intern_app_rebuilt(pers, st, &node, same, v, &a) {
                Err(e) => Err(e),
                Ok(ap) => {
                    let same2: bool = ap.eq2(&node);
                    let mut va: Vec<EIdx> = vargs;
                    va.push(a);
                    let n: usize = va.len();
                    let step = if hd.tag() == ETAG_CONST {
                        iota_rec_at(pers, vis, st, mode, lane, fuel, fe, depth, hd, &va, n)
                    } else {
                        // `iotaRec`'s own first two steps are `getAppFn` and a
                        // `.const` match, so a spine whose head is anything
                        // else returns `none` from every prefix: con-leche's
                        // `iotaArityOk` guard, in the form the arena can spell
                        // off the handle's tag.
                        Ok(None)
                    };
                    match step {
                        Err(e) => Err(e),
                        Ok(None) => whnf_app(
                            pers, vis, st, mode, lane, fuel, fe, depth, &ap, hd, va, same2,
                            args, nodes, i + 1,
                        ),
                        Ok(Some(e2)) => {
                            match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &e2) {
                                Err(e) => Err(e),
                                Ok(v2) => match head_and_args(pers, st, &v2) {
                                    Err(e) => Err(e),
                                    Ok(hv) => whnf_app(
                                        pers, vis, st, mode, lane, fuel, fe, depth, &v2, &hv.0,
                                        hv.1, false, args, nodes, i + 1,
                                    ),
                                },
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:902-938 betaPeelI
/// Lean twin: OWED (task #97-P6-9's ledger) — the peel loop of `whnf_app`.
///
/// `t` is the RAW (unsubstituted) λ body after the binders consumed so far and
/// `acc` their arguments, innermost first — so `acc` is exactly the list
/// `instantiate_list` takes at cursor `0`, and `instantiateList e (v :: vs) d =
/// (instantiateList e vs (d + 1)).instantiate1 v d`
/// (`ConLeche/Verify/InstList.lean`'s `instantiateList_cons`) is the equation
/// that identifies one peeled group with the chain of `instantiate1` the
/// spec-shaped body ran.  Each binder's certificate substitutes only its
/// DOMAIN; the body is substituted once, when peeling stops.
pub fn beta_peel(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    t: &EIdx,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    nodes: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, acc, 0) {
            Err(e) => Err(e),
            Ok(e2) => knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &e2),
        }
    } else {
        let a: EIdx = args[i].dup2();
        match view(pers, st, t) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(ty, body, mb)) => {
                if con_ron_core::kernel::env::beta_skip(mode, &mb.pw) {
                    let acc2: Vec<EIdx> = cons_eidx(&a, acc);
                    beta_peel(
                        pers, vis, st, mode, lane, fuel, fe, depth, &body, &acc2, args, nodes,
                        i + 1,
                    )
                } else {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, acc, 0) {
                        Err(e) => Err(e),
                        Ok(ty2) => {
                            match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &a) {
                                Err(e) => Err(e),
                                Ok(ta) => match knot_defeq(
                                    pers, vis, st, mode, lane, fuel, fe, depth, &ta, &ty2,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(true) => {
                                        let acc2: Vec<EIdx> = cons_eidx(&a, acc);
                                        beta_peel(
                                            pers, vis, st, mode, lane, fuel, fe, depth, &body,
                                            &acc2, args, nodes, i + 1,
                                        )
                                    }
                                    Ok(false) => {
                                        match instantiate_list_fast(
                                            pers, st, CORE_WALK_FUEL, t, acc, 0,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(f2) => match intern_app(pers, st, &f2, &a) {
                                                Err(e) => Err(e),
                                                Ok(fa) => {
                                                    mk_app_n_from(pers, st, &fa, args, i + 1)
                                                }
                                            },
                                        }
                                    }
                                },
                            }
                        }
                    }
                }
            }
            Ok(_) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, acc, 0) {
                Err(e) => Err(e),
                Ok(e2) => match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &e2) {
                    Err(e) => Err(e),
                    // The peeled group is over and the spine is not: the twin
                    // re-enters `whnfAppI` at the SAME argument.  A β has
                    // happened, so the accumulated head is no longer the
                    // original prefix and the upward cutoff is OFF.
                    Ok(v2) => match head_and_args(pers, st, &v2) {
                        Err(e) => Err(e),
                        Ok(hv) => whnf_app(
                            pers, vis, st, mode, lane, fuel, fe, depth, &v2, &hv.0, hv.1, false,
                            args, nodes, i,
                        ),
                    },
                },
            },
        }
    }
}

/// con-leche: none — `internE (.app f' a)`, the twin's one-line rebuild
/// Lean twin: `proof/ConRon/Arena/Core.lean:2005 whnfCoreBody` — the stuck
/// application, re-interned.  Its own function because both the plain and the
/// gated β arm end in it.
pub fn intern_app(
    pers: &PersTier,
    st: &mut AState,
    f: &EIdx,
    a: &EIdx,
) -> Result<EIdx, CheckError>  {
    intern_e(pers, st, ENodeView::App(f.dup2(), a.dup2()))
}

/// con-leche: none — `internE (.app f' a)`, the twin's one-line rebuild
/// Lean twin: OWED (task #97-P6-7's twin ledger) — **the UPWARD cutoff at the
/// stuck application**, `expr_ops::intern_rebuilt`'s clause where task
/// #97-P6-5's lever 2 could not reach.
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

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2006-2010 whnfCoreBody`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:63-66 whnfCoreBodyGated` — the
/// `.app` clause's non-λ head: the ι step on the re-interned application.  The
/// plain and the gated body write the same five lines; the port writes them
/// once.
pub fn whnf_core_stuck_app(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
    same: bool,
    fp: &EIdx,
    a: &EIdx,
) -> Result<EIdx, CheckError> {
    match intern_app_rebuilt(pers, st, h, same, fp, a) {
        Err(e) => Err(e),
        Ok(ap) => match iota_rec(pers, vis, st, mode, lane, fuel, fe, depth, &ap) {
            Err(e) => Err(e),
            Ok(Some(e2)) => knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &e2),
            Ok(None) => Ok(ap),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:1985-2040 whnfCoreBody` — the
/// head-normalization body: beta (with the per-redex argument certificate),
/// iota (with the stuck-major machinery) and the projection rule — but **no
/// delta**.  Values return themselves, which over handles is the handle
/// itself: hash-consing makes `.sort u` interned from a `.sort u` view the
/// same node.
pub fn whnf_core_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Sort(_)) => Ok(e.dup2()),
        Ok(ENodeView::FVar(_, _)) => Ok(e.dup2()),
        Ok(ENodeView::ForallE(_, _, _)) => Ok(e.dup2()),
        Ok(ENodeView::Lam(_, _, _)) => Ok(e.dup2()),
        Ok(ENodeView::Const(_, _)) => Ok(e.dup2()),
        Ok(ENodeView::Lit(_)) => Ok(e.dup2()),
        // **The batched β spine** (task #97-P6-9), con-leche's
        // `Cached/CoreC.lean:942-996 whnfCoreStepI`'s own `.app` clause: the
        // spine's head is normalized once and the whole argument vector is run
        // through `whnf_app`, which batches a consecutive run of λ binders into
        // ONE `instantiate_list` walk.  The spec-shaped clause this replaces
        // re-entered the knot per argument.
        Ok(ENodeView::App(_, _)) => {
            match get_app_spine(pers, st, CORE_WALK_FUEL, e) {
                Err(er) => Err(er),
                Ok(sp) => {
                    let hd: EIdx = sp.0;
                    let args: Vec<EIdx> = sp.1;
                    let nodes: Vec<EIdx> = sp.2;
                    match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &hd) {
                        Err(er) => Err(er),
                        Ok(v) => {
                            let same: bool = v.eq2(&hd);
                            match head_and_args(pers, st, &v) {
                                Err(er) => Err(er),
                                Ok(hv) => whnf_app(
                                    pers, vis, st, mode, lane, fuel, fe, depth, &v, &hv.0, hv.1,
                                    same, &args, &nodes, 0,
                                ),
                            }
                        }
                    }
                }
            }
        }
        Ok(ENodeView::Proj(sn, i, pe)) => {
            whnf_core_proj(pers, vis, st, mode, lane, fuel, fe, depth, &sn, i, &pe)
        }
        // **Unreachable by construction** (con-leche's task #241): annotate
        // output is let-free.
        Ok(ENodeView::LetE(_, _, _)) => {
            fail(CheckError::Internal(code_points(&M_LET_WHNF)))
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_WHNF)))
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1054-1062 whnfCoreLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2049 whnfCoreLoopFuel` — step budget
/// of the `whnfCore` head-normalization loop.  The arena's `whnfCoreBody` is
/// con-leche's SPEC shape — beta, iota and projection steps chained through
/// the knot, not iterated in a local loop — so this budget has **no reader**
/// here yet; it is twinned because the executed loop
/// (`Cached/CoreC.lean`'s `whnfCoreLoopI`) is what P2g will measure against,
/// and its budget must be the same number.
pub const WHNF_CORE_LOOP_FUEL: u64 = 1000000;

/// con-leche: ConLeche/Kernel/Core.lean:1064-1071 whnfLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2054 whnfLoopFuel` — step budget of
/// the `whnf` reduction loop (lean4lean's `FuelConfig.whnf`, same value).
/// Literal-acceleration and delta steps are *iteration*, not recursion.
pub const WHNF_LOOP_FUEL: u64 = 100000;

/// con-leche: ConLeche/Kernel/Core.lean:1073-1088 whnfStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2059-2067 whnfStep` — one iteration
/// of the reduction loop: head-normalize, try literal acceleration, unfold one
/// definition — and hand the reduct to the loop's continuation.  The twin's
/// `k : EIdx → AM EIdx` is the loop's step budget `n` here (the module note's
/// deviation 2); `k x` is `whnf_loop(…, n, x)`, which is what `whnfLoop`
/// passes.
pub fn whnf_step(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, e) {
        Err(er) => Err(er),
        Ok(e1) => match reduce_nat(pers, vis, st, mode, lane, fuel, fe, depth, &e1) {
            Err(er) => Err(er),
            Ok(Some(e2)) => whnf_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, &e2),
            Ok(None) => match unfold_definition(pers, vis, st, fe, &e1) {
                Err(er) => Err(er),
                Ok(Some(e2)) => whnf_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, &e2),
                Ok(None) => Ok(e1),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1090-1095 whnfLoop
/// Lean twin: `proof/ConRon/Arena/Core.lean:2072-2074 whnfLoop` — the reduction
/// loop: iterate `whnfStep` on its own step budget, so the whole chain costs
/// one knot level however many steps it takes.
pub fn whnf_loop(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if n == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF_LOOP)))
    } else {
        whnf_step(pers, vis, st, mode, lane, fuel, fe, depth, n - 1, e)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1097-1099 whnfBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2078-2079 whnfBody` — the reduction
/// loop's body: run `whnfLoop` at its own step budget.
pub fn whnf_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    whnf_loop(pers, vis, st, mode, lane, fuel, fe, depth, WHNF_LOOP_FUEL, e)
}

/// con-leche: ConLeche/Kernel/Core.lean:1101-1107 ensureSort
/// Lean twin: `proof/ConRon/Arena/Core.lean:2083-2087 ensureSort` — ensure `e`
/// (the type of some expression) is a sort, returning its level.
pub fn ensure_sort(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<LIdx, CheckError> {
    match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, e) {
        Err(er) => Err(er),
        Ok(w) => match view(pers, st, &w) {
            Err(er) => Err(er),
            Ok(ENodeView::Sort(u)) => Ok(u),
            Ok(_) => fail(CheckError::Invalid(code_points(&M_SORT))),
        },
    }
}

// ---------------------------------------------------------------------------
// Inference (`Core.lean:2089-2339`)
//
// `inferBody` and `inferBodyIO` differ in exactly two clauses (the λ's domain
// sort and the application's per-argument certificate) and agree verbatim in
// the other eight.  The twin writes both out in full, as con-leche does; the
// port spells each shared clause once and calls it from both, which is
// `con_ron_core::cached::core_c`'s own arrangement (`infer_const_i`,
// `infer_lit_nat`, `infer_fvar`, `infer_proj_at`).
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2093-2095 inferLamResult` — the λ
/// clause's result, `.forallE ty (bt.abstract1 depth) mb`.  con-leche writes it
/// once at the end of a clause with three exits; the arena names it, so the
/// three exits share one spelling and no arm is duplicated.
pub fn infer_lam_result(
    pers: &PersTier,
    st: &mut AState,
    ty: &EIdx,
    bt: &EIdx,
    depth: u64,
    mb: &BinderMeta,
) -> Result<EIdx, CheckError> {
    match abstract1_fast(pers, st, CORE_WALK_FUEL, bt, depth, 0) {
        Err(e) => Err(e),
        Ok(ab) => intern_e(
            pers,
            st,
            ENodeView::ForallE(ty.dup2(), ab, expr::binder_meta_dup(mb)),
        ),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2105-2107 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2230-2232 inferBodyIO`
/// The `.sort` clause, which both bodies write identically.
pub fn infer_sort(pers: &PersTier, st: &mut AState, u: &LIdx) -> Result<EIdx, CheckError> {
    match intern_l_node(pers, st, LNodeView::Succ(u.dup2())) {
        Err(e) => Err(e),
        Ok(su) => intern_e(pers, st, ENodeView::Sort(su)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2108-2111 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2233-2235 inferBodyIO`
/// The `.fvar` clause — the scope check at the leaf of a traversal that
/// happens anyway — which both bodies write identically.
pub fn infer_fvar(idx: u64, ty: &EIdx, depth: u64) -> Result<EIdx, CheckError> {
    if idx < depth {
        Ok(ty.dup2())
    } else {
        fail(CheckError::Invalid(code_points(&M_FVAR)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2112-2128 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2236-2251 inferBodyIO`
/// The `.const` clause, which both bodies write identically: the stored type
/// read through `constTyAt`, so a constant inferred twice at the same levels
/// pays the level substitution once.  A projection table is not a term
/// (con-leche's task #175 W4c).
pub fn infer_const(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    n: &NIdx,
    us: &LsIdx,
) -> Result<EIdx, CheckError> {
    match env::ifenv_find(vis, fe, n) {
        None => match unknown_const_error(st, n) {
            Err(e) => Err(e),
            Ok(err) => fail(err),
        },
        Some(ci) => {
            if env::i_constant_info_is_tower_entry(ci) {
                fail(CheckError::Invalid(code_points(&M_TOWER)))
            } else {
                match env::i_constant_info_to_constant_val(pers, &mut st.store, ci) {
                    Err(e) => Err(e),
                    Ok(cv) => match view_ls_len(pers, st, us) {
                        None => fail_dangling_ls(),
                        Some(usl) => {
                            if usl != cv.level_params.len() {
                                fail(CheckError::Invalid(code_points(&M_LEVELS)))
                            } else {
                                const_ty_at(pers, st, &cv, us)
                            }
                        }
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2129-2133 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2252-2256 inferBodyIO`
/// The `.lit (.natVal _)` clause, which both bodies write identically.
pub fn infer_lit_nat(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<EIdx, CheckError>  {
    match nat_lit_supported(pers, vis, st, fe) {
        Err(e) => Err(e),
        Ok(true) => match pin_nat(st) {
            Err(e) => Err(e),
            Ok(nn) => const_e(pers, st, &nn),
        },
        Ok(false) => fail(CheckError::Invalid(code_points(&M_NAT))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2134-2139 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2257-2262 inferBodyIO`
/// The `.lit (.strVal _)` clause, which both bodies write identically.
pub fn infer_lit_str(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
) -> Result<EIdx, CheckError>  {
    match str_lit_supported(pers, vis, st, fe) {
        Err(e) => Err(e),
        Ok(true) => match pin_string(st) {
            Err(e) => Err(e),
            Ok(sn) => const_e(pers, st, &sn),
        },
        Ok(false) => fail(CheckError::NotImplemented(code_points(&M_STR))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2140-2156 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2263-2279 inferBodyIO`
/// The `.forallE` clause, which both bodies write identically: the domain's
/// sort, the opened codomain's sort, the validated annotation and `imax`.
pub fn infer_forall(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => match view(pers, st, &w) {
                Err(e) => Err(e),
                // Binder-telescope loop (con-leche's task #72, `inferBodyI`'s
                // `.forallE` case): peel the whole ∀-chain, open in bulk, fold
                // `imax` outward.  The first binder is peeled here, which is why
                // `infer_pis` starts at `k = 1` with one free variable and a
                // one-entry stack.
                Ok(ENodeView::Sort(u)) => {
                    match intern_e(pers, st, ENodeView::FVar(depth, ty.dup2())) {
                        Err(e) => Err(e),
                        Ok(fv) => {
                            let fvs: Vec<EIdx> = cons_eidx(&fv, &Vec::new());
                            let mut stk: Vec<(LIdx, PropWhen)> = Vec::new();
                            stk.push((u, prop_when::dup(&mb.pw)));
                            infer_pis(
                                pers, vis, st, mode, lane, fuel, fe, depth, PEEL_FUEL, body, 1,
                                &fvs, stk,
                            )
                        }
                    }
                }
                Ok(_) => fail(CheckError::Invalid(code_points(&M_SORT))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2191-2215 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2313-2335 inferBodyIO`
/// The `.proj` clause, which both bodies write identically: the subject type's
/// head must be the node's own structure name (con-leche's task #175 wiring
/// W5), and a projection out of a propositional structure must land in `Prop`.
pub fn infer_proj(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, pe) {
        Err(e) => Err(e),
        Ok(tp) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tp) {
            Err(e) => Err(e),
            Ok(te) => match get_app_fn(pers, st, CORE_WALK_FUEL, &te) {
                Err(e) => Err(e),
                Ok(hd) => match view(pers, st, &hd) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t, us)) => {
                        match env::ifenv_find_proj(pers, vis, &mut st.store, fe, &t, i) {
                            Err(e) => Err(e),
                            Ok(Some(entry)) => {
                                infer_proj_at(pers, st, &te, sn, pe, &t, &us, &entry)
                            }
                            Ok(None) => {
                                fail(CheckError::NotImplemented(code_points(&M_NOENTRY)))
                            }
                        }
                    }
                    Ok(_) => fail(CheckError::NotImplemented(code_points(&M_NOENTRY))),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2196-2213 inferBody` — the `.proj`
/// clause's body, once the entry has been found.
pub fn infer_proj_at(
    pers: &PersTier,
    st: &mut AState,
    te: &EIdx,
    sn: &NIdx,
    pe: &EIdx,
    t: &NIdx,
    us: &LsIdx,
    entry: &IProjEntry,
) -> Result<EIdx, CheckError> {
    match get_app_args(pers, st, CORE_WALK_FUEL, te) {
        Err(e) => Err(e),
        Ok(targs) => match view_ls_len(pers, st, us) {
            None => fail_dangling_ls(),
            Some(usl) => {
                if t.eq2(sn)
                    && targs.len() as u64 == entry.num_params
                    && usl == entry.level_params.len()
                {
                    match zero_level(st) {
                        Err(e) => Err(e),
                        Ok(z) => match lvl_eq(pers, st, &entry.struct_sort, &z) {
                            Err(e) => Err(e),
                            Ok(Some(true)) => {
                                infer_proj_prop(pers, st, entry, us, &targs, pe)
                            }
                            Ok(_) => proj_entry_type_at(pers, st, entry, us, &targs, pe),
                        },
                    }
                } else {
                    fail(CheckError::NotImplemented(code_points(&M_NOENTRY)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2204-2211 inferBody` — the
/// propositional structure's extra premise: the field's guard level must be
/// `Prop` at this instantiation.
pub fn infer_proj_prop(
    pers: &PersTier,
    st: &mut AState,
    entry: &IProjEntry,
    us: &LsIdx,
    targs: &Vec<EIdx>,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match read_names(pers, st, &entry.level_params) {
        Err(e) => Err(e),
        Ok(ks) => match read_levels(pers, st, us) {
            Err(e) => Err(e),
            Ok(vs) => match read_level(pers, st, &entry.field_sort) {
                Err(e) => Err(e),
                Ok(fs) => {
                    let s = level::subst(&ks, &vs, &fs);
                    match level::is_equiv(&s, &level::zero()) {
                        Some(true) => proj_entry_type_at(pers, st, entry, us, targs, pe),
                        Some(false) => {
                            fail(CheckError::Invalid(code_points(&M_PROP)))
                        }
                        None => fail(CheckError::Invalid(code_points(&M_PROP))),
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2157-2180 inferBody` — the λ
/// clause: the domain's sort is run (unlike the io grade's), then the opened
/// body's type, then con-leche's task #161 chain rule or the task-#152
/// codomain-sort computation.
pub fn infer_lam(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
) -> Result<EIdx, CheckError> {
    match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => match view(pers, st, &w) {
                Err(e) => Err(e),
                // Binder-telescope loop (con-leche's task #72, `inferBodyI`'s
                // `.lam` case): peel the whole λ-chain, open in bulk, rebuild
                // with `abstract_range`.  The first binder is peeled here, which
                // is why `infer_lams` starts at `k = 1` with one free variable
                // and a one-entry stack.
                Ok(ENodeView::Sort(_)) => {
                    match intern_e(pers, st, ENodeView::FVar(depth, ty.dup2())) {
                        Err(e) => Err(e),
                        Ok(fv) => {
                            let fvs: Vec<EIdx> = cons_eidx(&fv, &Vec::new());
                            let mut stk: Vec<(EIdx, BinderMeta)> = Vec::new();
                            stk.push((ty.dup2(), expr::binder_meta_dup(mb)));
                            infer_lams(
                                pers, vis, st, mode, lane, fuel, fe, depth, PEEL_FUEL, body, 1,
                                &fvs, stk,
                            )
                        }
                    }
                }
                Ok(_) => fail(CheckError::Invalid(code_points(&M_SORT))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2160-2179 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2282-2298 inferBodyIO`
/// The λ clause from the opening on, which the two bodies share: the binder is
/// opened at a fresh free variable, the body's type is inferred, and the
/// annotation is validated.  The ONE difference is which grade the
/// codomain-sort leaf infers at — `r.inferIO` in the full body, `r.infer` in
/// the io body (`io = true` here) — so the flag is that difference and
/// nothing else.
pub fn infer_lam_open(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
    io: bool,
) -> Result<EIdx, CheckError> {
    match intern_e(pers, st, ENodeView::FVar(depth, ty.dup2())) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
            Err(e) => Err(e),
            Ok(ob) => {
                // `r.infer` in both bodies.  In the full body `io` is `false`
                // and `knot_infer_at` IS `knot_infer`; in the io body it is the
                // knot's `ioView` substitution.
                let bt = knot_infer_at(pers, vis, st, mode, lane, io, fuel, fe, depth + 1, &ob);
                match bt {
                    Err(e) => Err(e),
                    Ok(bt) => {
                        if con_ron_core::kernel::env::verified_checks(mode) {
                            infer_lam_cod(
                                pers,
                                vis,
                                st, mode, lane, fuel, fe, depth, ty, body, mb, &bt,
                            )
                        } else {
                            infer_lam_result(pers, st, ty, &bt, depth, mb)
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2163-2178 inferBody`
/// Lean twin: `proof/ConRon/Arena/Core.lean:2285-2297 inferBodyIO`
/// The λ clause's validated-annotation half: the chain rule at a λ-headed
/// body, the codomain-sort computation at the innermost binder.
pub fn infer_lam_cod(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
    bt: &EIdx,
) -> Result<EIdx, CheckError> {
    match lam_pw(pers, st, body) {
        Err(e) => Err(e),
        // con-leche's task #161 chain rule: datum equality with the
        // neighbour, no inference.
        Ok(Some(pw_i)) => {
            if !prop_when::beq(&mb.pw, &pw_i) {
                fail(CheckError::NotImplemented(code_points(&M_CHAIN)))
            } else {
                infer_lam_result(pers, st, ty, bt, depth, mb)
            }
        }
        // the innermost binder: the task-#152 codomain-sort computation
        Ok(None) => {
            // The full body writes `r.inferIO (depth+1) bt` and the io body
            // writes `r.infer (depth+1) bt`; both resolve to this knot's io
            // slot — in the io body because its record IS the io view (or, at
            // `LANE_IO`, because the knot's two infer slots are one function.
            let btt = knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth + 1, bt);
            match btt {
                Err(e) => Err(e),
                Ok(btt) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth + 1, &btt) {
                    Err(e) => Err(e),
                    Ok(vb) => match read_level(pers, st, &vb) {
                        Err(e) => Err(e),
                        Ok(lvb) => {
                            if !prop_when::beq(&level::zeroness_of(&lvb), &mb.pw) {
                                fail(CheckError::NotImplemented(code_points(&M_LEAF)))
                            } else {
                                infer_lam_result(pers, st, ty, bt, depth, mb)
                            }
                        }
                    },
                },
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1011-1042 inferSpineI
/// Lean twin: OWED (task #97-P6-9's ledger) — the cached tier's
/// application-inference spine loop, the EXECUTED checker's own `.app` clause.
///
/// **The batched instantiation lever** (task #97-P6-9), the telescope half.
/// The spec-shaped clause this replaces inferred the type of every PREFIX of
/// the spine and substituted one argument into it per level — so the residual
/// Π-telescope, binders and all, was rebuilt once per argument, which is where
/// task #97-P6-8a's 5.15× `forallE` excess comes from.  This walks the RAW
/// telescope structurally with the arguments accumulated in `acc` (innermost
/// first, the list `instantiate_list` takes at cursor 0) and substitutes each
/// domain, and the residual, in ONE walk.  con-leche makes the same move
/// between its PURE and its CACHED tier and proves the two equal:
/// `ConLeche/Verify/BetaSpine.lean` (`inferSpine_sound`), whose per-argument
/// decomposition is `Expr.instantiateList_cons`
/// (`ConLeche/Verify/InstList.lean`).
///
/// The non-`forallE` arm is the twin's: substitute, `whnf`, and restart the
/// accumulator — a telescope step the raw term did not have is exactly the
/// spec's `whnf`-then-`instantiate1` level.
pub fn infer_spine(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, acc, 0)
    } else {
        let a: EIdx = args[i].dup2();
        match view(pers, st, ty) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => {
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, acc, 0) {
                    Err(e) => Err(e),
                    Ok(dom2) => {
                        match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, &a) {
                            Err(e) => Err(e),
                            Ok(ta) => match knot_defeq(
                                pers, vis, st, mode, lane, fuel, fe, depth, &ta, &dom2,
                            ) {
                                Err(e) => Err(e),
                                Ok(false) => {
                                    fail(CheckError::Invalid(code_points(&M_APP_MISMATCH)))
                                }
                                Ok(true) => {
                                    let acc2: Vec<EIdx> = cons_eidx(&a, acc);
                                    infer_spine(
                                        pers, vis, st, mode, lane, fuel, fe, depth, &body, &acc2,
                                        args, i + 1,
                                    )
                                }
                            },
                        }
                    }
                }
            }
            Ok(_) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, acc, 0) {
                Err(e) => Err(e),
                Ok(ty2) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &ty2) {
                    Err(e) => Err(e),
                    Ok(w) => match view(pers, st, &w) {
                        Err(e) => Err(e),
                        Ok(ENodeView::ForallE(dom, body, _)) => {
                            match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, &a) {
                                Err(e) => Err(e),
                                Ok(ta) => match knot_defeq(
                                    pers, vis, st, mode, lane, fuel, fe, depth, &ta, &dom,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(false) => {
                                        fail(CheckError::Invalid(code_points(&M_APP_MISMATCH)))
                                    }
                                    Ok(true) => {
                                        let acc2: Vec<EIdx> = cons_eidx(&a, &Vec::new());
                                        infer_spine(
                                            pers, vis, st, mode, lane, fuel, fe, depth, &body,
                                            &acc2, args, i + 1,
                                        )
                                    }
                                },
                            }
                        }
                        Ok(_) => fail(CheckError::Invalid(code_points(&M_FN))),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// Lean twin: OWED (task #97-P6-9's ledger) — the `.app` clause of the cached
/// inference body: the spine's head is inferred once and its Π-telescope is
/// walked against the whole spine.
pub fn infer_app(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match head_and_args(pers, st, e) {
        Err(er) => Err(er),
        Ok(hv) => match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, &hv.0) {
            Err(er) => Err(er),
            Ok(tf) => {
                let acc: Vec<EIdx> = Vec::new();
                infer_spine(pers, vis, st, mode, lane, fuel, fe, depth, &tf, &acc, &hv.1, 0)
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The inference binder-telescope loops (con-leche's task #72,
// `Cached/CoreC.lean:1140-1290`) — task #97-P6-12.
//
// The spec-shaped clauses these replace opened ONE binder against ONE fresh
// free variable, inferred the whole residual telescope under it, and closed it
// again with one whole-body `abstract1` — so a chain of `k` binders walked its
// own tail `k` times.  con-leche's cached tier peels the whole chain:
// each domain is opened against the free variables accumulated so far in ONE
// `instantiate_list`, the residual leaf is opened once and inferred once, and
// the rebuild closes each domain with ONE `abstract_range`.  The identification
// with the chained spec bodies is `ConLeche/Verify/BinderLoop.lean`
// (`inferLams_sound`, `inferPis_sound`), over `Expr.instantiateList_cons`
// (`ConLeche/Verify/InstList.lean:54-116`) and `abstractRange_succ`
// (`ConLeche/Verify/AbstractRange.lean:29-55`).
//
// The two shapes that are the arena's rather than con-leche's are the same two
// `annotate_pis` / `annotate_lams` already carry (task #97-P6-11): the stack is
// a `Vec` pushed OUTERMOST-first and consumed by a count `n` counting down,
// where con-leche conses a `List` innermost-first and consumes its head — so
// `stk[j]` is the binder at level `d + j` and `j` is exactly the
// `abstract_range` width its domain wants, and `stk[n - 1]` is con-leche's
// `stk` head; and `fvs` is built innermost-first with `cons_eidx` and read by
// `instantiate_list` at cursor 0, where con-leche pushes outermost-first and
// reads with `instantiateRev`.
//
// **Only the full grade loops.**  con-leche's `inferBodyIOI` keeps BOTH binder
// clauses chained on purpose ("the loops are the front door's optimization, and
// looping the io lane would owe the whole loop-identification walk family a
// second, io-graded instance for a lane whose subjects are internal
// re-inferences"), so `infer_lam_open` / `infer_lam_cod` / `infer_lam_result`
// survive as the io body's λ clause and are unchanged.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:1142-1160 inferLamsOutI
/// Lean twin: OWED (task #97-P6-12's ledger) — the outward rebuild of the λ
/// telescope loop: fold the stack innermost binder first, rebuilding one `∀`
/// node per entry.
///
/// `stk[j]` is the binder at level `d + j` and its opened domain may mention
/// the `j` free variables below it, so `abstract_range ty d j` is what closes
/// it — where the per-binder clause spent one whole-body `abstract1` per level.
/// `j = 0` (the outermost binder) is `abstract_range_fast`'s own identity
/// clause and costs nothing.
///
/// con-leche's task #161 chain rule, threaded: a node's prop-ness annotation
/// must agree with its inner neighbour's, and `prev_pw` is that neighbour's
/// datum — the leaf phase supplies the first one (§`infer_lams_leaf`), so the
/// innermost step compares the entry with itself and is vacuously true.  The
/// intermediate `∀`-node inferences of the chained body are value-determined by
/// the peel phase's domain sorts and the leaf phase's body-type sort and cannot
/// fail (con-leche's task #100 stage 6).
pub fn infer_lams_out(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    d: u64,
    stk: &Vec<(EIdx, BinderMeta)>,
    n: usize,
    cur: &EIdx,
    prev_pw: &PropWhen,
) -> Result<EIdx, CheckError> {
    if n == 0 {
        Ok(cur.dup2())
    } else {
        let j: usize = n - 1;
        if con_ron_core::kernel::env::verified_checks(mode)
            && !prop_when::beq(&stk[j].1.pw, prev_pw)
        {
            fail(CheckError::NotImplemented(code_points(&M_CHAIN)))
        } else {
            match abstract_range_fast(pers, st, CORE_WALK_FUEL, &stk[j].0, d, j as u64, 0) {
                Err(e) => Err(e),
                Ok(ty_abs) => {
                    let m: BinderMeta = expr::binder_meta_dup(&stk[j].1);
                    let pw2: PropWhen = prop_when::dup(&m.pw);
                    match intern_e(pers, st, ENodeView::ForallE(ty_abs, cur.dup2(), m)) {
                        Err(e) => Err(e),
                        Ok(nd) => infer_lams_out(pers, st, mode, d, stk, j, &nd, &pw2),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI
/// Lean twin: OWED (task #97-P6-12's ledger) — the `match t with | .lam .. =>
/// pure () | _ => if mode.verifiedChecks then …` statement of the λ loop's leaf
/// phase, which the arena names so that the leaf's common tail is written once.
///
/// con-leche's task #152: at the verified modes the chain's body type is
/// sort-checked here — the spec's codomain check (`infer_lam_cod`'s
/// `lam_pw = none` branch), which fires at the innermost binder of a λ chain,
/// i.e. exactly when the peel stops on a non-λ residual.  The guard is the same
/// one the spec uses, on the same term, and the datum it validates is the
/// innermost binder's, `stk`'s head.
pub fn infer_lams_leaf_check(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    k: u64,
    stk: &Vec<(EIdx, BinderMeta)>,
    bt: &EIdx,
) -> Result<(), CheckError> {
    if !con_ron_core::kernel::env::verified_checks(mode) {
        Ok(())
    } else {
        match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, d + k, bt) {
            Err(e) => Err(e),
            Ok(btt) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, d + k, &btt) {
                Err(e) => Err(e),
                Ok(vb) => {
                    let n: usize = stk.len();
                    if n == 0 {
                        Ok(())
                    } else {
                        match read_level(pers, st, &vb) {
                            Err(e) => Err(e),
                            Ok(lvb) => {
                                if prop_when::beq(&level::zeroness_of(&lvb), &stk[n - 1].1.pw) {
                                    Ok(())
                                } else {
                                    fail(CheckError::NotImplemented(code_points(&M_LEAF)))
                                }
                            }
                        }
                    }
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI
/// Lean twin: OWED (task #97-P6-12's ledger) — the leaf phase of the λ
/// telescope loop: bulk-open the residual body against the whole accumulated
/// free-variable vector, infer it ONCE, run the innermost binder's codomain
/// check, close the leaf with ONE `abstract_range`, then rebuild outward.
///
/// The fold's initial neighbour is con-leche's own: a λ residual (the
/// fuel-exhausted path) supplies its own annotation — the head entry's chain
/// check then compares against it, exactly as the spec's per-node clause does;
/// a non-λ residual makes the head entry's step vacuous, its codomain fact
/// being `infer_lams_leaf_check` above.  `lam_pw` is `Expr.lamPw`, an O(1) read
/// of the node's own stored datum, and it decides both.
pub fn infer_lams_leaf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: &Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, fvs, 0) {
        Err(e) => Err(e),
        Ok(ob) => match knot_infer(pers, vis, st, mode, lane, fuel, fe, d + k, &ob) {
            Err(e) => Err(e),
            Ok(bt) => match lam_pw(pers, st, t) {
                Err(e) => Err(e),
                Ok(lpw) => {
                    let chk: Result<(), CheckError> = match &lpw {
                        Some(_) => Ok(()),
                        None => infer_lams_leaf_check(
                            pers, vis, st, mode, lane, fuel, fe, d, k, stk, &bt,
                        ),
                    };
                    match chk {
                        Err(e) => Err(e),
                        Ok(()) => {
                            let n: usize = stk.len();
                            let prev_pw: PropWhen = match lpw {
                                Some(p) => p,
                                None => {
                                    if n == 0 {
                                        prop_when::never()
                                    } else {
                                        prop_when::dup(&stk[n - 1].1.pw)
                                    }
                                }
                            };
                            match abstract_range_fast(pers, st, CORE_WALK_FUEL, &bt, d, k, 0) {
                                Err(e) => Err(e),
                                Ok(cur) => {
                                    infer_lams_out(pers, st, mode, d, stk, n, &cur, &prev_pw)
                                }
                            }
                        }
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1208-1228 inferLamsI
/// Lean twin: OWED (task #97-P6-12's ledger) — the λ-telescope inference loop:
/// peel the raw λ-chain, checking each opened domain to be a type on the way
/// in.  `k >= 1` counts the opened binders (the first is peeled by
/// `infer_lam`'s own clause) and `fvs` holds their free variables
/// innermost-first, which is the list `instantiate_list` takes at cursor 0.
///
/// One peeled domain is ONE `instantiate_list` walk over the domain alone,
/// where the per-binder clause substituted into the whole residual telescope
/// once per level; `Expr.instantiateList_cons`
/// (`ConLeche/Verify/InstList.lean:54-116`) is the equation that identifies the
/// batch with the chain of `instantiate1` the spec-shaped body ran.
pub fn infer_lams(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    // The peel's test is a tag read off the handle word and the binder
    // PROJECTION (task #97-P6-10): the loop asks "is this still a λ?" once per
    // binder and wants only the three fields when it is.
    if peel == 0 || t.tag() != ETAG_LAM {
        infer_lams_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view_bind(pers, st, t) {
            None => fail_dangling_e(),
            Some(p) => {
                let ty: EIdx = p.0;
                let body: EIdx = p.1;
                let mb: BinderMeta = p.2;
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, fvs, 0) {
                    Err(e) => Err(e),
                    Ok(tyo) => {
                        match knot_infer(pers, vis, st, mode, lane, fuel, fe, d + k, &tyo) {
                            Err(e) => Err(e),
                            Ok(tty) => {
                                match knot_whnf(pers, vis, st, mode, lane, fuel, fe, d + k, &tty) {
                                    Err(e) => Err(e),
                                    Ok(w) => match view(pers, st, &w) {
                                        Err(e) => Err(e),
                                        Ok(ENodeView::Sort(_)) => {
                                            match intern_e(
                                                pers,
                                                st,
                                                ENodeView::FVar(d + k, tyo.dup2()),
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(fv) => {
                                                    let fvs2: Vec<EIdx> = cons_eidx(&fv, fvs);
                                                    let mut stk2: Vec<(EIdx, BinderMeta)> = stk;
                                                    stk2.push((tyo, mb));
                                                    infer_lams(
                                                        pers, vis, st, mode, lane, fuel, fe, d,
                                                        peel - 1, &body, k + 1, &fvs2, stk2,
                                                    )
                                                }
                                            }
                                        }
                                        Ok(_) => {
                                            fail(CheckError::Invalid(code_points(&M_SORT)))
                                        }
                                    },
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1230-1254 inferPisOutI
/// Lean twin: OWED (task #97-P6-12's ledger) — the outward fold of the ∀
/// telescope loop: fold the accumulated domain sorts by `imax`, innermost
/// binder first, which is exactly the chained `∀`-rule's result value.
///
/// con-leche's task #272 (its GitHub issue #9): the codomain sort's zero-ness
/// datum is **threaded, not recomputed**.  `zeronessOf (imax u v) = zeronessOf
/// v` holds definitionally, so every node of a ∀ telescope shares the leaf's
/// datum, and the fold pays ONE `read_level` in the leaf phase where the
/// per-binder clause paid one per binder — and where con-leche's own pre-#272
/// fold walked `zeronessOf` down a growing right spine, `O(k²)` in the
/// telescope depth.  `pv` is that leaf datum; the pure mirror
/// (`Verify/BinderLoop.lean:156-163 inferPisOut`) recomputes it at every step
/// and `Verify/Cached/BinderLoopC.lean:359-404 inferPisOutC_sim` is where the
/// two are identified.
pub fn infer_pis_out(
    pers: &PersTier,
    st: &mut AState,
    mode: &CheckMode,
    stk: &Vec<(LIdx, PropWhen)>,
    n: usize,
    v: &LIdx,
    pv: &PropWhen,
) -> Result<LIdx, CheckError> {
    if n == 0 {
        Ok(v.dup2())
    } else {
        let j: usize = n - 1;
        if con_ron_core::kernel::env::verified_checks(mode) && !prop_when::beq(pv, &stk[j].1) {
            fail(CheckError::NotImplemented(code_points(&M_COD)))
        } else {
            match intern_l_node(pers, st, LNodeView::Imax(stk[j].0.dup2(), v.dup2())) {
                Err(e) => Err(e),
                Ok(v2) => infer_pis_out(pers, st, mode, stk, j, &v2, pv),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1256-1267 inferPisLeafI
/// Lean twin: OWED (task #97-P6-12's ledger) — the leaf phase of the ∀
/// telescope loop: bulk-open the residual body against the whole accumulated
/// free-variable vector, infer its sort ONCE, then fold the domain sorts
/// outward.  The telescope's zero-ness datum is read HERE, once, and threaded.
pub fn infer_pis_leaf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: &Vec<(LIdx, PropWhen)>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, fvs, 0) {
        Err(e) => Err(e),
        Ok(ob) => match knot_infer(pers, vis, st, mode, lane, fuel, fe, d + k, &ob) {
            Err(e) => Err(e),
            Ok(bt) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, d + k, &bt) {
                Err(e) => Err(e),
                Ok(v) => match read_level(pers, st, &v) {
                    Err(e) => Err(e),
                    Ok(lv) => {
                        let pv: PropWhen = level::zeroness_of(&lv);
                        let n: usize = stk.len();
                        match infer_pis_out(pers, st, mode, stk, n, &v, &pv) {
                            Err(e) => Err(e),
                            Ok(iv) => intern_e(pers, st, ENodeView::Sort(iv)),
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1269-1290 inferPisI
/// Lean twin: OWED (task #97-P6-12's ledger) — the ∀-telescope inference loop
/// (con-leche's task #100 stage 6: the `∀`-rule INFERS its codomain sort, the
/// stored annotation is not read): peel the raw ∀-chain, checking each opened
/// domain to be a type on the way in and accumulating its sort, infer the
/// bulk-opened leaf's sort once, and fold `imax` outward.
///
/// The stack carries `(LIdx, PropWhen)` and no expression at all — a ∀
/// telescope's inference builds no binder node, only the folded level and the
/// one `sort` around it, which is why this loop takes the whole per-level
/// `instantiate1` of the residual telescope off the run and puts nothing back.
pub fn infer_pis(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: Vec<(LIdx, PropWhen)>,
) -> Result<EIdx, CheckError> {
    // The peel's test is a tag read off the handle word and the binder
    // PROJECTION (task #97-P6-10), as `infer_lams`' is.
    if peel == 0 || t.tag() != ETAG_FORALL_E {
        infer_pis_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view_bind(pers, st, t) {
            None => fail_dangling_e(),
            Some(p) => {
                let ty: EIdx = p.0;
                let body: EIdx = p.1;
                let mb: BinderMeta = p.2;
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, fvs, 0) {
                    Err(e) => Err(e),
                    Ok(tyo) => {
                        match knot_infer(pers, vis, st, mode, lane, fuel, fe, d + k, &tyo) {
                            Err(e) => Err(e),
                            Ok(tty) => {
                                match knot_whnf(pers, vis, st, mode, lane, fuel, fe, d + k, &tty) {
                                    Err(e) => Err(e),
                                    Ok(w) => match view(pers, st, &w) {
                                        Err(e) => Err(e),
                                        Ok(ENodeView::Sort(u)) => {
                                            match intern_e(
                                                pers,
                                                st,
                                                ENodeView::FVar(d + k, tyo.dup2()),
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(fv) => {
                                                    let fvs2: Vec<EIdx> = cons_eidx(&fv, fvs);
                                                    let mut stk2: Vec<(LIdx, PropWhen)> = stk;
                                                    stk2.push((u, prop_when::dup(&mb.pw)));
                                                    infer_pis(
                                                        pers, vis, st, mode, lane, fuel, fe, d,
                                                        peel - 1, &body, k + 1, &fvs2, stk2,
                                                    )
                                                }
                                            }
                                        }
                                        Ok(_) => {
                                            fail(CheckError::Invalid(code_points(&M_SORT)))
                                        }
                                    },
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2101-2219 inferBody` — the
/// inference body.
pub fn infer_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        Ok(ENodeView::Const(n, us)) => infer_const(pers, vis, st, fe, &n, &us),
        Ok(ENodeView::Lit(Literal::NatVal(_))) => infer_lit_nat(pers, vis, st, fe),
        Ok(ENodeView::Lit(Literal::StrVal(_))) => infer_lit_str(pers, vis, st, fe),
        Ok(ENodeView::ForallE(ty, body, mb)) => {
            infer_forall(pers, vis, st, mode, lane, fuel, fe, depth, &ty, &body, &mb)
        }
        Ok(ENodeView::Lam(ty, body, mb)) => {
            infer_lam(pers, vis, st, mode, lane, fuel, fe, depth, &ty, &body, &mb)
        }
        Ok(ENodeView::App(_, _)) => infer_app(pers, vis, st, mode, lane, fuel, fe, depth, e),
        Ok(ENodeView::Proj(sn, i, pe)) => {
            infer_proj(pers, vis, st, mode, lane, fuel, fe, depth, &sn, i, &pe)
        }
        Ok(ENodeView::LetE(_, _, _)) => {
            fail(CheckError::Internal(code_points(&M_LET_INFER)))
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_INFER)))
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2226-2339 inferBodyIO` — **the io
/// inference body**: `inferBody` with two clauses changed — no domain-sort run
/// at the λ (official's `infer_lambda` skips it at `infer_only`), and the
/// application rule's per-argument certificate skipped when the ∀'s validated
/// annotation licenses it.
///
/// The `io` flag is the twin's `CoreFnsA.ioView`: it says whether this body's
/// `r.infer` is the knot's `inferIO` slot (`coreKnot`'s io slot passes
/// `ioView (coreKnot … fuel)`) or its `infer` slot (`coreKnotIO` passes the
/// plain record).
pub fn infer_body_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
        Ok(ENodeView::Const(n, us)) => infer_const(pers, vis, st, fe, &n, &us),
        Ok(ENodeView::Lit(Literal::NatVal(_))) => infer_lit_nat(pers, vis, st, fe),
        Ok(ENodeView::Lit(Literal::StrVal(_))) => infer_lit_str(pers, vis, st, fe),
        Ok(ENodeView::ForallE(ty, body, mb)) => {
            infer_forall_io(pers, vis, st, mode, lane, io, fuel, fe, depth, &ty, &body, &mb)
        }
        // con-leche's task #168 stage 2: no domain-sort run at the io grade
        Ok(ENodeView::Lam(ty, body, mb)) => {
            infer_lam_open(pers, vis, st, mode, lane, fuel, fe, depth, &ty, &body, &mb, io)
        }
        Ok(ENodeView::App(_, _)) => {
            infer_app_io_at(pers, vis, st, mode, lane, io, fuel, fe, depth, e)
        }
        Ok(ENodeView::Proj(sn, i, pe)) => {
            infer_proj_io(pers, vis, st, mode, lane, io, fuel, fe, depth, &sn, i, &pe)
        }
        Ok(ENodeView::LetE(_, _, _)) => {
            fail(CheckError::Internal(code_points(&M_LET_INFER)))
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_INFER)))
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2263-2279 inferBodyIO` — the io
/// body's ∀ clause: `inferBody`'s, with `r.infer` resolved through this lane.
pub fn infer_forall_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
) -> Result<EIdx, CheckError> {
    match knot_infer_at(pers, vis, st, mode, lane, io, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(tty) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tty) {
            Err(e) => Err(e),
            Ok(w) => match view(pers, st, &w) {
                Err(e) => Err(e),
                Ok(ENodeView::Sort(u)) => infer_forall_io_at(
                    pers,
                    vis,
                    st, mode, lane, io, fuel, fe, depth, ty, body, mb, &u,
                ),
                Ok(_) => fail(CheckError::Invalid(code_points(&M_SORT))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2265-2278 inferBodyIO` — the io
/// body's ∀ clause, once the domain's sort is known.
pub fn infer_forall_io_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
    u: &LIdx,
) -> Result<EIdx, CheckError> {
    match intern_e(pers, st, ENodeView::FVar(depth, ty.dup2())) {
        Err(e) => Err(e),
        Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
            Err(e) => Err(e),
            Ok(ob) => {
                match knot_infer_at(pers, vis, st, mode, lane, io, fuel, fe, depth + 1, &ob) {
                    Err(e) => Err(e),
                    Ok(tb) => {
                        match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth + 1, &tb) {
                            Err(e) => Err(e),
                            Ok(v) => {
                                let ok =
                                    if con_ron_core::kernel::env::verified_checks(mode) {
                                        match read_level(pers, st, &v) {
                                            Err(e) => Err(e),
                                            Ok(lv) => Ok(prop_when::beq(
                                                &level::zeroness_of(&lv),
                                                &mb.pw,
                                            )),
                                        }
                                    } else {
                                        Ok(true)
                                    };
                                match ok {
                                    Err(e) => Err(e),
                                    Ok(false) => fail(CheckError::NotImplemented(
                                        code_points(&M_COD),
                                    )),
                                    Ok(true) => {
                                        match intern_l_node(
                                            pers,
                                            st,
                                            LNodeView::Imax(u.dup2(), v.dup2()),
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(iu) => intern_e(pers, st, ENodeView::Sort(iu)),
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

/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2299-2312 inferBodyIO` — the io
/// body's `.app` clause, with `r.infer` resolved through this lane.
pub fn infer_app_io_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
            match knot_infer_at(pers, vis, st, mode, lane, io, fuel, fe, depth, &hv.0) {
                Err(er) => Err(er),
                Ok(tf) => {
                    let acc: Vec<EIdx> = Vec::new();
                    infer_spine_io(
                        pers, vis, st, mode, lane, io, fuel, fe, depth, &tf, &acc, &hv.1, 0,
                    )
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1044-1091 inferSpineIOI
/// Lean twin: OWED (task #97-P6-9's ledger) — `infer_spine` with the
/// per-argument certificate gated: **THE io SITE** (task #97f, P2f), where the
/// executed core reads `CheckMode.ioSkip` — the datum weakened by
/// `!mode.certs`, the io-grade argument certificate being a certificate
/// FAMILY.  The two agree at `.verified`, the mode the bridge is stated at.
///
/// A syntactic `.forallE` is its own whnf, so the syntactic step's datum is
/// the datum the pure io body reads off the whnf'd type (con-leche's own note
/// on `inferSpineIOI`); the returned type is the same telescope walk either
/// way, so the lane stays annotation-blind in its results.
pub fn infer_spine_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, acc, 0)
    } else {
        let a: EIdx = args[i].dup2();
        match view(pers, st, ty) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, mt)) => {
                let cert = if con_ron_core::kernel::env::io_skip(mode, &mt.pw) {
                    Ok(true)
                } else {
                    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &dom, acc, 0) {
                        Err(e) => Err(e),
                        Ok(dom2) => {
                            match knot_infer_at(
                                pers, vis, st, mode, lane, io, fuel, fe, depth, &a,
                            ) {
                                Err(e) => Err(e),
                                Ok(ta) => knot_defeq(
                                    pers, vis, st, mode, lane, fuel, fe, depth, &ta, &dom2,
                                ),
                            }
                        }
                    }
                };
                match cert {
                    Err(e) => Err(e),
                    Ok(false) => fail(CheckError::Invalid(code_points(&M_APP_MISMATCH))),
                    Ok(true) => {
                        let acc2: Vec<EIdx> = cons_eidx(&a, acc);
                        infer_spine_io(
                            pers, vis, st, mode, lane, io, fuel, fe, depth, &body, &acc2, args,
                            i + 1,
                        )
                    }
                }
            }
            Ok(_) => match instantiate_list_fast(pers, st, CORE_WALK_FUEL, ty, acc, 0) {
                Err(e) => Err(e),
                Ok(ty2) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &ty2) {
                    Err(e) => Err(e),
                    Ok(w) => match view(pers, st, &w) {
                        Err(e) => Err(e),
                        Ok(ENodeView::ForallE(dom, body, mt)) => {
                            let cert = if con_ron_core::kernel::env::io_skip(mode, &mt.pw) {
                                Ok(true)
                            } else {
                                match knot_infer_at(
                                    pers, vis, st, mode, lane, io, fuel, fe, depth, &a,
                                ) {
                                    Err(e) => Err(e),
                                    Ok(ta) => knot_defeq(
                                        pers, vis, st, mode, lane, fuel, fe, depth, &ta, &dom,
                                    ),
                                }
                            };
                            match cert {
                                Err(e) => Err(e),
                                Ok(false) => {
                                    fail(CheckError::Invalid(code_points(&M_APP_MISMATCH)))
                                }
                                Ok(true) => {
                                    let acc2: Vec<EIdx> = cons_eidx(&a, &Vec::new());
                                    infer_spine_io(
                                        pers, vis, st, mode, lane, io, fuel, fe, depth, &body,
                                        &acc2, args, i + 1,
                                    )
                                }
                            }
                        }
                        Ok(_) => fail(CheckError::Invalid(code_points(&M_FN))),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2313-2335 inferBodyIO` — the io
/// body's `.proj` clause, with `r.infer` resolved through this lane.
pub fn infer_proj_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_infer_at(pers, vis, st, mode, lane, io, fuel, fe, depth, pe) {
        Err(e) => Err(e),
        Ok(tp) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &tp) {
            Err(e) => Err(e),
            Ok(te) => match get_app_fn(pers, st, CORE_WALK_FUEL, &te) {
                Err(e) => Err(e),
                Ok(hd) => match view(pers, st, &hd) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(t, us)) => {
                        match env::ifenv_find_proj(pers, vis, &mut st.store, fe, &t, i) {
                            Err(e) => Err(e),
                            Ok(Some(entry)) => {
                                infer_proj_at(pers, st, &te, sn, pe, &t, &us, &entry)
                            }
                            Ok(None) => {
                                fail(CheckError::NotImplemented(code_points(&M_NOENTRY)))
                            }
                        }
                    }
                    Ok(_) => fail(CheckError::NotImplemented(code_points(&M_NOENTRY))),
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Definitional equality (`Core.lean:2342-2593`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1406-1418 boolTrueShortcut
/// Lean twin: `proof/ConRon/Arena/Core.lean:2349-2351 boolTrueShortcut` — **the
/// eq-true shortcut** (the divergence audit's E2): the left side is fully
/// head-normalised and the verdict is `true` iff the reduct is `Bool.true`.
pub fn bool_true_shortcut(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
) -> Result<bool, CheckError> {
    match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, a) {
        Err(e) => Err(e),
        Ok(w) => is_bool_true(pers, st, &w),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1420-1439 defeqSpine
/// Lean twin: `proof/ConRon/Arena/Core.lean:2357-2371 defeqSpine` —
/// levels-and-spine congruence for two applications of the *same* stored
/// constant (the lazy delta same-head short-circuit, official's
/// `try_eq_const_app`).
pub fn defeq_spine(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    match get_app_fn(pers, st, CORE_WALK_FUEL, a) {
        Err(e) => Err(e),
        Ok(ha) => match view(pers, st, &ha) {
            Err(e) => Err(e),
            Ok(ENodeView::Const(n, us)) => match get_app_fn(pers, st, CORE_WALK_FUEL, b) {
                Err(e) => Err(e),
                Ok(hb) => match view(pers, st, &hb) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(n2, us2)) => match get_app_args(pers, st, CORE_WALK_FUEL, a) {
                        Err(e) => Err(e),
                        Ok(aa) => match get_app_args(pers, st, CORE_WALK_FUEL, b) {
                            Err(e) => Err(e),
                            Ok(bb) => {
                                if n.eq2(&n2) && aa.len() == bb.len() {
                                    match lvls_eq(pers, st, &us, &us2) {
                                        Err(e) => Err(e),
                                        Ok(Some(true)) => def_eq_list(
                                            pers,
                                            vis,
                                            st, mode, lane, fuel, fe, depth, &aa, &bb, 0,
                                        ),
                                        Ok(_) => Ok(false),
                                    }
                                } else {
                                    Ok(false)
                                }
                            }
                        },
                    },
                    Ok(_) => Ok(false),
                },
            },
            Ok(_) => Ok(false),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2377-2381 defeqNoFvars` — the
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

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2519-2537 defeqStep` — the two
/// binder-congruence arms, which the twin writes twice (once for `∀`, once
/// for `λ`) and which differ only in the message of the annotation mismatch.
/// `is_lam` selects it.
pub fn defeq_binders(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty1: &EIdx,
    body1: &EIdx,
    m1: &BinderMeta,
    ty2: &EIdx,
    body2: &EIdx,
    m2: &BinderMeta,
    is_lam: bool,
) -> Result<bool, CheckError> {
    match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, ty1, ty2) {
        Err(e) => Err(e),
        Ok(false) => Ok(false),
        Ok(true) => match intern_e(pers, st, ENodeView::FVar(depth, ty2.dup2())) {
            Err(e) => Err(e),
            Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body1, &fv, 0) {
                Err(e) => Err(e),
                Ok(o1) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body2, &fv, 0) {
                    Err(e) => Err(e),
                    Ok(o2) => {
                        match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth + 1, &o1, &o2) {
                            Err(e) => Err(e),
                            Ok(false) => Ok(false),
                            Ok(true) => {
                                if con_ron_core::kernel::env::verified_checks(mode)
                                    && !prop_when::beq(&m1.pw, &m2.pw)
                                {
                                    if is_lam {
                                        fail(CheckError::NotImplemented(code_points(
                                            &M_DEFEQ_LAM,
                                        )))
                                    } else {
                                        fail(CheckError::NotImplemented(code_points(
                                            &M_DEFEQ_PI,
                                        )))
                                    }
                                } else {
                                    Ok(true)
                                }
                            }
                        }
                    }
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2465-2490 defeqStep` — the
/// `(literal, application)` arms, merged: a packed `Nat` literal against a
/// `Nat.succ` application, or a `String` literal against a unary
/// `String.ofList` application.  The twin writes them as two arms of the pair
/// match, separated by their mirror images; since the scrutinee pair is fixed,
/// merging two arms that differ only in the literal's constructor changes
/// nothing — the twin's fall-through for the other constructor is `stuckIrrel`,
/// which is what this arm does.
pub fn defeq_lit_app(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    l: &Literal,
    f: &EIdx,
    x: &EIdx,
    a2: &EIdx,
    b2: &EIdx,
    flipped: bool,
) -> Result<bool, CheckError> {
    match l {
        Literal::NatVal(nn) => {
            if nat::is_zero(nn) {
                stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
            } else {
                let k2: Nat = nat::pred(nn);
                match view(pers, st, f) {
                    Err(e) => Err(e),
                    Ok(ENodeView::Const(c, us)) => match empty_levels(st) {
                        Err(e) => Err(e),
                        Ok(el) => match pin_nat_succ(st) {
                            Err(e) => Err(e),
                            Ok(ns) => {
                                if c.eq2(&ns) && us.eq2(&el) {
                                    match intern_e(
                                        pers,
                                        st,
                                        ENodeView::Lit(expr::literal_nat(k2)),
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(lh) => {
                                            if flipped {
                                                knot_defeq(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, x,
                                                    &lh,
                                                )
                                            } else {
                                                knot_defeq(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, &lh,
                                                    x,
                                                )
                                            }
                                        }
                                    }
                                } else {
                                    stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                                }
                            }
                        },
                    },
                    Ok(_) => stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2),
                }
            }
        }
        Literal::StrVal(s) => {
            let cs: Vec<u32> = expr::str_copy(s);
            match view(pers, st, f) {
                Err(e) => Err(e),
                Ok(ENodeView::Const(c_o, us_o)) => match empty_levels(st) {
                    Err(e) => Err(e),
                    Ok(el) => match pin_string_of_list(st) {
                        Err(e) => Err(e),
                        Ok(sl) => match str_lit_supported(pers, vis, st, fe) {
                            Err(e) => Err(e),
                            Ok(sup) => {
                                if c_o.eq2(&sl) && us_o.eq2(&el) && sup {
                                    match str_lit_to_constructor(pers, st, &cs) {
                                        Err(e) => Err(e),
                                        Ok(ce) => {
                                            if flipped {
                                                knot_defeq(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, a2,
                                                    &ce,
                                                )
                                            } else {
                                                knot_defeq(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, &ce,
                                                    b2,
                                                )
                                            }
                                        }
                                    }
                                } else {
                                    stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                                }
                            }
                        },
                    },
                },
                Ok(_) => stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2455-2464 defeqStep` — the
/// `(Nat` literal`, constant)` arm, merged with its mirror: a packed literal
/// against a constructor form, compared shape-directed.
pub fn defeq_lit_const(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: &Nat,
    c: &NIdx,
    us: &LsIdx,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match empty_levels(st) {
        Err(e) => Err(e),
        Ok(el) => match pin_nat_zero(st) {
            Err(e) => Err(e),
            Ok(nz) => {
                if c.eq2(&nz) && us.eq2(&el) {
                    Ok(nat::is_zero(n))
                } else {
                    stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2451-2564 defeqStep` — the
/// structural stage: the twin's `match ← view a', ← view b'`, arm for arm in
/// its order, with the two `(literal, application)` arms merged (see
/// `defeq_lit_app`).
pub fn defeq_struct(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
                (ENodeView::Sort(u), ENodeView::Sort(v)) => match lvl_eq(pers, st, &u, &v) {
                    Err(e) => Err(e),
                    Ok(o) => lift_fueled(o),
                },
                (ENodeView::Lit(l1), ENodeView::Lit(l2)) => {
                    Ok(expr::literal_beq(&l1, &l2))
                }
                (ENodeView::Lit(Literal::NatVal(n)), ENodeView::Const(c, us)) => {
                    let m: Nat = nat::clone(&n);
                    defeq_lit_const(pers, vis, st, mode, lane, fuel, fe, depth, &m, &c, &us, a2, b2)
                }
                (ENodeView::Const(c, us), ENodeView::Lit(Literal::NatVal(n))) => {
                    let m: Nat = nat::clone(&n);
                    defeq_lit_const(pers, vis, st, mode, lane, fuel, fe, depth, &m, &c, &us, a2, b2)
                }
                (ENodeView::Lit(l), ENodeView::App(f, x)) => {
                    defeq_lit_app(pers, vis, st, mode, lane, fuel, fe, depth, &l, &f, &x, a2, b2, false)
                }
                (ENodeView::App(f, x), ENodeView::Lit(l)) => {
                    defeq_lit_app(pers, vis, st, mode, lane, fuel, fe, depth, &l, &f, &x, a2, b2, true)
                }
                (ENodeView::FVar(i, _), ENodeView::FVar(j, _)) => {
                    if i == j {
                        Ok(true)
                    } else {
                        stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
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
                                    stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                                }
                            },
                        }
                    } else {
                        stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                    }
                }
                (
                    ENodeView::ForallE(ty1, body1, m1),
                    ENodeView::ForallE(ty2, body2, m2),
                ) => defeq_binders(
                    pers,
                    vis,
                    st, mode, lane, fuel, fe, depth, &ty1, &body1, &m1, &ty2, &body2,
                    &m2, false,
                ),
                (ENodeView::Lam(ty1, body1, m1), ENodeView::Lam(ty2, body2, m2)) => {
                    defeq_binders(
                        pers,
                        vis,
                        st, mode, lane, fuel, fe, depth, &ty1, &body1, &m1, &ty2, &body2,
                        &m2, true,
                    )
                }
                (ENodeView::App(_, _), ENodeView::App(_, _)) => {
                    defeq_apps(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                }
                (ENodeView::Proj(s1, i1, e1), ENodeView::Proj(s2, i2, e2)) => {
                    if s1.eq2(&s2) && i1 == i2 {
                        match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &e1, &e2) {
                            Err(e) => Err(e),
                            Ok(true) => Ok(true),
                            Ok(false) => {
                                stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                            }
                        }
                    } else {
                        stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                    }
                }
                (ENodeView::Lam(ty1, body1, m1), _) => {
                    match eta_cert(pers, vis, st, mode, lane, fuel, fe, depth, &ty1, &body1, &m1, b2)
                    {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2),
                    }
                }
                (_, ENodeView::Lam(ty2, body2, m2)) => {
                    match eta_cert(pers, vis, st, mode, lane, fuel, fe, depth, &ty2, &body2, &m2, a2)
                    {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2),
                    }
                }
                (_, _) => stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2538-2550 defeqStep` — stuck
/// applications: **spine-wise** congruence (official's `is_def_eq_app`), never
/// a recursion on the partial applications.
pub fn defeq_apps(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
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
                                match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &fa, &fb)
                                {
                                    Err(e) => Err(e),
                                    Ok(false) => stuck_irrel(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth, a2, b2,
                                    ),
                                    Ok(true) => {
                                        match def_eq_list(
                                            pers,
                                            vis,
                                            st, mode, lane, fuel, fe, depth, &aa, &bb, 0,
                                        ) {
                                            Err(e) => Err(e),
                                            Ok(true) => Ok(true),
                                            Ok(false) => stuck_irrel(
                                                pers,
                                                vis,
                                                st, mode, lane, fuel, fe, depth, a2, b2,
                                            ),
                                        }
                                    }
                                }
                            }
                        },
                    }
                } else {
                    stuck_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2443-2449 defeqStep` — the
/// both-unfoldable case's last two arms: the cheap congruence at equal
/// *regular* hints, then the simultaneous unfolding.
pub fn defeq_unfold_both(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match unfold_definition(pers, vis, st, fe, a2) {
        Err(e) => Err(e),
        Ok(ua) => match unfold_definition(pers, vis, st, fe, b2) {
            Err(e) => Err(e),
            Ok(ub) => match (ua, ub) {
                (Some(a3), Some(b3)) => {
                    defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, false, &a3, &b3)
                }
                (_, _) => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2428-2449 defeqStep` — the
/// both-unfoldable case: the hint comparison decides which side unfolds.
pub fn defeq_delta_both(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match head_hint(pers, vis, st, fe, a2) {
        Err(e) => Err(e),
        Ok(ha) => match head_hint(pers, vis, st, fe, b2) {
            Err(e) => Err(e),
            Ok(hb) => {
                if con_ron_core::kernel::env::reducibility_hint_lt(&hb, &ha) {
                    match unfold_definition(pers, vis, st, fe, a2) {
                        Err(e) => Err(e),
                        Ok(Some(a3)) => {
                            defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, false, &a3, b2)
                        }
                        Ok(None) => Ok(false),
                    }
                } else if con_ron_core::kernel::env::reducibility_hint_lt(&ha, &hb) {
                    match unfold_definition(pers, vis, st, fe, b2) {
                        Err(e) => Err(e),
                        Ok(Some(b3)) => {
                            defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, false, a2, &b3)
                        }
                        Ok(None) => Ok(false),
                    }
                } else {
                    // Lean's `do` lifts `(← sameConstHeads a' b')` to the head
                    // of THIS branch (the nested `else if`'s own do-sequence),
                    // so it runs exactly when the two hint comparisons have
                    // both failed — and always then, whatever `sameRegular`
                    // says.
                    match same_const_heads(pers, st, a2, b2) {
                        Err(e) => Err(e),
                        Ok(sch) => {
                            if con_ron_core::kernel::env::reducibility_hint_same_regular(
                                &ha, &hb,
                            ) && sch
                            {
                                match defeq_spine(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                                {
                                    Err(e) => Err(e),
                                    Ok(true) => Ok(true),
                                    Ok(false) => defeq_unfold_both(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth, n, a2, b2,
                                    ),
                                }
                            } else {
                                defeq_unfold_both(
                                    pers,
                                    vis,
                                    st, mode, lane, fuel, fe, depth, n, a2, b2,
                                )
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2416-2450 defeqStep` — **lazy
/// delta, decision before materialization**: `unfoldableHead` decides, and
/// only the chosen side is unfolded.
pub fn defeq_delta(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match unfoldable_head(pers, vis, st, fe, a2) {
        Err(e) => Err(e),
        Ok(ua) => match unfoldable_head(pers, vis, st, fe, b2) {
            Err(e) => Err(e),
            Ok(ub) => {
                if ua && !ub {
                    match unfold_definition(pers, vis, st, fe, a2) {
                        Err(e) => Err(e),
                        Ok(Some(a3)) => {
                            defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, false, &a3, b2)
                        }
                        Ok(None) => Ok(false),
                    }
                } else if !ua && ub {
                    match unfold_definition(pers, vis, st, fe, b2) {
                        Err(e) => Err(e),
                        Ok(Some(b3)) => {
                            defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, false, a2, &b3)
                        }
                        Ok(None) => Ok(false),
                    }
                } else if ua && ub {
                    defeq_delta_both(pers, vis, st, mode, lane, fuel, fe, depth, n, a2, b2)
                } else {
                    defeq_struct(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2402-2415 defeqStep` — the hoisted
/// proof irrelevance (once per `is_def_eq_core` entry, the audit's D3, and
/// never on a pair official's `quick_is_def_eq` decides itself, D4) and the
/// literal acceleration of either side.
pub fn defeq_after_whnf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    pi: bool,
    a2: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    let pir = if pi && !quick_pair(a2, b2) {
        prop_irrel(pers, vis, st, mode, lane, fuel, fe, depth, a2, b2)
    } else {
        Ok(false)
    };
    match pir {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => match defeq_no_fvars(pers, st, a2, b2) {
            Err(e) => Err(e),
            Ok(nf) => {
                let ra = if nf {
                    reduce_nat(pers, vis, st, mode, lane, fuel, fe, depth, a2)
                } else {
                    Ok(None)
                };
                match ra {
                    Err(e) => Err(e),
                    Ok(Some(a3)) => {
                        defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, n, true, &a3, b2)
                    }
                    Ok(None) => {
                        let rb = if nf {
                            reduce_nat(pers, vis, st, mode, lane, fuel, fe, depth, b2)
                        } else {
                            Ok(None)
                        };
                        match rb {
                            Err(e) => Err(e),
                            Ok(Some(b3)) => defeq_loop(
                                pers,
                                vis,
                                st, mode, lane, fuel, fe, depth, n, true, a2, &b3,
                            ),
                            Ok(None) => {
                                defeq_delta(pers, vis, st, mode, lane, fuel, fe, depth, n, a2, b2)
                            }
                        }
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// Lean twin: `proof/ConRon/Arena/Core.lean:2388-2564 defeqStep` — the
/// definitional-equality body's one iteration: syntactic fast path, the
/// eq-true shortcut, head normalization of both sides (**no delta**), the
/// hoisted proof irrelevance, then the *lazy delta* strategy of real kernels.
/// The twin's continuation `k : Bool → EIdx → EIdx → AM Bool` is the loop's
/// step budget `n` here (the module note's deviation 2).
///
/// **The eq-true shortcut's two reads always run**: Lean's `do` lifts
/// `(← isBoolTrue b)` and `(← hasFvarFast … a)` out of the condition `pi && …
/// && …`, and both touch the state (`isBoolTrue` interns `Bool.true` and the
/// empty level list; `hasFvarFast` writes the fvar-range memo).
pub fn defeq_step(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    pi: bool,
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
                    let sc = if pi && ibt && !hf {
                        bool_true_shortcut(pers, vis, st, mode, lane, fuel, fe, depth, a)
                    } else {
                        Ok(false)
                    };
                    match sc {
                        Err(e) => Err(e),
                        Ok(true) => Ok(true),
                        Ok(false) => {
                            match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, a) {
                                Err(e) => Err(e),
                                Ok(a2) => {
                                    match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, b)
                                    {
                                        Err(e) => Err(e),
                                        Ok(b2) => {
                                            if a2.eq2(&b2) {
                                                Ok(true)
                                            } else {
                                                defeq_after_whnf(
                                                    pers,
                                                    vis,
                                                    st, mode, lane, fuel, fe, depth, n,
                                                    pi, &a2, &b2,
                                                )
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
}

/// con-leche: ConLeche/Kernel/Core.lean:1703-1708 defeqLoop
/// Lean twin: `proof/ConRon/Arena/Core.lean:2568-2572 defeqLoop` — the
/// lazy-delta loop: iterate `defeqStep` on its own step budget.
pub fn defeq_loop(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    n: u64,
    pi: bool,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if n == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_DEFEQ_LOOP)))
    } else {
        defeq_step(pers, vis, st, mode, lane, fuel, fe, depth, n - 1, pi, a, b)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1710-1714 defeqLoopFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2577 defeqLoopFuel` — step budget of
/// the lazy-delta loop (lean4lean's `FuelConfig.lazyDelta`).  Exhaustion is an
/// internal error, never a verdict.
pub const DEFEQ_LOOP_FUEL: u64 = 100000;

/// con-leche: ConLeche/Kernel/Core.lean:1716-1719 defeqBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2581-2583 defeqBody` — the
/// definitional-equality body: the lazy-delta loop at its own step budget.
pub fn defeq_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    defeq_loop(pers, vis, st, mode, lane, fuel, fe, depth, DEFEQ_LOOP_FUEL, true, a, b)
}

/// con-leche: ConLeche/Kernel/Core.lean:1721-1730 isPropType
/// Lean twin: `proof/ConRon/Arena/Core.lean:2587-2593 isPropType` — check that a
/// (raw) type is a `Prop` by annotating it and inferring its sort.
pub fn is_prop_type(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
) -> Result<bool, CheckError> {
    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        // io grade: `ty'` is the pass's own output, already annotated
        Ok(typ) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &typ) {
            Err(e) => Err(e),
            Ok(t) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth, &t) {
                Err(e) => Err(e),
                Ok(s) => match zero_level(st) {
                    Err(e) => Err(e),
                    Ok(z) => match lvl_eq(pers, st, &s, &z) {
                        Err(e) => Err(e),
                        Ok(o) => lift_fueled(o),
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The untrusted annotation writes (`Core.lean:2595-2719`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:1015-1016 pwWritten
/// Lean twin: `proof/ConRon/Arena/Core.lean:2601 pwWritten` — is this datum a
/// real (non-placeholder) input annotation?
pub fn pw_written(pw: &PropWhen) -> bool {
    !prop_when::is_never(pw)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:1018-1024 annotBinderMeta
/// Lean twin: `proof/ConRon/Arena/Core.lean:2606-2609 annotBinderMeta` — the
/// datum a rebuilt binder ends up with: the one threaded in from the node
/// below, unless it carries a real input annotation.  Twinned, as con-leche
/// declares it; `annotateBody` inlines the same test.
pub fn annot_binder_meta(pw: Option<PropWhen>, mb: &BinderMeta) -> BinderMeta {
    match pw {
        Some(p) => {
            if pw_written(&mb.pw) {
                expr::binder_meta_dup(mb)
            } else {
                expr::binder_meta(p)
            }
        }
        None => expr::binder_meta_dup(mb),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1746-1777 annotPwPi
/// Lean twin: `proof/ConRon/Arena/Core.lean:2615-2623 annotPwPi` — the ∀ node's
/// datum: the zero-ness of the *codomain*'s sort, on the already-annotated
/// opened body.  The head-symbol reader comes first and subsumes the chain
/// read.
pub fn annot_pw_pi(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    body: &EIdx,
) -> Result<PropWhen, CheckError> {
    match type_sort_pw(pers, vis, st, fe, CORE_WALK_FUEL, body) {
        Err(e) => Err(e),
        Ok(Some(pw)) => Ok(pw),
        // io grade: `body'` is already annotated (bottom-up)
        Ok(None) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, body) {
            Err(e) => Err(e),
            Ok(t) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth, &t) {
                Err(e) => Err(e),
                Ok(v) => match read_level(pers, st, &v) {
                    Err(e) => Err(e),
                    Ok(lv) => Ok(level::zeroness_of(&lv)),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1779-1793 annotPwLam
/// Lean twin: `proof/ConRon/Arena/Core.lean:2627-2635 annotPwLam` — the λ node's
/// datum: the zero-ness of the sort of the *body's type*.
pub fn annot_pw_lam(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    body: &EIdx,
) -> Result<PropWhen, CheckError> {
    match proof_pw(pers, vis, st, fe, CORE_WALK_FUEL, body) {
        Err(e) => Err(e),
        Ok(Some(pw)) => Ok(pw),
        Ok(None) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, body) {
            Err(e) => Err(e),
            Ok(bt) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &bt) {
                Err(e) => Err(e),
                Ok(t) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth, &t) {
                    Err(e) => Err(e),
                    Ok(vb) => match read_level(pers, st, &vb) {
                        Err(e) => Err(e),
                        Ok(lvb) => Ok(level::zeroness_of(&lvb)),
                    },
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The annotation's binder-telescope loops (`Cached/CoreC.lean:1636-1779`)
//
// **The batched instantiation lever, the annotation half** (task #97-P6-11),
// under the ruling before DESIGN.md §8.7: con-leche itself makes the
// multi-substitution move between its PURE and its CACHED tier, so the arena
// may substitute a whole accumulated vector in one walk where the pure
// checker loops `instantiate1` — and the bridge owes the equation con-leche
// already proves.
//
// The spec-shaped clause (`annotate_binder`, which survives below as the λ
// residual) opens the body of EVERY binder of a ∀/λ telescope against one
// fresh free variable and abstracts the annotated result back, so a telescope
// of `k` binders walks its own tail `k` times and re-interns every binder
// under it once per level.  That is task #97-P6-8a's binder excess against
// nanoda, and 17.1 % of the Mathlib prefix's new nodes after task #97-P6-9.
//
// con-leche's cached tier peels the whole telescope instead
// (`annotatePisI`/`annotateLamsI`, its own task #72): each domain is opened
// against the free variables accumulated so far in ONE `instantiateList`, the
// residual leaf is opened once and annotated once, and the outward rebuild
// closes each domain with ONE `abstractRange`.  `ConLeche/Verify/BinderLoop.lean`
// proves both loops sound against the chained bodies
// (`annotatePis_sound:1612`, `annotateLams_sound:1714`), and
// `ConLeche/Verify/Cached/BinderLoopC.lean` relates the cached spelling to
// those pure mirrors clause by clause; §6 of the task section is the ledger.
//
// Two shapes are the arena's rather than con-leche's, for DESIGN.md §3.4's
// reasons and no other:
//
//   * `annotateBindersOutI` takes the node builder `mk` as a function
//     argument.  A closure is what §3.4 rules out, so the arena passes
//     `is_lam : bool` and branches — the same collapse `annotate_binder`
//     already makes over con-leche's two `annotateBody` binder clauses.
//   * the stack is a `Vec<(EIdx, BinderMeta)>` pushed OUTERMOST-first and
//     consumed by a count `n` counting down, where con-leche conses a `List`
//     innermost-first and consumes its head: `stk[j]` is then the binder at
//     level `d + j`, and `j` is exactly the `abstractRange` width its domain
//     wants.  `annotatePisPwI`/`annotateLamsPwI` — the one-line `Option`
//     wrappers around the datum computation — are inlined at the two leaves.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:168-172 peelFuel
/// Lean twin: OWED (task #97-P6-11's ledger) — the fuel of the two telescope
/// peels, con-leche's number verbatim.  Exhaustion is not an error: the loop
/// falls through to its leaf phase with the binders peeled so far, which is
/// con-leche's own `| 0, t, k, fvs, stk => …LeafI` clause.
pub const PEEL_FUEL: u64 = 16777216;

/// con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI
/// Lean twin: OWED (task #97-P6-11's ledger) — the outward rebuild of both
/// annotation telescope loops: fold the stack innermost binder first,
/// rebuilding one binder node per entry.
///
/// `stk[j]` is the binder at level `d + j` and its annotated domain may mention
/// the `j` free variables below it, so `abstract_range ty' d j` is what closes
/// it — where the per-binder clause spent one whole-body `abstract1` per level.
/// `j = 0` (the outermost binder) is `abstract_range_fast`'s own identity clause
/// and costs nothing.
///
/// con-leche's task #161 P5 (the untrusted write): `pw` is the datum written
/// just below, threaded outward — `zeronessOf (imax u v) = zeronessOf v` makes
/// every ∀ node's codomain-sort zero-ness its inner neighbour's, and the λ
/// chain rule says the same of λ nodes, so the telescope pays ONE computation,
/// in the leaf phase, and every node above reads.  A binder whose input datum
/// is a real annotation (`pw_written`) is left alone, and it is that datum that
/// travels on.
pub fn annotate_binders_out(
    pers: &PersTier,
    st: &mut AState,
    is_lam: bool,
    d: u64,
    pw: Option<PropWhen>,
    stk: &Vec<(EIdx, BinderMeta)>,
    n: usize,
    cur: &EIdx,
) -> Result<EIdx, CheckError> {
    if n == 0 {
        Ok(cur.dup2())
    } else {
        let j: usize = n - 1;
        match abstract_range_fast(pers, st, CORE_WALK_FUEL, &stk[j].0, d, j as u64, 0) {
            Err(e) => Err(e),
            Ok(ty_abs) => {
                let written: bool = match pw {
                    Some(_) => true,
                    None => false,
                };
                let m: BinderMeta = annot_binder_meta(pw, &stk[j].1);
                let pw2: Option<PropWhen> = if written {
                    Some(prop_when::dup(&m.pw))
                } else {
                    None
                };
                let node = if is_lam {
                    intern_e(pers, st, ENodeView::Lam(ty_abs, cur.dup2(), m))
                } else {
                    intern_e(pers, st, ENodeView::ForallE(ty_abs, cur.dup2(), m))
                };
                match node {
                    Err(e) => Err(e),
                    Ok(nd) => annotate_binders_out(pers, st, is_lam, d, pw2, stk, j, &nd),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1704-1713 annotatePisLeafI
/// Lean twin: OWED (task #97-P6-11's ledger) — the leaf phase of the ∀
/// telescope loop: bulk-open the residual body against the whole accumulated
/// free-variable vector, annotate it ONCE, compute the telescope's datum once,
/// close the leaf with ONE `abstract_range`, then rebuild outward.
///
/// `annotatePisPwI` (`:1693-1702`) is the `some (annotPwPiI …)` line, inlined:
/// the write is UNGATED in con-leche since 2026-09-06 — writing the datum is
/// part of the real checker's algorithm and only VALIDATING it is
/// certification-only work — so both modes compute it here.
pub fn annotate_pis_leaf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: &Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, fvs, 0) {
        Err(e) => Err(e),
        Ok(to) => match knot_annotate(pers, vis, st, mode, lane, fuel, fe, d + k, &to) {
            Err(e) => Err(e),
            Ok(leafp) => {
                match annot_pw_pi(pers, vis, st, mode, lane, fuel, fe, d + k, &leafp) {
                    Err(e) => Err(e),
                    Ok(p) => match abstract_range_fast(pers, st, CORE_WALK_FUEL, &leafp, d, k, 0) {
                        Err(e) => Err(e),
                        Ok(cur) => {
                            let n: usize = stk.len();
                            annotate_binders_out(pers, st, false, d, Some(p), stk, n, &cur)
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1715-1730 annotatePisI
/// Lean twin: OWED (task #97-P6-11's ledger) — the ∀-telescope annotation
/// loop: peel the raw ∀-chain, annotating each opened domain on the way in.
/// `k >= 1` counts the opened binders (the first is peeled by
/// `annotate_body`'s own clause) and `fvs` holds their free variables
/// innermost-first, which is the list `instantiate_list` takes at cursor 0.
///
/// One peeled domain is ONE `instantiate_list` walk over the domain alone,
/// where the per-binder clause substituted into the whole residual telescope
/// once per level; `Expr.instantiateList_cons`
/// (`ConLeche/Verify/InstList.lean:54-116`) is the equation that identifies the
/// batch with the chain of `instantiate1` the spec-shaped body ran.
pub fn annotate_pis(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    if peel == 0 {
        annotate_pis_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view(pers, st, t) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, body, mb)) => {
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, fvs, 0) {
                    Err(e) => Err(e),
                    Ok(tyo) => {
                        match knot_annotate(pers, vis, st, mode, lane, fuel, fe, d + k, &tyo) {
                            Err(e) => Err(e),
                            Ok(typ) => {
                                match intern_e(pers, st, ENodeView::FVar(d + k, typ.dup2())) {
                                    Err(e) => Err(e),
                                    Ok(fv) => {
                                        let fvs2: Vec<EIdx> = cons_eidx(&fv, fvs);
                                        let mut stk2: Vec<(EIdx, BinderMeta)> = stk;
                                        stk2.push((typ, mb));
                                        annotate_pis(
                                            pers, vis, st, mode, lane, fuel, fe, d, peel - 1,
                                            &body, k + 1, &fvs2, stk2,
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Ok(_) => annotate_pis_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1753-1762 annotateLamsLeafI
/// Lean twin: OWED (task #97-P6-11's ledger) — `annotate_pis_leaf` rebuilding
/// λ nodes, with the λ chain's datum (`annotPwLamI`: the zero-ness of the sort
/// of the innermost body's TYPE) in place of the ∀ telescope's.
/// `annotateLamsPwI` (`:1747-1751`) is inlined with it.
pub fn annotate_lams_leaf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: &Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    match instantiate_list_fast(pers, st, CORE_WALK_FUEL, t, fvs, 0) {
        Err(e) => Err(e),
        Ok(to) => match knot_annotate(pers, vis, st, mode, lane, fuel, fe, d + k, &to) {
            Err(e) => Err(e),
            Ok(leafp) => {
                match annot_pw_lam(pers, vis, st, mode, lane, fuel, fe, d + k, &leafp) {
                    Err(e) => Err(e),
                    Ok(p) => match abstract_range_fast(pers, st, CORE_WALK_FUEL, &leafp, d, k, 0) {
                        Err(e) => Err(e),
                        Ok(cur) => {
                            let n: usize = stk.len();
                            annotate_binders_out(pers, st, true, d, Some(p), stk, n, &cur)
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1764-1777 annotateLamsI
/// Lean twin: OWED (task #97-P6-11's ledger) — the λ twin of `annotate_pis`.
/// Its caller guards it with `bvar_b e == 0` (`annotate_body`'s λ clause):
/// con-leche's own note says the λ loop is chain-identical only on
/// `bvar`-closed nodes, because the chained tails re-open exactly what they
/// closed, and the derived word decides that in O(1).
pub fn annotate_lams(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    d: u64,
    peel: u64,
    t: &EIdx,
    k: u64,
    fvs: &Vec<EIdx>,
    stk: Vec<(EIdx, BinderMeta)>,
) -> Result<EIdx, CheckError> {
    if peel == 0 {
        annotate_lams_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk)
    } else {
        match view(pers, st, t) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(ty, body, mb)) => {
                match instantiate_list_fast(pers, st, CORE_WALK_FUEL, &ty, fvs, 0) {
                    Err(e) => Err(e),
                    Ok(tyo) => {
                        match knot_annotate(pers, vis, st, mode, lane, fuel, fe, d + k, &tyo) {
                            Err(e) => Err(e),
                            Ok(typ) => {
                                match intern_e(pers, st, ENodeView::FVar(d + k, typ.dup2())) {
                                    Err(e) => Err(e),
                                    Ok(fv) => {
                                        let fvs2: Vec<EIdx> = cons_eidx(&fv, fvs);
                                        let mut stk2: Vec<(EIdx, BinderMeta)> = stk;
                                        stk2.push((typ, mb));
                                        annotate_lams(
                                            pers, vis, st, mode, lane, fuel, fe, d, peel - 1,
                                            &body, k + 1, &fvs2, stk2,
                                        )
                                    }
                                }
                            }
                        }
                    }
                }
            }
            Ok(_) => annotate_lams_leaf(pers, vis, st, mode, lane, fuel, fe, d, t, k, fvs, &stk),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2664-2683 annotateBody` — the two
/// binder clauses, which differ only in the node they rebuild and in which
/// datum computation they run when the input annotation is a placeholder.
///
/// Since task #97-P6-11 this is the **λ RESIDUAL** and nothing else:
/// `annotate_body`'s binder clauses run the telescope loops above, and
/// con-leche's cached `annotateBodyI` keeps this single-binder clause for the
/// one case its λ loop does not cover — a λ node whose `bvarB` is not zero.
/// `is_lam = false` is therefore unreachable, exactly as it is in con-leche
/// (whose `.forallE` clause has no such fallback), and on `Init` and on the
/// Mathlib 25 % prefix this function is entered ZERO times: every λ node the
/// annotation pass meets there is `bvar`-closed.
pub fn annotate_binder(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    body: &EIdx,
    mb: &BinderMeta,
    is_lam: bool,
) -> Result<EIdx, CheckError> {
    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(typ) => match intern_e(pers, st, ENodeView::FVar(depth, typ.dup2())) {
            Err(e) => Err(e),
            Ok(fv) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, body, &fv, 0) {
                Err(e) => Err(e),
                Ok(ob) => {
                    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth + 1, &ob) {
                        Err(e) => Err(e),
                        Ok(bodyp) => {
                            let pw = if !pw_written(&mb.pw) {
                                if is_lam {
                                    annot_pw_lam(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth + 1, &bodyp,
                                    )
                                } else {
                                    annot_pw_pi(
                                        pers,
                                        vis,
                                        st, mode, lane, fuel, fe, depth + 1, &bodyp,
                                    )
                                }
                            } else {
                                Ok(prop_when::dup(&mb.pw))
                            };
                            match pw {
                                Err(e) => Err(e),
                                Ok(pw) => {
                                    match abstract1_fast(
                                        pers,
                                        st,
                                        CORE_WALK_FUEL,
                                        &bodyp,
                                        depth,
                                        0,
                                    ) {
                                        Err(e) => Err(e),
                                        Ok(ab) => {
                                            let m = expr::binder_meta(pw);
                                            if is_lam {
                                                intern_e(
                                                    pers,
                                                    st,
                                                    ENodeView::Lam(typ, ab, m),
                                                )
                                            } else {
                                                intern_e(
                                                    pers,
                                                    st,
                                                    ENodeView::ForallE(typ, ab, m),
                                                )
                                            }
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

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2684-2695 annotateBody` — the
/// `.letE` clause: con-leche's task #217 runs the official `infer_let` triple
/// HERE, before the ζ reduct is taken, which is why no other pass ever meets a
/// `let`.
pub fn annotate_let(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    ty: &EIdx,
    v: &EIdx,
    b: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, ty) {
        Err(e) => Err(e),
        Ok(typ) => match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, &typ) {
            Err(e) => Err(e),
            Ok(t) => match ensure_sort(pers, vis, st, mode, lane, fuel, fe, depth, &t) {
                Err(e) => Err(e),
                Ok(_) => match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, v) {
                    Err(e) => Err(e),
                    Ok(vp) => match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, &vp) {
                        Err(e) => Err(e),
                        Ok(tv) => {
                            match knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &tv, &typ) {
                                Err(e) => Err(e),
                                Ok(false) => {
                                    fail(CheckError::Invalid(code_points(&M_LET_VALUE)))
                                }
                                Ok(true) => {
                                    match instantiate1_fast(pers, st, CORE_WALK_FUEL, b, v, 0) {
                                        Err(e) => Err(e),
                                        Ok(bz) => knot_annotate(
                                            pers,
                                            vis,
                                            st, mode, lane, fuel, fe, depth, &bz,
                                        ),
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

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2696-2719 annotateBody` — the
/// `.proj` clause: con-leche's task #271 (issue #7) checks the node's OWN
/// structure name, official's `infer_proj` premise, here.
pub fn annotate_proj(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    sn: &NIdx,
    i: u64,
    pe: &EIdx,
) -> Result<EIdx, CheckError> {
    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, pe) {
        Err(e) => Err(e),
        Ok(ep) => match knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, &ep) {
            Err(e) => Err(e),
            Ok(t) => match knot_whnf(pers, vis, st, mode, lane, fuel, fe, depth, &t) {
                Err(e) => Err(e),
                Ok(te) => match get_app_fn(pers, st, CORE_WALK_FUEL, &te) {
                    Err(e) => Err(e),
                    Ok(hd) => match view(pers, st, &hd) {
                        Err(e) => Err(e),
                        Ok(ENodeView::Const(tn, _)) => {
                            annotate_proj_at(pers, vis, st, fe, sn, i, &ep, &te, &tn)
                        }
                        Ok(_) => {
                            fail(CheckError::NotImplemented(code_points(&M_NONSTRUCT)))
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2701-2718 annotateBody` — the
/// `.proj` clause's body, once the subject type's head is known.
pub fn annotate_proj_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &IFEnv,
    sn: &NIdx,
    i: u64,
    ep: &EIdx,
    te: &EIdx,
    tn: &NIdx,
) -> Result<EIdx, CheckError> {
    match env::ifenv_find_proj(pers, vis, &mut st.store, fe, tn, i) {
        Err(e) => Err(e),
        Ok(Some(entry)) => {
            if !tn.eq2(sn) {
                fail(CheckError::Invalid(code_points(&M_OTHER_STRUCT)))
            } else {
                match get_app_args(pers, st, CORE_WALK_FUEL, te) {
                    Err(e) => Err(e),
                    Ok(targs) => {
                        if targs.len() as u64 != entry.num_params {
                            fail(CheckError::Invalid(code_points(&M_PARAMS)))
                        } else {
                            intern_e(pers, st, ENodeView::Proj(tn.dup2(), i, ep.dup2()))
                        }
                    }
                }
            }
        }
        Ok(None) => match env::ifenv_find_proj(pers, vis, &mut st.store, fe, tn, 0) {
            Err(e) => Err(e),
            Ok(Some(_)) => fail(CheckError::Invalid(code_points(&M_RANGE))),
            Ok(None) => {
                fail(CheckError::NotImplemented(code_points(&M_NONSTRUCTLIKE)))
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
/// Lean twin: `proof/ConRon/Arena/Core.lean:2642-2719 annotateBody` — the
/// annotation body: compute the codomain-sort annotations of every binder,
/// bottom-up, by real inference on the opened (already annotated) body.
pub fn annotate_body(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::BVar(_)) => Ok(e.dup2()),
        // leaf scope check, as in `inferBody`
        Ok(ENodeView::FVar(idx, _)) => {
            if idx < depth {
                Ok(e.dup2())
            } else {
                fail(CheckError::Invalid(code_points(&M_FVAR)))
            }
        }
        Ok(ENodeView::Sort(_)) => Ok(e.dup2()),
        Ok(ENodeView::Const(_, _)) => Ok(e.dup2()),
        Ok(ENodeView::Lit(Literal::NatVal(_))) => match nat_lit_supported(pers, vis, st, fe) {
            Err(er) => Err(er),
            Ok(true) => Ok(e.dup2()),
            Ok(false) => fail(CheckError::Invalid(code_points(&M_NAT))),
        },
        Ok(ENodeView::Lit(Literal::StrVal(_))) => match str_lit_supported(pers, vis, st, fe) {
            Err(er) => Err(er),
            Ok(true) => Ok(e.dup2()),
            Ok(false) => fail(CheckError::NotImplemented(code_points(&M_STR))),
        },
        // structural (con-leche's task #100 stage 6)
        Ok(ENodeView::App(f, a)) => {
            match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, &f) {
                Err(er) => Err(er),
                Ok(fp) => match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, &a) {
                    Err(er) => Err(er),
                    Ok(ap) => {
                        let same: bool = fp.eq2(&f) && ap.eq2(&a);
                        crate::arena::expr_ops::intern_rebuilt(
                            pers,
                            st,
                            e,
                            same,
                            ENodeView::App(fp, ap),
                        )
                    }
                },
            }
        }
        // Binder-telescope loop (con-leche's task #72, `annotateBodyI`'s
        // `.forallE` case): peel the whole ∀-chain, open in bulk, rebuild with
        // `abstract_range`.  The first binder is peeled here, which is why
        // `annotate_pis` starts at `k = 1` with one free variable.
        Ok(ENodeView::ForallE(ty, body, mb)) => {
            match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, &ty) {
                Err(er) => Err(er),
                Ok(typ) => match intern_e(pers, st, ENodeView::FVar(depth, typ.dup2())) {
                    Err(er) => Err(er),
                    Ok(fv) => {
                        let fvs: Vec<EIdx> = cons_eidx(&fv, &Vec::new());
                        let mut stk: Vec<(EIdx, BinderMeta)> = Vec::new();
                        stk.push((typ, mb));
                        annotate_pis(
                            pers, vis, st, mode, lane, fuel, fe, depth, PEEL_FUEL, &body, 1,
                            &fvs, stk,
                        )
                    }
                },
            }
        }
        // con-leche's `annotateBodyI`'s `.lam` case: "the λ-loop is chain-
        // identical only on bvar-closed nodes (the chained tails re-open
        // exactly what they closed); disciplined inputs always are, and the
        // cached bound decides in O(1)".  Otherwise the spec-shaped
        // single-binder clause below runs, unchanged.
        Ok(ENodeView::Lam(ty, body, mb)) => match bvar_b(pers, st, CORE_WALK_FUEL, e) {
            Err(er) => Err(er),
            Ok(b) => {
                if b == 0 {
                    match knot_annotate(pers, vis, st, mode, lane, fuel, fe, depth, &ty) {
                        Err(er) => Err(er),
                        Ok(typ) => match intern_e(pers, st, ENodeView::FVar(depth, typ.dup2())) {
                            Err(er) => Err(er),
                            Ok(fv) => {
                                let fvs: Vec<EIdx> = cons_eidx(&fv, &Vec::new());
                                let mut stk: Vec<(EIdx, BinderMeta)> = Vec::new();
                                stk.push((typ, mb));
                                annotate_lams(
                                    pers, vis, st, mode, lane, fuel, fe, depth, PEEL_FUEL,
                                    &body, 1, &fvs, stk,
                                )
                            }
                        },
                    }
                } else {
                    annotate_binder(
                        pers, vis, st, mode, lane, fuel, fe, depth, &ty, &body, &mb, true,
                    )
                }
            }
        },
        Ok(ENodeView::LetE(ty, v, b)) => {
            annotate_let(pers, vis, st, mode, lane, fuel, fe, depth, &ty, &v, &b)
        }
        Ok(ENodeView::Proj(sn, i, pe)) => {
            annotate_proj(pers, vis, st, mode, lane, fuel, fe, depth, &sn, i, &pe)
        }
    }
}

// ---------------------------------------------------------------------------
// The knot (`Core.lean:2721-2859`)
//
// con-leche's `Core.lean`:2897-2936 with the memo probes of
// `ConLeche/Cached/CoreC.lean`:1877-1906 inlined in the slots (the twin's
// deviation 6).  The six slots are six plain mutually recursive functions
// here (the module note's deviation 1), each taking the `lane` that says which
// of the arena's three knots it belongs to.
//
// The twin's detach-before-update (lesson 14) and `@[noinline]` (lesson 15)
// have no Rust counterpart: `&mut` IS the unique reference the detaching
// manufactures, and `@[noinline]` is a Lean reference-count concern.  The cap
// (DESIGN.md §8.3's lesson 10) and the journal (`arena::core_state`'s module
// note) are in each recorder.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
/// Lean twin: OWED (task #97-P6-7's twin ledger) — **the head kinds
/// `whnfCoreBody` answers with its own argument**, read off the handle's
/// constructor tag without decoding the node.
///
/// `whnfCoreBody`'s first six clauses are `pure e` (`sort`, `fvar`, `forallE`,
/// `lam`, `const`, `lit`); only `app` and `proj` reduce, and `letE`/`bvar`
/// fail.  The knot's slot therefore spends a memo probe, a `view` decode, a
/// `dup` and a memo insert to learn the tag it already had in its hand.  On
/// the Mathlib 25 % prefix that is **61.25 M of the 164.95 M `whnfCore` misses
/// (37.1 %) and 9.57 M of the 33.85 M hits (28.3 %)**, and those 61.25 M rows
/// were also 37 % of the biggest per-declaration table.
///
/// The answer is `e` ITSELF, not a handle denoting the same term, so the
/// clause is handle-identical and the memo it bypasses could only ever have
/// answered `e` too.  It is the same six kinds in `CoreGated`'s body
/// (`core_gated::whnf_core_body_gated`, its first six clauses), which is why
/// the test sits above the lane split rather than inside one arm.
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

/// con-leche: ConLeche/Kernel/Core.lean:1073-1088 whnfStep
/// Lean twin: OWED (task #97-P6-7's twin ledger) — **the head kinds `whnfBody`
/// answers with its own argument**, again off the tag alone.
///
/// One iteration of the reduction loop is `whnfCore`, then `reduceNat`, then
/// `unfoldDefinition`, and it stops when the last two decline.  At `sort`,
/// `fvar`, `lam`, `forallE` and `lit`: `whnfCore` is the identity (above);
/// `reduceNat` matches only an `app`, so it is `none`; and `unfoldDefinition`
/// takes the head of the application spine, which for a non-`app` is the node
/// itself, and matches only a `const`, so it is `none` too.  The loop returns
/// its argument at the first step.
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

/// con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2732-2737 whnfCoreSet` — record a
/// `whnfCore` answer.
pub fn whnf_core_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    if st.caches.whnf_core_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.whnf_core_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.whnf_core_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2741-2746 whnfSet` — record a
/// `whnf` answer.
pub fn whnf_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    if st.caches.whnf_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.whnf_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.whnf_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2750-2755 inferSet` — record a
/// full-grade `infer` answer.
pub fn infer_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    if st.caches.infer_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.infer_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.infer_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2760-2765 inferIOSet` — record an
/// io-grade `infer` answer, in the io grade's OWN table (con-leche's task #170
/// memo ruling).
pub fn infer_io_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    if st.caches.infer_io_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.infer_io_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.infer_io_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:1877-1890 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2769-2774 annotSet` — record an
/// `annotate` answer.
pub fn annot_set(st: &mut AState, e: &EIdx, r: &EIdx) {
    if st.caches.annot_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.annot_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let _ = st.caches.annot_c.insert(e.dup2(), r.dup2());
}

/// con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2779-2784 defeqSet` — record a
/// `defeq` verdict at the ORDERED pair, both signs (con-leche's `defeqC` stores
/// the `Bool` result `r`, which is what makes a negative memo sound).
pub fn defeq_set(st: &mut AState, a: &EIdx, b: &EIdx, r: bool) {
    if st.caches.defeq_c.len() < CACHE_CAP {
        ()
    } else {
        st.caches.defeq_c = con_ron_core::ron::hashmap2::HashMap2::new();
    }
    let k: EIdxPair = eidx_pair(a, b);
    let _ = st.caches.defeq_c.insert(k, r);
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2810 coreKnot` — the `whnfCoreC`
/// probe, over a *shared* state borrow so the map's borrow ends before the
/// miss branch writes (`con_ron_core::cached::core_c::whnf_core_probe`'s
/// reason, task #14's rule).
pub fn whnf_core_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.whnf_core_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2817 coreKnot` — the `whnfC` probe.
pub fn whnf_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.whnf_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2824 coreKnot` — the `inferC` probe.
pub fn infer_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.infer_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2846 coreKnot` — the `inferIOC`
/// probe.
pub fn infer_io_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.infer_io_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2838 coreKnot` — the `annotC`
/// probe.
pub fn annot_probe(st: &AState, e: &EIdx) -> Option<EIdx> {
    match st.caches.annot_c.get(e) {
        Some(r) => Some(r.dup2()),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1893-1906 memoBI
/// Lean twin: `proof/ConRon/Arena/Core.lean:2831 coreKnot` — the `defeqC` probe
/// at the ORDERED pair.
pub fn defeq_probe(st: &AState, k: &EIdxPair) -> Option<bool> {
    match st.caches.defeq_c.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2809-2815 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:107-108 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:42 coreKnotIO` — **the
/// `whnfCore` slot.**  At `LANE_FULL` and `LANE_IO` it is the memoized body
/// (`coreKnotIO`'s slot *is* the full knot's, at the same fuel); at
/// `LANE_GATED` it is `whnfCoreBodyGated` and carries no memo, because the P
/// knot is a specification and a second memoized knot over the same state
/// would let one lane's table answer the other lane's query.
pub fn knot_whnf_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF_CORE)))
    } else if whnf_core_stuck_tag(e) {
        Ok(e.dup2())
    } else if lane == LANE_GATED {
        whnf_core_body_gated(pers, vis, st, mode, lane, fuel - 1, fe, depth, e)
    } else {
        match whnf_core_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_core_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    whnf_core_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2816-2822 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:109 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:43 coreKnotIO` — the `whnf` slot.
pub fn knot_whnf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WHNF)))
    } else if whnf_stuck_tag(e) {
        Ok(e.dup2())
    } else if lane == LANE_GATED {
        whnf_body(pers, vis, st, mode, lane, fuel - 1, fe, depth, e)
    } else {
        match whnf_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    whnf_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// con-leche: ConLeche/Kernel/CoreIO.lean:91-119 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2823-2829 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:110 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:46 coreKnotIO` — **the `infer`
/// slot.**  At `LANE_FULL` it is `inferBody` under `inferC`; at `LANE_GATED`
/// it is `inferBody` tied to the gated knot, unmemoized; at `LANE_IO` it is
/// `inferBodyIO` tied to the io knot, unmemoized (the leaf lane).
pub fn knot_infer(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INFER)))
    } else if lane == LANE_GATED {
        infer_body(pers, vis, st, mode, lane, fuel - 1, fe, depth, e)
    } else if lane == LANE_IO {
        infer_body_io(pers, vis, st, mode, lane, false, fuel - 1, fe, depth, e)
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    infer_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// con-leche: ConLeche/Kernel/CoreIO.lean:91-119 coreKnotIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2844-2859 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:117-118 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:47 coreKnotIO` — **the `inferIO`
/// slot.**  At `LANE_FULL` the selector is `mode.betaGate`, con-leche's
/// `Kernel/Core.lean` spelling and not `Cached/CoreC.lean`'s `mode.ioGate`;
/// the two agree at `.verified`, which is the only mode the bridge is stated
/// at.  The io body runs under its own table (`inferIOC`), the full body under
/// `inferC`: a hit in one grade never serves the other (DESIGN.md §8.3,
/// lesson 9).  `LANE_GATED`'s slot is the parked stage-1 artifact (the twin's
/// comment), and `LANE_IO`'s is its `infer` slot again.
pub fn knot_infer_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INFER)))
    } else if lane == LANE_GATED {
        infer_body(pers, vis, st, mode, lane, fuel - 1, fe, depth, e)
    } else if lane == LANE_IO {
        infer_body_io(pers, vis, st, mode, lane, false, fuel - 1, fe, depth, e)
    } else if con_ron_core::kernel::env::io_gate(mode) {
        match infer_io_probe(st, e) {
            Some(r) => Ok(r),
            None => {
                match infer_body_io(pers, vis, st, mode, LANE_FULL, true, fuel - 1, fe, depth, e) {
                    Err(er) => Err(er),
                    Ok(r) => {
                        infer_io_set(st, e, &r);
                        Ok(r)
                    }
                }
            }
        }
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    infer_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:132-138 CoreFns.ioView
/// con-leche: ConLeche/Cached/CoreC.lean:60-64 CoreFnsI.ioView
/// Lean twin: `proof/ConRon/Arena/Core.lean:271-272 CoreFnsA.ioView` — the knot
/// slot a body's `r.infer` call resolves to: the `infer` slot under the plain
/// record, the `inferIO` slot under its io view.  **This function IS the
/// `ioView` substitution in the port** (`con_ron_core::cached::core_c::
/// infer_at_i`'s own words): the knot is plain functions, so there is no
/// record whose `infer` field can be rebound.
pub fn knot_infer_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    io: bool,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if io {
        knot_infer_io(pers, vis, st, mode, lane, fuel, fe, depth, e)
    } else {
        knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, e)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2830-2836 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:111-112 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:44 coreKnotIO` — the `defeq`
/// slot, memoized at the ORDERED pair.
pub fn knot_defeq(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_DEFEQ)))
    } else if lane == LANE_GATED {
        defeq_body(pers, vis, st, mode, lane, fuel - 1, fe, depth, a, b)
    } else {
        let k: EIdxPair = eidx_pair(a, b);
        match defeq_probe(st, &k) {
            Some(r) => Ok(r),
            None => match defeq_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, a, b) {
                Err(er) => Err(er),
                Ok(r) => {
                    defeq_set(st, a, b, r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1919-1958 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1916-1979 coreKnotI
/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// Lean twin: `proof/ConRon/Arena/Core.lean:2837-2843 coreKnot`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:113-114 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreIO.lean:45 coreKnotIO` — the `annotate`
/// slot.
pub fn knot_annotate(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ANNOTATE)))
    } else if lane == LANE_GATED {
        annotate_body(pers, vis, st, mode, lane, fuel - 1, fe, depth, e)
    } else {
        match annot_probe(st, e) {
            Some(r) => Ok(r),
            None => match annotate_body(pers, vis, st, mode, LANE_FULL, fuel - 1, fe, depth, e) {
                Err(er) => Err(er),
                Ok(r) => {
                    annot_set(st, e, &r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1960-1963 checkFuel
/// Lean twin: `proof/ConRon/Arena/Core.lean:2864 checkFuel` — the shared fuel
/// for the checker core: bounds the recursion depth of reduction, inference
/// and definitional equality.
pub const CHECK_FUEL: u64 = 100000;

// ---------------------------------------------------------------------------
// The fueled entry points (`Core.lean:2866-2923`)
//
// `ConLeche/Kernel/TypeChecker.lean`, whose seven (T) declarations live here
// because the arena has ONE knot (the twin's deviation 5): con-leche's
// `pureFns` is `coreKnot mode env id` at `CheckM` with no memo, and the
// arena's `coreKnot` already carries the memos, so `pureFnsA` is the same
// expression over handles.  `pureFnsA` itself has no Rust counterpart — a
// record of functions is what §3.4 rules out — and its place is taken by
// `LANE_FULL`, which every entry below passes.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/TypeChecker.lean:27-29 whnfCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2884-2886 whnfCore` — head
/// normalization without delta (fueled).
pub fn whnf_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_whnf_core(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:31-33 whnf
/// Lean twin: `proof/ConRon/Arena/Core.lean:2890-2892 whnf` — the full
/// reduction loop (fueled).
pub fn whnf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_whnf(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:35-38 inferTypeCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2896-2898 inferTypeCore` —
/// full-grade type inference (fueled): the declaration front door's entry.
pub fn infer_type_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_infer(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:40-46 inferTypeIO
/// Lean twin: `proof/ConRon/Arena/Core.lean:2903-2905 inferTypeIO` — type
/// inference at the io grade (fueled): what every internal inference call site
/// runs.
pub fn infer_type_io(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_infer_io(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:48-50 isDefEqCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2909-2911 isDefEqCore` —
/// definitional equality (fueled).
pub fn is_def_eq_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    knot_defeq(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, a, b)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:52-54 annotateCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2915-2917 annotateCore` — the
/// annotation pass (fueled).
pub fn annotate_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_annotate(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:56-58 ensureSortCore
/// Lean twin: `proof/ConRon/Arena/Core.lean:2921-2923 ensureSortCore` —
/// `ensureSort` over the knot (fueled).
pub fn ensure_sort_core(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<LIdx, CheckError> {
    ensure_sort(pers, vis, st, mode, LANE_FULL, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/TypeChecker.lean:23-25 pureFns
/// Lean twin: `proof/ConRon/Arena/Core.lean:2879-2880 pureFnsA` — the core,
/// tied at `AM`, fuel in the knot.  The twin's record has no Rust counterpart
/// (§3.4 rules out a record of functions); this constant is what replaces it,
/// and every entry point above passes it.  Named `pureFnsA` in the twin
/// because the arena's is the MEMOIZED knot; con-leche's `pureFns` is its
/// unmemoized specification, whose verdicts the memo does not change.
pub const PURE_FNS_A: u32 = LANE_FULL;

// ---------------------------------------------------------------------------
// The per-declaration bracket (`Core.lean:2925-2958`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:394-398 CState.flushed
/// Lean twin: `proof/ConRon/Arena/Core.lean:3007-3009 flushCaches` — **what
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

/// con-leche: none — **the per-declaration bracket, closed** (DESIGN.md §8.3)
/// Lean twin: `proof/ConRon/Arena/Core.lean:2944-2949 dropScratch` — drop the
/// scratch tier of the store and the cache entries that name it, in one
/// operation, so the two halves cannot drift apart.
pub fn drop_scratch(st: &mut AState) {
    flush_caches(st);
    st.store.drop_scratch();
}

/// con-leche: none — **the per-declaration bracket, opened** (DESIGN.md §8.3)
/// Lean twin: `proof/ConRon/Arena/Core.lean:2954-2958 enterScratch` — turn the
/// scratch tier on, and clear the per-call memo tables of `Memos`, which
/// belong to no tier and whose keys the new tier may reuse.
pub fn enter_scratch(st: &mut AState) {
    st.memos.reset();
    st.store.enable_scratch();
}

// ---------------------------------------------------------------------------
// The differential test (`proof/ConRon/Arena/CoreTest.lean`)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_names;

    /// con-leche: none — a test fixture
    /// The state the driver builds: an empty store with the reserved-name
    /// pins interned (task #97-P6-4a).  Every subject below reads a pin
    /// somewhere, so this is the only state they can run in.
    fn pinned_state() -> AState {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        match crate::arena::pins::intern_reserved_pins(pers, &mut st) {
            Ok(()) => st,
            Err(_) => panic!("the reserved-name pins must intern"),
        }
    }
    use crate::arena::core_gated;
    use crate::arena::core_io;
    use crate::arena::env::{mk_ifenv, IConstantInfo, IEnv};
    use crate::arena::monad::{denote_l, denote_ls, denote_n, intern_levels, intern_name};
    use crate::arena::store::EStore;
    use con_ron_core::cached::core_c;
    use con_ron_core::cached::state_c;
    use con_ron_core::cached::state_c::CState;
    use con_ron_core::kernel::core_types::CheckM;
    use con_ron_core::kernel::env as cenv;
    use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, IndCaps};
    use con_ron_core::kernel::expr::Expr;
    use con_ron_core::kernel::fenv;
    use con_ron_core::kernel::fenv::FEnv;
    use con_ron_core::kernel::name as cname;

    // --- the readback and the `Expr`-tree interning (task #97-P4b's helpers) -

    /// The fuel-indexed readback of an expression handle
    /// (`proof/ConRon/Arena/Denote.lean`'s `denoteEAux`), test-only as task
    /// #97-P4a ruled.
    fn denote_e_aux(pers: &PersTier, st: &EStore, fuel: u64, i: &EIdx) -> Option<Expr> {
        if fuel == 0 {
            return None;
        }
        match st.view(pers, i) {
            None => None,
            Some(ENodeView::BVar(k)) => Some(expr::bvar(k)),
            Some(ENodeView::FVar(k, ty)) => {
                denote_e_aux(pers, st, fuel - 1, &ty).map(|t| expr::fvar(k, t))
            }
            Some(ENodeView::Sort(u)) => denote_l(pers, st.ls(), &u).map(expr::sort),
            Some(ENodeView::Const(n, us)) => {
                match (denote_n(pers, st.ns(), &n), denote_ls(pers, st.ls_s(), &us)) {
                    (Some(a), Some(b)) => Some(expr::mk_const(a, b)),
                    _ => None,
                }
            }
            Some(ENodeView::App(g, a)) => {
                match (denote_e_aux(pers, st, fuel - 1, &g), denote_e_aux(pers, st, fuel - 1, &a)) {
                    (Some(x), Some(y)) => Some(expr::app(x, y)),
                    _ => None,
                }
            }
            Some(ENodeView::Lam(ty, b, m)) => {
                match (denote_e_aux(pers, st, fuel - 1, &ty), denote_e_aux(pers, st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::lam(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::ForallE(ty, b, m)) => {
                match (denote_e_aux(pers, st, fuel - 1, &ty), denote_e_aux(pers, st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::forall_e(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::LetE(ty, v, b)) => match (
                denote_e_aux(pers, st, fuel - 1, &ty),
                denote_e_aux(pers, st, fuel - 1, &v),
                denote_e_aux(pers, st, fuel - 1, &b),
            ) {
                (Some(x), Some(y), Some(z)) => Some(expr::let_e(x, y, z)),
                _ => None,
            },
            Some(ENodeView::Lit(l)) => Some(expr::lit(l)),
            Some(ENodeView::Proj(n, k, e)) => {
                match (denote_n(pers, st.ns(), &n), denote_e_aux(pers, st, fuel - 1, &e)) {
                    (Some(a), Some(x)) => Some(expr::proj(a, k, x)),
                    _ => None,
                }
            }
        }
    }

    /// `denoteE` at the store's own node count as fuel.
    fn denote_e(pers: &PersTier, st: &EStore, i: &EIdx) -> Option<Expr> {
        denote_e_aux(pers, st, st.node_count(pers) as u64 + 1, i)
    }

    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the fixture must build without a decline"),
        }
    }

    /// Intern a whole `Expr` tree, node by node (the twin's `internExprT`).
    fn intern_expr(pers: &PersTier, st: &mut AState, e: &Expr) -> EIdx {
        match expr::view(e) {
            expr::ExprView::Bvar(i) => ok(intern_e(pers, st, ENodeView::BVar(*i))),
            expr::ExprView::Fvar(i, ty) => {
                let t = intern_expr(pers, st, ty);
                ok(intern_e(pers, st, ENodeView::FVar(*i, t)))
            }
            expr::ExprView::Sort(u) => {
                let hu = ok(crate::arena::monad::intern_level(pers, st, u));
                ok(intern_e(pers, st, ENodeView::Sort(hu)))
            }
            expr::ExprView::Const(n, us) => {
                let hn = ok(intern_name(pers, st, n));
                let hus = ok(intern_levels(pers, st, us));
                ok(intern_e(pers, st, ENodeView::Const(hn, hus)))
            }
            expr::ExprView::App(f, a) => {
                let hf = intern_expr(pers, st, f);
                let ha = intern_expr(pers, st, a);
                ok(intern_e(pers, st, ENodeView::App(hf, ha)))
            }
            expr::ExprView::Lam(ty, b, m) => {
                let ht = intern_expr(pers, st, ty);
                let hb = intern_expr(pers, st, b);
                ok(intern_e(pers, st, ENodeView::Lam(ht, hb, expr::binder_meta_dup(m))))
            }
            expr::ExprView::ForallE(ty, b, m) => {
                let ht = intern_expr(pers, st, ty);
                let hb = intern_expr(pers, st, b);
                ok(intern_e(pers, st, ENodeView::ForallE(ht, hb, expr::binder_meta_dup(m))))
            }
            expr::ExprView::LetE(ty, v, b) => {
                let ht = intern_expr(pers, st, ty);
                let hv = intern_expr(pers, st, v);
                let hb = intern_expr(pers, st, b);
                ok(intern_e(pers, st, ENodeView::LetE(ht, hv, hb)))
            }
            expr::ExprView::Lit(l) => ok(intern_e(pers, st, ENodeView::Lit(expr::literal_dup(l)))),
            expr::ExprView::Proj(n, i, sub) => {
                let hn = ok(intern_name(pers, st, n));
                let hs = intern_expr(pers, st, sub);
                ok(intern_e(pers, st, ENodeView::Proj(hn, *i, hs)))
            }
        }
    }

    // --- interning a con-ron-core environment (the twin's `internCI`) --------

    fn intern_names(pers: &PersTier, st: &mut AState, ns: &Vec<Name>) -> Vec<NIdx> {
        ns.iter().map(|n| ok(intern_name(pers, st, n))).collect()
    }

    fn intern_cv(pers: &PersTier, st: &mut AState, cv: &ConstantVal) -> IConstantVal {
        let name = ok(intern_name(pers, st, &cv.name));
        let level_params = intern_names(pers, st, &cv.level_params);
        let ty = intern_expr(pers, st, &cv.ty);
        IConstantVal { name, level_params, ty }
    }

    fn intern_caps(pers: &PersTier, st: &mut AState, c: &IndCaps) -> IIndCaps {
        IIndCaps {
            eta: c.eta,
            eta_ctor: ok(intern_name(pers, st, &c.eta_ctor)),
            eta_params: c.eta_params,
            eta_fields: c.eta_fields,
            unitlike: c.unitlike,
            unit_params: c.unit_params,
            rule_k: c.rule_k,
            sort_z: prop_when::dup(&c.sort_z),
        }
    }

    /// The twin's `internCI`; a `projInfo` is out of this module's scope (the
    /// fixture has no structure), so it panics rather than silently producing
    /// a different environment from con-ron-core's.
    fn intern_ci(pers: &PersTier, st: &mut AState, c: &ConstantInfo) -> IConstantInfo {
        match c {
            ConstantInfo::AxiomInfo(cv) => IConstantInfo::AxiomInfo(intern_cv(pers, st, cv)),
            ConstantInfo::DefnInfo(cv, v, h) => {
                let icv = intern_cv(pers, st, cv);
                let iv = intern_expr(pers, st, v);
                IConstantInfo::DefnInfo(icv, iv, cenv::reducibility_hint_dup(h))
            }
            ConstantInfo::ThmInfo(cv, v) => {
                let icv = intern_cv(pers, st, cv);
                let iv = intern_expr(pers, st, v);
                IConstantInfo::ThmInfo(icv, iv)
            }
            ConstantInfo::IndInfo(cv, caps) => {
                let icv = intern_cv(pers, st, cv);
                let ic = intern_caps(pers, st, caps);
                IConstantInfo::IndInfo(icv, ic)
            }
            ConstantInfo::CtorInfo(cv, n_p, n_f) => {
                IConstantInfo::CtorInfo(intern_cv(pers, st, cv), *n_p, *n_f)
            }
            ConstantInfo::RecInfo(cv, m_i, r_p, _rules) => {
                let icv = intern_cv(pers, st, cv);
                IConstantInfo::RecInfo(icv, *m_i, *r_p, Vec::new())
            }
            ConstantInfo::ProjInfo(_) => panic!("CoreTest: projInfo is out of scope"),
        }
    }

    // --- the fixture ---------------------------------------------------------

    fn nm(s: &str) -> Name {
        cname::mk_str(cname::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn never() -> con_ron_core::kernel::expr::BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    /// The twin's `envCL` and its twenty-three subject terms, as con-ron-core
    /// values: the environment is written ONCE and the arena's is *derived*
    /// from it, so the two cannot drift.
    struct Terms {
        nat_ty: Expr,
        zero_e: Expr,
        prop_e: Expr,
        two: Expr,
        ax: Expr,
        lit7: Expr,
        lit3: Expr,
        succ3: Expr,
        id_nat: Expr,
        beta_two: Expr,
        succ_lam: Expr,
        beta_succ: Expr,
        pi_nat: Expr,
        sort0: Expr,
        sort1: Expr,
        fv0: Expr,
        pf_a: Expr,
        pf_b: Expr,
        id_prop: Expr,
        unknown: Expr,
        let_two: Expr,
        let_bad: Expr,
        app_ax: Expr,
        pi_pi: Expr,
    }

    fn terms() -> Terms {
        let nat_ty = expr::mk_const(basis_names::nat_name(), Vec::new());
        let zero_e = expr::mk_const(basis_names::nat_zero_name(), Vec::new());
        let succ_e = expr::mk_const(basis_names::nat_succ_name(), Vec::new());
        let prop_e = expr::mk_const(nm("P"), Vec::new());
        let id_nat = expr::lam(expr::dup(&nat_ty), expr::bvar(0), never());
        let two = expr::mk_const(nm("two"), Vec::new());
        let ax = expr::mk_const(nm("myax"), Vec::new());
        let lit3 = expr::lit(expr::literal_nat(nat::from_u64(3)));
        let succ_lam = expr::lam(
            expr::dup(&nat_ty),
            expr::app(expr::dup(&succ_e), expr::bvar(0)),
            never(),
        );
        let sort0 = expr::sort(level::zero());
        Terms {
            beta_two: expr::app(expr::dup(&id_nat), expr::dup(&two)),
            app_ax: expr::app(expr::dup(&id_nat), expr::dup(&ax)),
            succ3: expr::app(expr::dup(&succ_e), expr::dup(&lit3)),
            beta_succ: expr::app(expr::dup(&succ_lam), expr::dup(&lit3)),
            pi_nat: expr::forall_e(expr::dup(&nat_ty), expr::dup(&nat_ty), never()),
            pi_pi: expr::forall_e(
                expr::dup(&nat_ty),
                expr::forall_e(expr::dup(&nat_ty), expr::dup(&nat_ty), never()),
                never(),
            ),
            sort1: expr::sort(level::succ(level::zero())),
            fv0: expr::fvar(0, expr::dup(&nat_ty)),
            pf_a: expr::mk_const(nm("pfA"), Vec::new()),
            pf_b: expr::mk_const(nm("pfB"), Vec::new()),
            id_prop: expr::lam(expr::dup(&prop_e), expr::bvar(0), never()),
            unknown: expr::mk_const(nm("nope"), Vec::new()),
            let_two: expr::let_e(expr::dup(&nat_ty), expr::dup(&two), expr::bvar(0)),
            let_bad: expr::let_e(expr::dup(&nat_ty), expr::dup(&sort0), expr::bvar(0)),
            lit7: expr::lit(expr::literal_nat(nat::from_u64(7))),
            lit3,
            sort0,
            succ_lam,
            id_nat,
            two,
            ax,
            prop_e,
            zero_e,
            nat_ty,
        }
    }

    /// The twin's `envCL`, newest first (the order `Env.find?` reads).
    fn env_cl(t: &Terms) -> Vec<ConstantInfo> {
        let cv = |n: Name, ty: Expr| ConstantVal {
            name: n,
            level_params: Vec::new(),
            ty,
        };
        vec![
            ConstantInfo::AxiomInfo(cv(nm("pfB"), expr::dup(&t.prop_e))),
            ConstantInfo::AxiomInfo(cv(nm("pfA"), expr::dup(&t.prop_e))),
            ConstantInfo::AxiomInfo(cv(nm("P"), expr::sort(level::zero()))),
            ConstantInfo::AxiomInfo(cv(nm("myax"), expr::dup(&t.nat_ty))),
            ConstantInfo::DefnInfo(
                cv(nm("two"), expr::dup(&t.nat_ty)),
                expr::app(
                    expr::mk_const(basis_names::nat_succ_name(), Vec::new()),
                    expr::app(
                        expr::mk_const(basis_names::nat_succ_name(), Vec::new()),
                        expr::dup(&t.zero_e),
                    ),
                ),
                cenv::ReducibilityHint::Regular(1),
            ),
            ConstantInfo::CtorInfo(
                cv(
                    basis_names::nat_succ_name(),
                    expr::forall_e(expr::dup(&t.nat_ty), expr::dup(&t.nat_ty), never()),
                ),
                0,
                1,
            ),
            ConstantInfo::CtorInfo(cv(basis_names::nat_zero_name(), expr::dup(&t.nat_ty)), 0, 0),
            ConstantInfo::IndInfo(
                cv(
                    basis_names::nat_name(),
                    expr::sort(level::succ(level::zero())),
                ),
                cenv::ind_caps_default(),
            ),
        ]
    }

    /// The twin's `Fx`: the handles every check names, beside the
    /// con-ron-core terms they denote and the two environments.
    struct Fx {
        st: AState,
        fe: IFEnv,
        cst: CState,
        cfe: FEnv,
        t: Terms,
        two: EIdx,
        ax: EIdx,
        lit7: EIdx,
        #[allow(dead_code)]
        lit3: EIdx,
        succ3: EIdx,
        id_nat: EIdx,
        beta_two: EIdx,
        succ_lam: EIdx,
        beta_succ: EIdx,
        pi_nat: EIdx,
        sort0: EIdx,
        sort1: EIdx,
        fv0: EIdx,
        pf_a: EIdx,
        pf_b: EIdx,
        id_prop: EIdx,
        unknown: EIdx,
        let_two: EIdx,
        let_bad: EIdx,
        app_ax: EIdx,
        pi_pi: EIdx,
        nat: EIdx,
        zero: EIdx,
    }

    /// The twin's `buildFx`: intern the environment, index it, and intern
    /// every subject term.
    fn build_fx() -> Fx {
        let pers: &PersTier = &PersTier::empty();
        let t = terms();
        let cs = env_cl(&t);
        let cfe = fenv::mk_fenv(cenv::env_of(&cs));
        let mut st = pinned_state();
        // the arena's `IEnv.consts` is oldest-first, so the cited
        // (newest-first) list is interned back to front
        let mut ics: Vec<IConstantInfo> = Vec::new();
        for c in cs.iter().rev() {
            let ic = intern_ci(pers, &mut st, c);
            ics.push(ic);
        }
        let fe = mk_ifenv(IEnv { consts: ics });
        let two = intern_expr(pers, &mut st, &t.two);
        let ax = intern_expr(pers, &mut st, &t.ax);
        let lit7 = intern_expr(pers, &mut st, &t.lit7);
        let lit3 = intern_expr(pers, &mut st, &t.lit3);
        let succ3 = intern_expr(pers, &mut st, &t.succ3);
        let id_nat = intern_expr(pers, &mut st, &t.id_nat);
        let beta_two = intern_expr(pers, &mut st, &t.beta_two);
        let succ_lam = intern_expr(pers, &mut st, &t.succ_lam);
        let beta_succ = intern_expr(pers, &mut st, &t.beta_succ);
        let pi_nat = intern_expr(pers, &mut st, &t.pi_nat);
        let sort0 = intern_expr(pers, &mut st, &t.sort0);
        let sort1 = intern_expr(pers, &mut st, &t.sort1);
        let fv0 = intern_expr(pers, &mut st, &t.fv0);
        let pf_a = intern_expr(pers, &mut st, &t.pf_a);
        let pf_b = intern_expr(pers, &mut st, &t.pf_b);
        let id_prop = intern_expr(pers, &mut st, &t.id_prop);
        let unknown = intern_expr(pers, &mut st, &t.unknown);
        let let_two = intern_expr(pers, &mut st, &t.let_two);
        let let_bad = intern_expr(pers, &mut st, &t.let_bad);
        let app_ax = intern_expr(pers, &mut st, &t.app_ax);
        let pi_pi = intern_expr(pers, &mut st, &t.pi_pi);
        let nat = intern_expr(pers, &mut st, &t.nat_ty);
        let zero = intern_expr(pers, &mut st, &t.zero_e);
        Fx {
            st,
            fe,
            cst: state_c::cstate_new(),
            cfe,
            t,
            two,
            ax,
            lit7,
            lit3,
            succ3,
            id_nat,
            beta_two,
            succ_lam,
            beta_succ,
            pi_nat,
            sort0,
            sort1,
            fv0,
            pf_a,
            pf_b,
            id_prop,
            unknown,
            let_two,
            let_bad,
            app_ax,
            pi_pi,
            nat,
            zero,
        }
    }

    // --- the mode, the fuel, and the outcome comparison ----------------------

    /// The twin's `MU`: `.verified`, the lane the bridge is stated at and the
    /// one where the arena's io selector (`mode.betaGate`) and con-leche's
    /// cached one (`mode.ioGate`) agree.
    fn mu() -> CheckMode {
        CheckMode::Verified
    }

    /// The twin's `F`: the knot fuel and the ambient depth.
    const F: u64 = 60;

    /// The twin's `errEq`: same constructor, same message.  `Native` has no
    /// con-leche counterpart and never matches, which is right — a `Native`
    /// claims nothing.
    fn err_eq(a: &CheckError, b: &CheckError) -> bool {
        match (a, b) {
            (CheckError::NotImplemented(x), CheckError::NotImplemented(y)) => {
                cname::str_eq(x, y)
            }
            (CheckError::Invalid(x), CheckError::Invalid(y)) => cname::str_eq(x, y),
            (CheckError::Internal(x), CheckError::Internal(y)) => cname::str_eq(x, y),
            _ => false,
        }
    }

    /// The twin's `chkE`: an `EIdx`-valued entry point against con-ron-core's
    /// `Expr`-valued one, over the WHOLE outcome.
    fn chk_e(
        pers: &PersTier,
        st: &AState,
        got: Result<EIdx, CheckError>,
        want: CheckM<Expr>,
    ) -> bool  {
        match (got, want) {
            (Ok(r), Ok(e)) => match denote_e(pers, &st.store, &r) {
                Some(x) => expr::beq(&x, &e),
                None => false,
            },
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// The twin's `chkB`: a `bool`-valued entry point (definitional equality)
    /// against con-ron-core's, over the whole outcome.
    fn chk_b(got: Result<bool, CheckError>, want: CheckM<bool>) -> bool {
        match (got, want) {
            (Ok(r), Ok(e)) => r == e,
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    /// The twin's `chkL`: an `LIdx`-valued entry point against con-ron-core's
    /// `Level`-valued one.
    fn chk_l(
        pers: &PersTier,
        st: &AState,
        got: Result<LIdx, CheckError>,
        want: CheckM<Level>,
    ) -> bool  {
        match (got, want) {
            (Ok(r), Ok(u)) => match denote_l(pers, st.store.ls(), &r) {
                Some(x) => level::beq(&x, &u),
                None => false,
            },
            (Err(a), Err(b)) => err_eq(&a, &b),
            _ => false,
        }
    }

    fn ok_e(got: CheckM<Expr>, e: &Expr) -> bool {
        match got {
            Ok(a) => expr::beq(&a, e),
            Err(_) => false,
        }
    }

    fn ok_b(got: CheckM<bool>, b: bool) -> bool {
        match got {
            Ok(a) => a == b,
            Err(_) => false,
        }
    }

    // --- 1. the fixture builds, and denotes what it should (9) ---------------

    #[test]
    fn fixture_denotes_what_it_should() {
        let pers: &PersTier = &PersTier::empty();
        let f = build_fx();
        // the fixture built without a `Native` or an internal error: every
        // `intern_expr` above went through `ok`, which panics otherwise
        assert!(f.st.store.node_count(pers) > 0);
        assert!(expr::beq(&denote_e(pers, &f.st.store, &f.two).unwrap(), &f.t.two));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &f.beta_two).unwrap(),
            &f.t.beta_two
        ));
        assert!(expr::beq(&denote_e(pers, &f.st.store, &f.pi_pi).unwrap(), &f.t.pi_pi));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &f.let_bad).unwrap(),
            &f.t.let_bad
        ));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &f.id_prop).unwrap(),
            &f.t.id_prop
        ));
        assert!(expr::beq(&denote_e(pers, &f.st.store, &f.succ3).unwrap(), &f.t.succ3));
        assert!(f.fe.env.consts.len() == 8);
        let last = env::i_constant_info_name(&f.fe.env.consts[7]);
        assert!(env::ifenv_find(f.fe.visible_below, &f.fe, &last).is_some());
    }

    // --- 2. the positive outcomes, pinned by hand (7) ------------------------

    #[test]
    fn the_positive_outcomes_are_what_they_should_be() {
        let mut f = build_fx();
        let m = mu();
        assert!(ok_e(
            core_c::whnf(&m, F, &mut f.cst, &f.cfe, 0, &f.t.two),
            &expr::lit(expr::literal_nat(nat::from_u64(2)))
        ));
        assert!(ok_e(
            core_c::whnf(&m, F, &mut f.cst, &f.cfe, 0, &f.t.beta_succ),
            &expr::lit(expr::literal_nat(nat::from_u64(4)))
        ));
        assert!(ok_e(
            core_c::infer(&m, F, &mut f.cst, &f.cfe, 0, &f.t.lit7),
            &f.t.nat_ty
        ));
        assert!(ok_e(
            core_c::infer(&m, F, &mut f.cst, &f.cfe, 0, &f.t.id_nat),
            &f.t.pi_nat
        ));
        assert!(ok_b(
            core_c::defeq(&m, F, &mut f.cst, &f.cfe, 0, &f.t.pf_a, &f.t.pf_b),
            true
        ));
        assert!(ok_b(
            core_c::defeq(&m, F, &mut f.cst, &f.cfe, 0, &f.t.two, &f.t.lit7),
            false
        ));
        assert!(ok_e(
            core_c::annotate(&m, F, &mut f.cst, &f.cfe, 0, &f.t.id_prop),
            &expr::lam(
                expr::dup(&f.t.prop_e),
                expr::bvar(0),
                expr::binder_meta(prop_when::if_all_zero(Vec::new()))
            )
        ));
    }

    /// The mirror of the seven hand-pinned outcomes above, on the ARENA side.
    /// The twin does not have it — `chkE` forces the arena to con-leche's
    /// answer and con-leche's is pinned — but spelling it out here costs seven
    /// lines and makes the differential's non-vacuity visible from either end.
    #[test]
    fn the_arena_side_of_the_pinned_outcomes() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let two = ok(whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &two).unwrap(),
            &expr::lit(expr::literal_nat(nat::from_u64(2)))
        ));
        let four = ok(whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.beta_succ));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &four).unwrap(),
            &expr::lit(expr::literal_nat(nat::from_u64(4)))
        ));
        let t7 = ok(infer_type_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.lit7));
        assert!(expr::beq(&denote_e(pers, &f.st.store, &t7).unwrap(), &f.t.nat_ty));
        let tid = ok(infer_type_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.id_nat));
        assert!(expr::beq(&denote_e(pers, &f.st.store, &tid).unwrap(), &f.t.pi_nat));
        assert!(ok(is_def_eq_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.pf_a, &f.pf_b)));
        assert!(!ok(is_def_eq_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two, &f.lit7)));
        let ann = ok(annotate_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.id_prop));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &ann).unwrap(),
            &expr::lam(
                expr::dup(&f.t.prop_e),
                expr::bvar(0),
                expr::binder_meta(prop_when::if_all_zero(Vec::new()))
            )
        ));
    }

    // --- 3. `whnf` — twelve subjects -----------------------------------------

    #[test]
    fn whnf_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr, u64)> = vec![
            (f.two.dup2(), expr::dup(&f.t.two), 0),
            (f.ax.dup2(), expr::dup(&f.t.ax), 0),
            (f.lit7.dup2(), expr::dup(&f.t.lit7), 0),
            (f.succ3.dup2(), expr::dup(&f.t.succ3), 0),
            (f.beta_two.dup2(), expr::dup(&f.t.beta_two), 0),
            (f.beta_succ.dup2(), expr::dup(&f.t.beta_succ), 0),
            (f.pi_nat.dup2(), expr::dup(&f.t.pi_nat), 0),
            (f.sort0.dup2(), expr::dup(&f.t.sort0), 0),
            (f.fv0.dup2(), expr::dup(&f.t.fv0), 1),
            (f.id_nat.dup2(), expr::dup(&f.t.id_nat), 0),
            (f.app_ax.dup2(), expr::dup(&f.t.app_ax), 0),
            (f.nat.dup2(), expr::dup(&f.t.nat_ty), 0),
        ];
        for (h, e, d) in subjects.iter() {
            let got = whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, *d, h);
            let want = core_c::whnf(&m, F, &mut f.cst, &f.cfe, *d, e);
            assert!(chk_e(pers, &f.st, got, want), "whnf disagreed");
        }
    }

    // --- 4. `whnfCore` — the delta-free head normal form (4) ------------------

    #[test]
    fn whnf_core_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr)> = vec![
            (f.two.dup2(), expr::dup(&f.t.two)),
            (f.beta_two.dup2(), expr::dup(&f.t.beta_two)),
            (f.succ3.dup2(), expr::dup(&f.t.succ3)),
            (f.pi_pi.dup2(), expr::dup(&f.t.pi_pi)),
        ];
        for (h, e) in subjects.iter() {
            let got = whnf_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, h);
            let want = core_c::whnf_core(&m, F, &mut f.cst, &f.cfe, 0, e);
            assert!(chk_e(pers, &f.st, got, want));
        }
        // `whnfCore` must NOT unfold `two`, where `whnf` does
        let wc = ok(whnf_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two));
        assert!(expr::beq(
            &denote_e(pers, &f.st.store, &wc).unwrap(),
            &f.t.two
        ));
    }

    // --- 5. `infer` — twelve subjects, the last two failures ------------------

    #[test]
    fn infer_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr, u64)> = vec![
            (f.sort0.dup2(), expr::dup(&f.t.sort0), 0),
            (f.sort1.dup2(), expr::dup(&f.t.sort1), 0),
            (f.lit7.dup2(), expr::dup(&f.t.lit7), 0),
            (f.two.dup2(), expr::dup(&f.t.two), 0),
            (f.ax.dup2(), expr::dup(&f.t.ax), 0),
            (f.pf_a.dup2(), expr::dup(&f.t.pf_a), 0),
            (f.succ3.dup2(), expr::dup(&f.t.succ3), 0),
            (f.id_nat.dup2(), expr::dup(&f.t.id_nat), 0),
            (f.pi_nat.dup2(), expr::dup(&f.t.pi_nat), 0),
            (f.fv0.dup2(), expr::dup(&f.t.fv0), 1),
            // the two failure shapes: an unknown constant, and an
            // out-of-scope `fvar`
            (f.unknown.dup2(), expr::dup(&f.t.unknown), 0),
            (f.fv0.dup2(), expr::dup(&f.t.fv0), 0),
        ];
        for (h, e, d) in subjects.iter() {
            let got = infer_type_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, *d, h);
            let want = core_c::infer(&m, F, &mut f.cst, &f.cfe, *d, e);
            assert!(chk_e(pers, &f.st, got, want));
        }
    }

    // --- 6. `inferIO` — the io grade, under its own memo (3) ------------------

    #[test]
    fn infer_io_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr)> = vec![
            (f.two.dup2(), expr::dup(&f.t.two)),
            (f.id_nat.dup2(), expr::dup(&f.t.id_nat)),
            (f.succ3.dup2(), expr::dup(&f.t.succ3)),
        ];
        for (h, e) in subjects.iter() {
            let got = infer_type_io(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, h);
            let want = core_c::infer_io(&m, F, &mut f.cst, &f.cfe, 0, e);
            assert!(chk_e(pers, &f.st, got, want));
        }
    }

    // --- 7. `defeq` — twelve pairs, both verdicts -----------------------------

    #[test]
    fn defeq_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let pairs: Vec<(EIdx, EIdx, Expr, Expr)> = vec![
            (f.two.dup2(), f.two.dup2(), expr::dup(&f.t.two), expr::dup(&f.t.two)),
            (f.two.dup2(), f.lit7.dup2(), expr::dup(&f.t.two), expr::dup(&f.t.lit7)),
            (
                f.zero.dup2(),
                f.zero.dup2(),
                expr::dup(&f.t.zero_e),
                expr::dup(&f.t.zero_e),
            ),
            (f.pf_a.dup2(), f.pf_b.dup2(), expr::dup(&f.t.pf_a), expr::dup(&f.t.pf_b)),
            (f.pf_a.dup2(), f.pf_a.dup2(), expr::dup(&f.t.pf_a), expr::dup(&f.t.pf_a)),
            (
                f.sort0.dup2(),
                f.sort1.dup2(),
                expr::dup(&f.t.sort0),
                expr::dup(&f.t.sort1),
            ),
            (
                f.sort0.dup2(),
                f.sort0.dup2(),
                expr::dup(&f.t.sort0),
                expr::dup(&f.t.sort0),
            ),
            (
                f.id_nat.dup2(),
                f.id_nat.dup2(),
                expr::dup(&f.t.id_nat),
                expr::dup(&f.t.id_nat),
            ),
            (
                f.pi_nat.dup2(),
                f.pi_nat.dup2(),
                expr::dup(&f.t.pi_nat),
                expr::dup(&f.t.pi_nat),
            ),
            (f.ax.dup2(), f.two.dup2(), expr::dup(&f.t.ax), expr::dup(&f.t.two)),
            (
                f.beta_two.dup2(),
                f.succ3.dup2(),
                expr::dup(&f.t.beta_two),
                expr::dup(&f.t.succ3),
            ),
            (
                f.nat.dup2(),
                f.sort0.dup2(),
                expr::dup(&f.t.nat_ty),
                expr::dup(&f.t.sort0),
            ),
        ];
        for (ha, hb, ea, eb) in pairs.iter() {
            let got = is_def_eq_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, ha, hb);
            let want = core_c::defeq(&m, F, &mut f.cst, &f.cfe, 0, ea, eb);
            assert!(chk_b(got, want));
        }
    }

    // --- 8. `annotate` — twelve subjects, the last two failures ---------------

    #[test]
    fn annotate_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr)> = vec![
            (f.sort0.dup2(), expr::dup(&f.t.sort0)),
            (f.lit7.dup2(), expr::dup(&f.t.lit7)),
            (f.two.dup2(), expr::dup(&f.t.two)),
            (f.id_nat.dup2(), expr::dup(&f.t.id_nat)),
            (f.id_prop.dup2(), expr::dup(&f.t.id_prop)),
            (f.pi_nat.dup2(), expr::dup(&f.t.pi_nat)),
            (f.pi_pi.dup2(), expr::dup(&f.t.pi_pi)),
            (f.succ3.dup2(), expr::dup(&f.t.succ3)),
            (f.succ_lam.dup2(), expr::dup(&f.t.succ_lam)),
            (f.let_two.dup2(), expr::dup(&f.t.let_two)),
            // the two failure shapes: a let whose value does not fit its
            // type, and an out-of-scope free variable
            (f.let_bad.dup2(), expr::dup(&f.t.let_bad)),
            (f.fv0.dup2(), expr::dup(&f.t.fv0)),
        ];
        for (h, e) in subjects.iter() {
            let got = annotate_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, h);
            let want = core_c::annotate(&m, F, &mut f.cst, &f.cfe, 0, e);
            assert!(chk_e(pers, &f.st, got, want));
        }
    }

    // --- 9. `ensureSort` (3) --------------------------------------------------

    #[test]
    fn ensure_sort_agrees() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let subjects: Vec<(EIdx, Expr)> = vec![
            (f.nat.dup2(), expr::dup(&f.t.nat_ty)),
            (f.sort0.dup2(), expr::dup(&f.t.sort0)),
            (f.two.dup2(), expr::dup(&f.t.two)),
        ];
        for (h, e) in subjects.iter() {
            let got = ensure_sort_core(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, h);
            let want = core_c::ensure_sort_i(&m, F, &mut f.cst, &f.cfe, 0, e);
            assert!(chk_l(pers, &f.st, got, want));
        }
    }

    // --- 10. the memos and the declaration bracket (9) ------------------------

    #[test]
    fn the_memos_hit_and_answer_identically() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        // the `whnf` table is empty before the first call and carries the
        // subject afterwards
        let before = f.st.caches.whnf_c.contains_key(&f.two);
        let r1 = ok(whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two));
        let after = f.st.caches.whnf_c.contains_key(&f.two);
        assert!(!before);
        assert!(after);
        // the second call returns the same handle as the first
        let r2 = ok(whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two));
        assert!(r1.eq2(&r2));
        // …and the second call is a HIT: it is answered from the table
        let hit = whnf_probe(&f.st, &f.two).unwrap();
        let r3 = ok(whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two));
        assert!(hit.eq2(&r3));
        // the three infer grades keep three tables: a `whnf` run populates
        // `whnfC` and `whnfCoreC`, never `annotC`
        assert!(f.st.caches.whnf_c.len() > 0);
        assert!(f.st.caches.whnf_core_c.len() > 0);
        assert!(f.st.caches.annot_c.len() == 0);
        // a full-grade `infer` populates `inferC`; the io grade populates
        // `inferIOC` (DESIGN.md §8.3, lesson 9)
        let mut g = build_fx();
        let _ = infer_type_core(pers, g.fe.visible_below, &mut g.st, &m, &g.fe, F, 0, &g.succ3);
        assert!(g.st.caches.infer_c.len() > 0);
        let mut h = build_fx();
        let _ = infer_type_io(pers, h.fe.visible_below, &mut h.st, &m, &h.fe, F, 0, &h.succ3);
        assert!(h.st.caches.infer_io_c.len() > 0);
        // the `defeq` table stores the verdict at the ordered pair, both
        // signs: a `false` answer is memoized too
        let mut k = build_fx();
        let v1 = ok(is_def_eq_core(pers, k.fe.visible_below, &mut k.st, &m, &k.fe, F, 0, &k.two, &k.lit7));
        let probe = defeq_probe(&k.st, &eidx_pair(&k.two, &k.lit7));
        let v2 = ok(is_def_eq_core(pers, k.fe.visible_below, &mut k.st, &m, &k.fe, F, 0, &k.two, &k.lit7));
        assert!(probe == Some(v1) && v1 == v2 && !v1);
    }

    #[test]
    fn the_declaration_bracket_flushes_the_caches_whole() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        // the caches go whole, persistent rows included: `drop_scratch` is
        // con-leche's `flushC` (task #97f, P2f — DESIGN.md §8.3's survivor
        // policy is amended, and the twin's `#guard` says the same)
        let _ = whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two);
        let before = f.st.caches.whnf_c.len();
        enter_scratch(&mut f.st);
        drop_scratch(&mut f.st);
        assert!(before > 0);
        assert!(f.st.caches.whnf_c.len() == 0);
        // the SPECIFICATION of a surviving row is still there, and still
        // says this row could have stayed: `whnf` of a persistent handle
        // outside a scratch tier answers with a persistent handle, so
        // `keep_e` holds of the row the flush just threw away.  (The journal
        // walk that used to spell the filter went with the journals at task
        // #97-P6-1; the predicate is what P3 states `flushC`'s soundness
        // against, and the twin's `Caches.dropScratchEntries` is where.)
        let mut g = build_fx();
        let r = ok(whnf(pers, g.fe.visible_below, &mut g.st, &m, &g.fe, F, 0, &g.two));
        assert!(crate::arena::core_state::keep_e(&g.two, &r));
    }

    #[test]
    fn the_declaration_bracket_drops_the_scratch_rows() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        // an entry whose VALUE is a scratch handle does not survive.  The
        // subject is an APPLICATION and not the literal it was until task
        // #97-P6-7: `whnf` of a literal now answers off the constructor tag
        // and never reaches the memo (`whnf_stuck_tag`), so a literal would
        // test nothing here.  `Nat 123456` is stuck — no beta, no iota, and
        // `Nat` is an inductive and not a definition to unfold — so `whnf`
        // answers it with itself and records that answer.
        enter_scratch(&mut f.st);
        let lit = ok(intern_e(
            pers,
            &mut f.st,
            ENodeView::Lit(expr::literal_nat(nat::from_u64(123456))),
        ));
        let h = ok(intern_e(pers, &mut f.st, ENodeView::App(f.nat.dup2(), lit)));
        let _ = whnf(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &h);
        let inside = f.st.caches.whnf_c.contains_key(&h);
        let scratch = !h.is_persistent();
        drop_scratch(&mut f.st);
        let after = f.st.caches.whnf_c.contains_key(&h);
        assert!(inside);
        assert!(scratch);
        assert!(!after);
    }

    // --- 11. the gated and io knots (6) ---------------------------------------

    /// The twin compares the gated and io lanes against con-leche's OWN gated
    /// and io lanes; `con-ron-core` has neither (census class (S): "the Rust
    /// port skips them, because the port has one knot"), so the partner here
    /// is the executed core.  That is the weaker check the twin's own note
    /// describes — "what these check is that they are not *broken*" — and at
    /// `.verified` it is exact: the gated `whnfCore`'s gate
    /// (`verifiedChecks && pw.isNever`) and `betaGateFires`
    /// (`betaGate && pw.isNever`) agree there, and the io lane's `infer` is
    /// the same body the memoized io slot runs.
    #[test]
    fn the_gated_and_io_knots_agree_with_the_executed_one() {
        let pers: &PersTier = &PersTier::empty();
        let mut f = build_fx();
        let m = mu();
        let got = core_gated::whnf_core_gated(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.beta_two);
        let want = core_c::whnf_core(&m, F, &mut f.cst, &f.cfe, 0, &f.t.beta_two);
        assert!(chk_e(pers, &f.st, got, want));

        let got = core_gated::whnf_gated(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.two);
        let want = core_c::whnf(&m, F, &mut f.cst, &f.cfe, 0, &f.t.two);
        assert!(chk_e(pers, &f.st, got, want));

        let got = core_gated::infer_type_core_gated(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.succ3);
        let want = core_c::infer(&m, F, &mut f.cst, &f.cfe, 0, &f.t.succ3);
        assert!(chk_e(pers, &f.st, got, want));

        let got = core_io::infer_type_core_io(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.succ3);
        let want = core_c::infer_io(&m, F, &mut f.cst, &f.cfe, 0, &f.t.succ3);
        assert!(chk_e(pers, &f.st, got, want));

        let got = core_gated::annotate_core_gated(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.id_prop);
        let want = core_c::annotate(&m, F, &mut f.cst, &f.cfe, 0, &f.t.id_prop);
        assert!(chk_e(pers, &f.st, got, want));

        let got = core_gated::is_def_eq_core_gated(pers, f.fe.visible_below, &mut f.st, &m, &f.fe, F, 0, &f.pf_a, &f.pf_b);
        let want = core_c::defeq(&m, F, &mut f.cst, &f.cfe, 0, &f.t.pf_a, &f.t.pf_b);
        assert!(chk_b(got, want));
    }
}
