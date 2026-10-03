//! `arena::expr_ops` — the `ExprOps` twins of (C).
//!
//! The Rust twin of `proof/ConRon/Arena/ExprOps.lean`, which is itself
//! `ConLeche/Kernel/ExprOps.lean` clause for clause over handles: **63
//! functions covering 70 con-leche declarations**, same names in snake_case,
//! same fuel arguments, same memo keys, same cutoffs.  DESIGN.md §8.6's
//! lockstep ruling (code first, proofs later) means this file and the Lean
//! twin are written together and must stay term for term apart.
//!
//! ## The four rules the twin is written by, and what they become here
//!
//! 1. **`view` where con-leche matched, `intern` where it built, handle
//!    equality where it compared** (DESIGN.md §8.3).  A leaf arm con-leche
//!    writes as `| .fvar idx ty => .fvar idx ty` is `Ok(h.dup2())`: the node
//!    is already in the store and `denoteE` is injective, so rebuilding it
//!    would give the same handle.
//! 2. **Fuel.**  A handle DAG has no structural order, so every walk over it
//!    takes an explicit `fuel` and declines when it runs out.  A recursion
//!    structural on something else — a binder count (`strip_pis`), an
//!    argument list (`mk_app_n`) — takes none, exactly as the twin's does.
//!    Lean's `| fuel + 1, …` pattern is `if fuel == 0 { fail } else { … fuel
//!    - 1 … }`.
//! 3. **The memo lives in the state.**  con-leche threads it as an
//!    argument-and-result pair and `con_ron_core::kernel::expr_ops` as a
//!    `&mut HashMap`; here it is a field of `AState`, keyed `(EIdx, cursor)`,
//!    dropped at the top-level entry — which is why the substituted term is
//!    not in the key.  Each `…_fast` entry is con-leche's `(…Go v {} e d).1`:
//!    clear, walk, clear.
//! 4. **One function per intended Rust function, arms inline.**  The twin
//!    inlines its constructor arms deliberately (its own note: the only way
//!    to split them that `mvcgen` likes passes the dispatcher in as a
//!    function argument, and a closure is what DESIGN.md §3.4 forbids).  The
//!    Rust does the same, so the two are one-to-one; when P3 splits them into
//!    a `mutual` block the Rust splits the same way.
//!
//! ## The cutoffs (DESIGN.md §8.3 lesson 20)
//!
//! | walk | cutoff | con-leche's licence |
//! |---|---|---|
//! | `instantiate1_go` | `bvarBRaw < satRange && bvarBRaw <= d` | task #97s's `instantiate1_of_bvarBound_le` |
//! | `abstract1_go` | `fvarB <= d` | `abstract1_of_fvarRange_le` |
//! | `lower_bvars_go` | `bvarB <= c + amount` | `lowerBVars_of_bvarBound_le` |
//! | `instantiate1_lift_go` | `bvarB <= d` | `instantiate1Lift_of_bvarBound_le` |
//! | `inst_lp_go` | `hasLP = false` | `Expr.instantiateLevelParams_eq_self` |
//!
//! `instantiate1`'s is the one cutoff con-leche does NOT have; DESIGN.md §8.3
//! asks for it by name and the twin takes it, so the port takes it too.
//! `instantiate_list` and `lift_loose_bvars` have none, here as there: a
//! cutoff the original does not have needs its own licence proved.
//!
//! ## Where the Rust is not the twin term for term
//!
//! Five kinds of place, all of them DESIGN.md §3.3/§3.4's standing
//! deviations rather than choices of this task:
//!
//! * **`Nat` is `u64`** (cursors, fuel, de Bruijn indices, binder counts) and
//!   a `List` is a `Vec`.  Lean's truncating subtraction is
//!   `con_ron_core::kernel::expr_ops::sub_nat` wherever the cited arm has no
//!   guard, and a bare `-` wherever it does — con-ron-core's own rule, and
//!   its `sub_nat`'s doc names the same three sites.
//! * **A `List` recursion is a cursor recursion over a `Vec`** (§3.4), so
//!   eleven of the twin's list-shaped walks gain a `…_from` companion.  The
//!   twin has the same split wherever *it* could not write `mapM`
//!   (`readNames`, `substLevelList`) — for the same reason, one layer up.
//! * **`x :: xs` on the way out of a recursion copies** (`cons_eidx`,
//!   `cons_binder`): a `Vec` has no cons.  Where the twin conses *after* a
//!   recursive call that mutates the store — `inst_pis_at_f_go`'s domain —
//!   the order is kept exactly, because interning in a different order gives
//!   the same denotation but different handles, and this port is in lockstep
//!   with the twin at the handle.
//! * **A twin that cannot fail returns its value** (`arena::monad`'s note):
//!   `exprPtrBEq`, `LIdx.hasParam` and `Expr.hasLevelParam` read the derived
//!   column and nothing else.

use crate::arena::handle::{
    e_tag_is_bind, EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_FORALL_E, ETAG_FVAR,
    ETAG_LAM, ETAG_LET_E, ETAG_PROJ,
};
use crate::arena::monad::{
    AState, EIdxNat, abs1_clear, abs1_get, abs1_set, bvar_b_clear, bvar_b_get, bvar_b_set, derived_e, eidx_nat_key, fail, fail_dangling_e, fvar_b_clear, fvar_b_get, fvar_b_set, inst1_clear, inst1_get, inst1_l_clear, inst1_l_get, inst1_l_set, inst1_set, inst_l_clear, inst_l_get, inst_l_set, inst_lp_clear, inst_lp_get, inst_lp_l_get, inst_lp_l_set, inst_lp_ls_get, inst_lp_ls_set, inst_lp_set, intern_e_app, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_fvar, intern_e_lam, intern_e_let_e, intern_e_proj, intern_e_sort, intern_level, intern_levels, lift_clear, lift_get, lift_set, lower_clear, lower_get, lower_set, read_level_m, read_levels_m, read_names_m, intern_e_bind_i, view, view_app, view_bind, view_bind_i, view_bvar, view_fvar_idx, view_fvar_ty, view_let, view_proj,
};
use crate::arena::handle::BMIdx;
use crate::arena::handle::ETAG_CONST;
use crate::arena::monad::{read_level, read_names, view_const, view_ls};
use crate::arena::store::ENodeView;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr_ops::sub_nat;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name::Name;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::{Dup, Eq2};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use crate::ron::hashmap2::HashMap2 as HashMap;
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The fuel-exhaustion messages, one per walk, as the twin has one per walk
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: instantiate1"`, as code points.
const M_FUEL_INST1: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110, 115,
    116, 97, 110, 116, 105, 97, 116, 101, 49,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: instantiateList"`, as code points.
const M_FUEL_INST_LIST: [u32; 31] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110, 115,
    116, 97, 110, 116, 105, 97, 116, 101, 76, 105, 115, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: liftLooseBVars"`, as code points.
const M_FUEL_LIFT: [u32; 30] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 105, 102,
    116, 76, 111, 111, 115, 101, 66, 86, 97, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: abstractRange"`, as code points.
const M_FUEL_ABS_RANGE: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 98, 115, 116,
    114, 97, 99, 116, 82, 97, 110, 103, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: wscopedBGo"`, as code points.
const M_FUEL_WSCOPED_GO: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 115, 99,
    111, 112, 101, 100, 66, 71, 111,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: fvarLeavesGo"`, as code points.
const M_FUEL_FVAR_LEAVES_GO: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 102, 118, 97,
    114, 76, 101, 97, 118, 101, 115, 71, 111,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: leavesSubGo"`, as code points.
const M_FUEL_LEAVES_SUB_GO: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 101, 97,
    118, 101, 115, 83, 117, 98, 71, 111,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: getAppFn"`, as code points.
const M_FUEL_APP_FN: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 103, 101, 116,
    65, 112, 112, 70, 110,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: getAppArgs"`, as code points.
const M_FUEL_APP_ARGS: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 103, 101, 116,
    65, 112, 112, 65, 114, 103, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: piResult"`, as code points.
const M_FUEL_PI_RESULT: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 82,
    101, 115, 117, 108, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: bvarBound"`, as code points.
const M_FUEL_BVAR_BOUND: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 98, 118, 97, 114,
    66, 111, 117, 110, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: fvarRange"`, as code points.
const M_FUEL_FVAR_RANGE: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 102, 118, 97, 114,
    82, 97, 110, 103, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: abstract1"`, as code points.
const M_FUEL_ABS1: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 98, 115, 116,
    114, 97, 99, 116, 49,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: lowerBVars"`, as code points.
const M_FUEL_LOWER: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 111, 119,
    101, 114, 66, 86, 97, 114, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: instantiate1Lift"`, as code points.
const M_FUEL_INST1_LIFT: [u32; 32] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110, 115,
    116, 97, 110, 116, 105, 97, 116, 101, 49, 76, 105, 102, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: instantiateLevelParams"`, as code points.
const M_FUEL_INST_LP: [u32; 38] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110, 115,
    116, 97, 110, 116, 105, 97, 116, 101, 76, 101, 118, 101, 108, 80, 97, 114, 97, 109, 115,
];

// ---------------------------------------------------------------------------
// `List` over a `Vec`: the copying combinators the twin gets from `::` and
// `++` for free (DESIGN.md §3.3's deviation 5, §3.4's no-closure rule)
// ---------------------------------------------------------------------------

/// con-leche: none — `List.take`/`List.append` over a `Vec<EIdx>`
/// The first `k` entries of `xs` appended to `out`.  A handle is a `u32`, so
/// the copy is a word each.
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:186-192 eidxCopyUpto` — the
/// same window copy, `Array.push` for `Vec::push`.
pub fn eidx_copy_upto(xs: &Vec<EIdx>, k: usize, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if i >= k || i >= xs.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(xs[i].dup2());
        eidx_copy_upto(xs, k, i + 1, o)
    }
}

/// con-leche: none — `List.take` over a `Vec<EIdx>`
/// `xs.take k`.
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:202-203 takeEidx` — the same
/// prefix of a push-order vector.
pub fn take_eidx(xs: &Vec<EIdx>, k: usize) -> Vec<EIdx> {
    let n: usize = if k < xs.len() { k } else { xs.len() };
    eidx_copy_upto(xs, k, 0, Vec::with_capacity(n))
}

/// con-leche: none — `List.take` over a `Vec<EIdx>` at a `u64` count, without a `usize` cast
/// `xs.take n` where the count is a machine word of the checker's own
/// arithmetic (a parameter count, a major-premise index): task #61's
/// `kernel::core_k::take_exprs_n` over handles (task #97-P5-Usize).  The
/// obvious `take_eidx(xs, n as usize)` is a *truncating* cast under Aeneas,
/// so on a 32-bit target a count past `u32::MAX` would take a short prefix
/// where the twin's `List.take` takes the whole list.  The count is consumed
/// by the recursion instead of converted: `i` walks the `Vec` and `n` counts
/// down, so no value ever crosses between the two widths.
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:202-203 takeEidx` — the same
/// prefix of a push-order vector.
pub fn take_eidx_n(xs: &Vec<EIdx>, n: u64) -> Vec<EIdx> {
    take_eidx_n_from(xs, n, 0, Vec::new())
}

/// con-leche: none — `List.take` over a `Vec<EIdx>` at a `u64` count
/// The index recursion behind `take_eidx_n`; the accumulator is passed by
/// value and returned (task #6's rule).
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:202-203 takeEidx` — the
/// window copy, one handle per step.
pub fn take_eidx_n_from(xs: &Vec<EIdx>, n: u64, i: usize, out: Vec<EIdx>) -> Vec<EIdx> {
    if n == 0 || i >= xs.len() {
        out
    } else {
        let mut o: Vec<EIdx> = out;
        o.push(xs[i].dup2());
        take_eidx_n_from(xs, n - 1, i + 1, o)
    }
}

/// con-leche: none — `x :: xs` over a `Vec<EIdx>`
/// Lean conses in `O(1)` and shares the tail; a `Vec` has no cons, so the
/// tail is copied.  Every call site is a telescope arity, not a term size.
///
/// **Not the substitution accumulators any more** (task #97-P6-15).  They
/// consed once per binder and each cons copied the whole tail, so a telescope
/// of `n` binders paid `n` allocations and `n²/2` handle copies —
/// `eidx_copy_upto` was 4.3 % of `Init`.  Those accumulators are now built in
/// PUSH order by `Vec::push` on an OWNED vector and read from the end
/// (`last_eidx`, `instantiate_list`'s `bvar` arm); what is left here is the
/// lists that are genuinely built on the way OUT of a recursion, where the
/// answer is a cons of a value the recursion produced.
pub fn cons_eidx(a: &EIdx, xs: &Vec<EIdx>) -> Vec<EIdx> {
    let mut out: Vec<EIdx> = Vec::with_capacity(xs.len() + 1);
    out.push(a.dup2());
    eidx_copy_upto(xs, xs.len(), 0, out)
}

/// con-leche: none — `xs ++ [y]` on a `Vec<EIdx>`, at a BORROWED `xs`
/// Lean twin: `proof/ConRon/Arena/Core.lean:1350-1367 structEtaProjCerts` — the
/// cited `targs ++ [b]` (task #97-P6-13; moved here from `arena::core` by
/// task #97-P6-15, which needs it beside `cons_eidx`).
///
/// `snoc_eidx(eidx_vec_dup(targs), b)` is what the call sites wrote, and it
/// is TWO allocations and `2n` handle copies: `eidx_vec_dup` allocates
/// exactly `n` and fills it, and the `push` then overflows that capacity and
/// re-allocates and copies again.  Sized once, it is one allocation and
/// `n + 1` copies.  A capacity, so the refinement absorbs it (DESIGN.md §3.2).
///
/// It is also the push-order accumulator's step at the two sites that cannot
/// own their accumulator — `inst_pis_at_f_go` and `inst_lams_at_f_go` read it
/// again AFTER the recursive call — which task #97-P6-9 measured at 260 calls
/// and 0 interns on the whole of `Init`.
pub fn snoc_eidx_of(xs: &Vec<EIdx>, y: &EIdx) -> Vec<EIdx> {
    let out: Vec<EIdx> = Vec::with_capacity(xs.len() + 1);
    let mut out = eidx_copy_upto(xs, xs.len(), 0, out);
    out.push(y.dup2());
    out
}

/// con-leche: none — `List.take` over a PUSH-ORDER `Vec<EIdx>`
/// The last `k` entries of `xs`, in `xs`' own order (task #97-P6-15).
///
/// A substitution vector is built by `Vec::push` and read from the END — its
/// entry for `bvar (d + j)` is `xs[xs.len() - 1 - j]` — so the twin's
/// `vs.take k`, the first `k` of the list, is this SUFFIX of the vector.
/// `take_eidx` is the same function on a vector that is in list order, and
/// both are `eidx_copy_upto` over a window.
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:205-208 lastEidx` — the same
/// suffix of a push-order vector.
pub fn last_eidx(xs: &Vec<EIdx>, k: usize) -> Vec<EIdx> {
    let n: usize = if k < xs.len() { xs.len() - k } else { 0 };
    eidx_copy_upto(xs, xs.len(), n, Vec::with_capacity(xs.len() - n))
}

/// con-leche: none — `==` on `List EIdx`, elementwise
/// The comparison `recRulePlain` makes: `args.take want.length == want`.  A
/// `List.take` shorter than `want` cannot be equal to it, which is the length
/// test; the elements are handles, so `==` is word equality (exactness, task
/// #97a's `denoteE_inj`).
pub fn eidx_take_beq(args: &Vec<EIdx>, want: &Vec<EIdx>) -> bool {
    if args.len() < want.len() {
        false
    } else {
        eidx_prefix_beq(args, want, 0)
    }
}

/// con-leche: none — `==` on `List EIdx`, elementwise
/// The cursor recursion behind `eidx_take_beq`.
pub fn eidx_prefix_beq(args: &Vec<EIdx>, want: &Vec<EIdx>, i: usize) -> bool {
    if i >= want.len() {
        true
    } else if args[i].eq2(&want[i]) {
        eidx_prefix_beq(args, want, i + 1)
    } else {
        false
    }
}

/// con-leche: none — `(ty, m) :: xs` over a `Vec<(EIdx, BinderMeta)>`
/// The `stripLams`/`stripPis` telescope's cons; `BinderMeta` is copied by
/// `binder_meta_dup` (a `PropWhen` reference bump on its rare arms).
pub fn cons_binder(
    ty: &EIdx,
    m: &BinderMeta,
    xs: &Vec<(EIdx, BinderMeta)>,
) -> Vec<(EIdx, BinderMeta)> {
    let mut out: Vec<(EIdx, BinderMeta)> = Vec::new();
    out.push((ty.dup2(), expr::binder_meta_dup(m)));
    binder_copy_from(xs, 0, out)
}

/// con-leche: none — `List.append` over a `Vec<(EIdx, BinderMeta)>`
/// The cursor recursion behind `cons_binder`.
pub fn binder_copy_from(
    xs: &Vec<(EIdx, BinderMeta)>,
    i: usize,
    out: Vec<(EIdx, BinderMeta)>,
) -> Vec<(EIdx, BinderMeta)> {
    if i >= xs.len() {
        out
    } else {
        let mut o: Vec<(EIdx, BinderMeta)> = out;
        o.push((xs[i].0.dup2(), expr::binder_meta_dup(&xs[i].1)));
        binder_copy_from(xs, i + 1, o)
    }
}

// ---------------------------------------------------------------------------
// The UPWARD cutoff of a substituting walk (task #97-P6-5, lever 2)
// ---------------------------------------------------------------------------

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:139-141 internRebuiltFVar` —
/// `internRebuiltFVar`, the `fvar` arm of `intern_rebuilt`: the same cutoff,
/// over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_fvar(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    idx: u64,
    ty: EIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_fvar(pers, st, idx, ty)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:142-144 internRebuiltSort` —
/// `internRebuiltSort`, the `sort` arm of `intern_rebuilt`: the same cutoff,
/// over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_sort(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    u: LIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_sort(pers, st, u)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:145-147 internRebuiltConst` —
/// `internRebuiltConst`, the `const` arm of `intern_rebuilt`: the same cutoff,
/// over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_const(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    n: NIdx,
    us: LsIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_const(pers, st, n, us)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:148-150 internRebuiltApp` —
/// `internRebuiltApp`, the `app` arm of `intern_rebuilt`: the same cutoff, over
/// the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_app(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    f: EIdx,
    a: EIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_app(pers, st, f, a)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:151-154 internRebuiltLam` —
/// `internRebuiltLam`, the `lam` arm of `intern_rebuilt`: the same cutoff, over
/// the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_lam(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    ty: EIdx,
    body: EIdx,
    m: BinderMeta,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_lam(pers, st, ty, body, m)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:155-158 internRebuiltForallE` —
/// `internRebuiltForallE`, the `forall_e` arm of `intern_rebuilt`: the same
/// cutoff, over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_forall_e(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    ty: EIdx,
    body: EIdx,
    m: BinderMeta,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_forall_e(pers, st, ty, body, m)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:159-161 internRebuiltLetE` —
/// `internRebuiltLetE`, the `let_e` arm of `intern_rebuilt`: the same cutoff,
/// over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_let_e(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    ty: EIdx,
    val: EIdx,
    body: EIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_let_e(pers, st, ty, val, body)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:162-164 internRebuiltProj` —
/// `internRebuiltProj`, the `proj` arm of `intern_rebuilt`: the same cutoff,
/// over the arm's FIELDS.
///
/// `intern_rebuilt` takes an `ENodeView`, so the twenty-three substituting
/// walks that call it built one per rebuilt node and `EStore::intern`
/// dispatched on its tag again — the two things task #97-P6-15's lever 1 took
/// out of the other 276 intern sites.  These are the hottest of them all.
pub fn intern_rebuilt_proj(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    n: NIdx,
    i: u64,
    e: EIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_proj(pers, st, n, i, e)
    }
}

/// con-leche: none — `internE` with task #97-P6-5's upward cutoff
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:166-173 internRebuiltBindI` —
/// `internRebuiltBindI`, `internRebuiltBind` at a binder datum the walk is
/// CARRYING ACROSS rather than changing.
///
/// A substituting walk takes a binder apart and puts it back with the same
/// datum; since task #97-P6-16 the datum is interned and the walk carries its
/// `BMIdx`, so the round trip is a register move where it used to be a
/// `binder_meta_dup` out of the record and a cons probe of the datum back in.
pub fn intern_rebuilt_bind_i(
    pers: &PersTier,
    st: &mut AState,
    h: &EIdx,
    same: bool,
    tag: u32,
    ty: EIdx,
    body: EIdx,
    m: BMIdx,
) -> Result<EIdx, CheckError> {
    if same {
        Ok(h.dup2())
    } else {
        intern_e_bind_i(pers, st, tag, ty, body, m)
    }
}

// ---------------------------------------------------------------------------
// `instantiate1` — `ExprOps.lean:29-45`, `:80-116`, `:182-184`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:259-285 instantiate1Go` —
/// replace `bvar d` by `v`, lowering loose `bvar`s above `d` by one.  The
/// derived-word cutoff comes first (`bvarB <= d`, read off the packed word in
/// `O(1)`); the five leaf kinds answer without touching the memo; everything
/// else probes the memo, runs the body one level down and inserts.
///
/// `else .bvar i` is `Ok(h.dup2())`: the node is already interned and
/// `denoteE` is injective, so rebuilding it yields the same handle.
pub fn instantiate1_go(
    pers: &PersTier,
    st: &mut AState,
    v: &EIdx,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST1)))
    } else {
        let der: u64 = derived_e(pers, st, h);
        let b: u64 = expr::bvar_of_data(der);
        if b < expr::sat_range() && b <= d {
            Ok(h.dup2())
        } else {
            let t: u32 = h.tag();
            if t == ETAG_APP {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst1_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match view_app(pers, st, h) {
                        None => fail_dangling_e(),
                        Some(p) => {
                            let f: EIdx = p.0;
                            let a: EIdx = p.1;
                            match instantiate1_go(pers, st, v, fuel - 1, &f, d) {
                                Err(e) => Err(e),
                                Ok(f2) => match instantiate1_go(pers, st, v, fuel - 1, &a, d) {
                                    Err(e) => Err(e),
                                    Ok(a2) => match intern_e_app(pers, st, f2, a2) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst1_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                },
                            }
                        }
                    },
                }
            } else if e_tag_is_bind(t) {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst1_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match view_bind_i(pers, st, h) {
                        None => fail_dangling_e(),
                        Some(p) => {
                            let ty: EIdx = p.0;
                            let body: EIdx = p.1;
                            let m: BMIdx = p.2;
                            match instantiate1_go(pers, st, v, fuel - 1, &ty, d) {
                                Err(e) => Err(e),
                                Ok(t2) => {
                                    match instantiate1_go(pers, st, v, fuel - 1, &body, d + 1) {
                                        Err(e) => Err(e),
                                        Ok(b2) => {
                                            match intern_e_bind_i(pers, st, t, t2, b2, m) {
                                                Err(e) => Err(e),
                                                Ok(r) => {
                                                    inst1_set(st, k, &r);
                                                    Ok(r)
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    },
                }
            } else if t == ETAG_BVAR {
                match view_bvar(pers, st, h) {
                    None => fail_dangling_e(),
                    Some(i) => {
                        if i == d {
                            Ok(v.dup2())
                        } else if i > d {
                            intern_e_bvar(pers, st, i - 1)
                        } else {
                            Ok(h.dup2())
                        }
                    }
                }
            } else if t == ETAG_LET_E {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst1_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match view_let(pers, st, h) {
                        None => fail_dangling_e(),
                        Some(p) => {
                            let ty: EIdx = p.0;
                            let val: EIdx = p.1;
                            let body: EIdx = p.2;
                            match instantiate1_go(pers, st, v, fuel - 1, &ty, d) {
                                Err(e) => Err(e),
                                Ok(t2) => match instantiate1_go(pers, st, v, fuel - 1, &val, d) {
                                    Err(e) => Err(e),
                                    Ok(w) => {
                                        match instantiate1_go(pers, st, v, fuel - 1, &body, d + 1) {
                                            Err(e) => Err(e),
                                            Ok(b2) => {
                                                match intern_e_let_e(pers, st, t2, w, b2)
                                                {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        inst1_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                    },
                }
            } else if t == ETAG_PROJ {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst1_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match view_proj(pers, st, h) {
                        None => fail_dangling_e(),
                        Some(p) => {
                            let n: NIdx = p.0;
                            let i: u64 = p.1;
                            let sub: EIdx = p.2;
                            match instantiate1_go(pers, st, v, fuel - 1, &sub, d) {
                                Err(e) => Err(e),
                                Ok(u) => match intern_e_proj(pers, st, n, i, u) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst1_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            }
                        }
                    },
                }
            } else {
                Ok(h.dup2())
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:385-392 instantiate1Fast` — the
/// top-level entry: `(instantiate1Go v {} e d).1`, i.e. the memo is fresh
/// before and dropped after, because it depends on the substituted term.
pub fn instantiate1_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    v: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst1_clear(st);
    match instantiate1_go(pers, st, v, fuel, e, d) {
        Err(er) => Err(er),
        Ok(r) => {
            inst1_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `instantiateList` — `ExprOps.lean:191-235`, `:267-303`, `:371-373`
// ---------------------------------------------------------------------------

/// con-leche: none — a derived-word cutoff con-leche does not have (task #97f)
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:402-428 instantiateList` (and
/// `:264-267 instantiateListGo`, `:343-346 liftLooseBVarsGo`) — the cutoff
/// `bvarBRaw < satRange && bvarBRaw ≤ k`.
///
/// **Denotation-preserving**, by the two elementary lemmas the twin's module
/// note states for P3: `looseBVarsBounded d e → instantiateList e vs d = e`
/// and `looseBVarsBounded c e → liftLooseBVars e c amount = e` (the `.bvar j`
/// clause is the only non-congruence, and `j < k` takes the unchanged branch).
/// `looseBVarsBounded k e` is `e.bvarBound ≤ k`, and the store's derived word
/// is con-leche's own `Expr.data`, so `bvarBRaw < satRange` is exactly the side
/// condition under which the packed field IS `e.bvarBound` — the same guard
/// `instantiate1_go` carries.
///
/// P2f's gate is what forced it: `tests/e2e/proj_share.ndjson` does not finish
/// without these two cutoffs, with 18 % of its cycles in `instantiateList`.
#[inline(always)]
pub fn inst_list_cutoff(pers: &PersTier, st: &AState, h: &EIdx, k: u64) -> bool {
    let der: u64 = derived_e(pers, st, h);
    let b: u64 = expr::bvar_of_data(der);
    b < expr::sat_range() && b <= k
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:402-428 instantiateList` — the
/// unmemoized bulk instantiation.  con-leche's termination measure is
/// `(vs.length, sizeOf e)`; the single fuel counter decreases on both kinds of
/// recursive call, which is that order flattened.  **Two twins, not one**:
/// `instantiate_list_go`'s `bvar` arm calls this one, because that arm
/// recurses into the replacement with a *shorter* list and the memo is keyed
/// for the outer one.
///
/// **`vs` is in PUSH order** (task #97-P6-15, the maintainer's ruling): the
/// callers build their substitution accumulator with `Vec::push` on an OWNED
/// vector — `O(1)` amortised — instead of consing a fresh `Vec` per binder,
/// which was `n` allocations and `n^2/2` handle copies over a telescope
/// (`eidx_copy_upto`, 4.3 % of `Init`).  The LIST this function is about is
/// unchanged; it is read from the end — `vs[vs.len() - 1 - j]` for the twin's
/// `vs[j]`, `last_eidx k` for `vs.take k`.  The twin's clause changes with
/// it: those accumulators become an `Array` built with `Array.push`, whose
/// denotation is the reverse of the list the `::` chain built.
pub fn instantiate_list(
    pers: &PersTier,
    st: &mut AState,
    vs: &Vec<EIdx>,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LIST)))
    } else if inst_list_cutoff(pers, st, h, d) {
        Ok(h.dup2())
    } else {
        let t: u32 = h.tag();
        if t == ETAG_APP {
            match view_app(pers, st, h) {
                None => fail_dangling_e(),
                Some(p) => {
                    let f: EIdx = p.0;
                    let a: EIdx = p.1;
                    match instantiate_list(pers, st, vs, fuel - 1, &f, d) {
                        Err(e) => Err(e),
                        Ok(f2) => match instantiate_list(pers, st, vs, fuel - 1, &a, d) {
                            Err(e) => Err(e),
                            Ok(a2) => intern_e_app(pers, st, f2, a2),
                        },
                    }
                }
            }
        } else if e_tag_is_bind(t) {
            match view_bind_i(pers, st, h) {
                None => fail_dangling_e(),
                Some(p) => {
                    let ty: EIdx = p.0;
                    let body: EIdx = p.1;
                    let m: BMIdx = p.2;
                    match instantiate_list(pers, st, vs, fuel - 1, &ty, d) {
                        Err(e) => Err(e),
                        Ok(t2) => match instantiate_list(pers, st, vs, fuel - 1, &body, d + 1) {
                            Err(e) => Err(e),
                            Ok(b) => intern_e_bind_i(pers, st, t, t2, b, m),
                        },
                    }
                }
            }
        } else if t == ETAG_LET_E {
            match view_let(pers, st, h) {
                None => fail_dangling_e(),
                Some(p) => {
                    let ty: EIdx = p.0;
                    let val: EIdx = p.1;
                    let body: EIdx = p.2;
                    match instantiate_list(pers, st, vs, fuel - 1, &ty, d) {
                        Err(e) => Err(e),
                        Ok(t2) => match instantiate_list(pers, st, vs, fuel - 1, &val, d) {
                            Err(e) => Err(e),
                            Ok(w) => match instantiate_list(pers, st, vs, fuel - 1, &body, d + 1) {
                                Err(e) => Err(e),
                                Ok(b) => intern_e_let_e(pers, st, t2, w, b),
                            },
                        },
                    }
                }
            }
        } else if t == ETAG_PROJ {
            match view_proj(pers, st, h) {
                None => fail_dangling_e(),
                Some(p) => {
                    let n: NIdx = p.0;
                    let i: u64 = p.1;
                    let sub: EIdx = p.2;
                    match instantiate_list(pers, st, vs, fuel - 1, &sub, d) {
                        Err(e) => Err(e),
                        Ok(u) => intern_e_proj(pers, st, n, i, u),
                    }
                }
            }
        } else if t == ETAG_BVAR {
            match view_bvar(pers, st, h) {
                None => fail_dangling_e(),
                Some(j) => {
                    if j < d {
                        Ok(h.dup2())
                    } else {
                        let n: u64 = vs.len() as u64;
                        if j - d < n {
                            let i: usize = (j - d) as usize;
                            // **`vs` is in PUSH order** (task #97-P6-15): the
                            // accumulator is built by `Vec::push`, so the
                            // twin's `vs[j - d]` — the innermost binder's
                            // argument first — is this vector's entry `j - d`
                            // FROM THE END.  The two are the same list; only
                            // the direction the `Vec` grows changed.
                            let vi: EIdx = vs[vs.len() - 1 - i].dup2();
                            // **The cutoff hoisted over the prefix copy** (task
                            // #97-P6-9).  The recursion into the replacement is
                            // con-leche's own `instantiateList vs[j-d]
                            // (vs.take (j-d)) d`, and its own note says it "is the
                            // identity on `bvar`-closed replacements (every checker
                            // call site)" — which is exactly what `inst_list_cutoff`
                            // decides, in O(1), off the handle's derived word.
                            // Testing it BEFORE `take_eidx` is the same value by
                            // the cutoff's own equation (`looseBVarsBounded d e →
                            // instantiateList e vs d = e`, for every `vs`), and it
                            // takes the prefix copy off the batched β path, which
                            // hits this clause once per bound variable of every
                            // peeled group.
                            if inst_list_cutoff(pers, st, &vi, d) {
                                Ok(vi)
                            } else {
                                let pre: Vec<EIdx> = last_eidx(vs, i);
                                instantiate_list(pers, st, &pre, fuel - 1, &vi, d)
                            }
                        } else {
                            intern_e_bvar(pers, st, j - n)
                        }
                    }
                }
            }
        } else {
            Ok(h.dup2())
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:532-555 instantiateListGo` —
/// the memoized bulk instantiation.  The `bvar` arm delegates to the pure walk
/// above, exactly as con-leche's does.
pub fn instantiate_list_go(
    pers: &PersTier,
    st: &mut AState,
    vs: &Vec<EIdx>,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LIST)))
    } else if inst_list_cutoff(pers, st, h, d) {
        Ok(h.dup2())
    } else {
        let t: u32 = h.tag();
        if t == ETAG_APP {
            let k: EIdxNat = eidx_nat_key(h, d);
            match inst_l_get(st, &k) {
                Some(r) => Ok(r),
                None => match view_app(pers, st, h) {
                    None => fail_dangling_e(),
                    Some(p) => {
                        let f: EIdx = p.0;
                        let a: EIdx = p.1;
                        match instantiate_list_go(pers, st, vs, fuel - 1, &f, d) {
                            Err(e) => Err(e),
                            Ok(f2) => match instantiate_list_go(pers, st, vs, fuel - 1, &a, d) {
                                Err(e) => Err(e),
                                Ok(a2) => match intern_e_app(pers, st, f2, a2) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst_l_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        }
                    }
                },
            }
        } else if e_tag_is_bind(t) {
            let k: EIdxNat = eidx_nat_key(h, d);
            match inst_l_get(st, &k) {
                Some(r) => Ok(r),
                None => match view_bind_i(pers, st, h) {
                    None => fail_dangling_e(),
                    Some(p) => {
                        let ty: EIdx = p.0;
                        let body: EIdx = p.1;
                        let m: BMIdx = p.2;
                        match instantiate_list_go(pers, st, vs, fuel - 1, &ty, d) {
                            Err(e) => Err(e),
                            Ok(t2) => {
                                match instantiate_list_go(pers, st, vs, fuel - 1, &body, d + 1) {
                                    Err(e) => Err(e),
                                    Ok(b) => {
                                        match intern_e_bind_i(pers, st, t, t2, b, m) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                inst_l_set(st, k, &r);
                                                Ok(r)
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            }
        } else if t == ETAG_BVAR {
            instantiate_list(pers, st, vs, fuel - 1, h, d)
        } else if t == ETAG_LET_E {
            let k: EIdxNat = eidx_nat_key(h, d);
            match inst_l_get(st, &k) {
                Some(r) => Ok(r),
                None => match view_let(pers, st, h) {
                    None => fail_dangling_e(),
                    Some(p) => {
                        let ty: EIdx = p.0;
                        let val: EIdx = p.1;
                        let body: EIdx = p.2;
                        match instantiate_list_go(pers, st, vs, fuel - 1, &ty, d) {
                            Err(e) => Err(e),
                            Ok(t2) => match instantiate_list_go(pers, st, vs, fuel - 1, &val, d) {
                                Err(e) => Err(e),
                                Ok(w) => {
                                    match instantiate_list_go(pers, st, vs, fuel - 1, &body, d + 1)
                                    {
                                        Err(e) => Err(e),
                                        Ok(b) => {
                                            match intern_e_let_e(pers, st, t2, w, b) {
                                                Err(e) => Err(e),
                                                Ok(r) => {
                                                    inst_l_set(st, k, &r);
                                                    Ok(r)
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    }
                },
            }
        } else if t == ETAG_PROJ {
            let k: EIdxNat = eidx_nat_key(h, d);
            match inst_l_get(st, &k) {
                Some(r) => Ok(r),
                None => match view_proj(pers, st, h) {
                    None => fail_dangling_e(),
                    Some(p) => {
                        let n: NIdx = p.0;
                        let i: u64 = p.1;
                        let sub: EIdx = p.2;
                        match instantiate_list_go(pers, st, vs, fuel - 1, &sub, d) {
                            Err(e) => Err(e),
                            Ok(u) => match intern_e_proj(pers, st, n, i, u) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_l_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        }
                    }
                },
            }
        } else {
            Ok(h.dup2())
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:650-657 instantiateListFast` —
/// the top-level entry.
pub fn instantiate_list_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    vs: &Vec<EIdx>,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst_l_clear(st);
    match instantiate_list_go(pers, st, vs, fuel, e, d) {
        Err(er) => Err(er),
        Ok(r) => {
            inst_l_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `liftLooseBVars` — `ExprOps.lean:380-400`, `:430-466`, `:532-534`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:458-478 liftLooseBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:508-544 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:663-696 liftLooseBVarsGo` —
/// bump every loose bound variable `>= cutoff` by `amount`.
pub fn lift_loose_bvars_go(
    pers: &PersTier,
    st: &mut AState,
    amount: u64,
    fuel: u64,
    h: &EIdx,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LIFT)))
    } else if inst_list_cutoff(pers, st, h, c) {
        Ok(h.dup2())
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(i)) => {
                if i >= c {
                    intern_e_bvar(pers, st, i + amount)
                } else {
                    Ok(h.dup2())
                }
            }
            Ok(ENodeView::FVar(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::App(a, b)) => {
                let k: EIdxNat = eidx_nat_key(h, c);
                match lift_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &a, c) {
                        Err(e) => Err(e),
                        Ok(a2) => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &b, c) {
                            Err(e) => Err(e),
                            Ok(b2) => match intern_e_app(pers, st, a2, b2) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    lift_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Lam(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, c);
                match lift_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &body, c + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e_lam(pers, st, t, b, m) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    lift_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::ForallE(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, c);
                match lift_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &body, c + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e_forall_e(pers, st, t, b, m) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    lift_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                let k: EIdxNat = eidx_nat_key(h, c);
                match lift_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &val, c) {
                            Err(e) => Err(e),
                            Ok(w) => {
                                match lift_loose_bvars_go(pers, st, amount, fuel - 1, &body, c + 1) {
                                    Err(e) => Err(e),
                                    Ok(b) => match intern_e_let_e(pers, st, t, w, b) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            lift_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                }
                            }
                        },
                    },
                }
            }
            Ok(ENodeView::Proj(n, i, sub)) => {
                let k: EIdxNat = eidx_nat_key(h, c);
                match lift_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match lift_loose_bvars_go(pers, st, amount, fuel - 1, &sub, c) {
                        Err(e) => Err(e),
                        Ok(u) => match intern_e_proj(pers, st, n, i, u) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                lift_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:610-612 liftLooseBVarsFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:797-803 liftLooseBVarsFast` —
/// the top-level entry.
pub fn lift_loose_bvars_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    amount: u64,
    c: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    lift_clear(st);
    match lift_loose_bvars_go(pers, st, amount, fuel, e, c) {
        Err(er) => Err(er),
        Ok(r) => {
            lift_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// The measures and the scope predicates
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The scope queries, MEMOIZED (`ExprOps.lean:636-795`, task #97g item 5)
// ---------------------------------------------------------------------------
//
// The two walks above (`fvar_leaves`, `wscoped_b`) and `arena::core`'s
// `fvar_leaves_subset` are `Kernel/ExprOps.lean`'s, and over an arena they are
// the wrong ones: con-leche runs them on `Expr` TREES, where a walk is linear
// in the term; (B) and (C) run them on a hash-consed DAG, where an unmemoized
// walk is linear in the term's *unfolding* — which is what hash-consing exists
// to avoid.  con-leche's EXECUTED tier knows it and carries `wscopedBGoC`
// ("one memoized DAG walk"), `fvarLeavesGoC` (a `seen` set) and `leavesSubGo`
// (its task #86's leaf guard, which never builds the fabrication's leaf list
// at all).  Measured by task #97g on `core.ndjson`'s first 27 920
// declarations: the unmemoized `fabScopeOk` was **43.9 % of the cycles**, and
// the three memoized walks took the prefix from 3 034 G instructions to 866 G.
//
// Each memo is threaded as an argument-and-result pair (a moved
// `ron::HashMap` returned) rather than put in `Memos`, which is con-leche's
// own spelling and `frontend::proj_rec`'s for its `seen` set: the tables are
// per-CALL and two of the three depend on data that is not in the key
// (`leaves_sub_go`'s base list), so a state-carried table would need a clear
// at every entry anyway.
//
// The `fvar_b == 0` short-circuit at the head of each is con-leche's, and it
// reads the RAW packed field: on the saturated branch the field is
// `sat_range() != 0`, so the test does not fire and the walk proceeds — no
// recomputation, and no `&mut` state (these three take `&AState`).
//
// WHERE THESE CITATIONS POINT since con-leche `78ded4b6` (task #97-catchup).
// Upstream's tasks #313–#319 rewrote every traversal memo in its CACHED tier:
// one walk became three declarations — `<name>P`, the memo-free plain descent
// that is the specification; `enter<X>P`, the child step (cutoff, compound
// test, `withExclusive` read); and `<name>XP`, the walk, which carries its own
// proof over an ADDRESS key.  `wscopedBGoC` is now `wscopedBXP` and
// `leavesSubGo` is now `leavesSubXP`, and that is the whole of what the bump
// costs these walks: NO ARM CHANGED, compared clause for clause against
// upstream's new `wscopedBP` / `leavesSubP`, and the cutoff upstream moved out
// into `wscopedBC` / `leavesSubC` is still made at the head of every recursive
// call here, exactly as `enterWSP` / `enterLSub` make it.
//
// And nothing of #319's `withExclusive` gate is owed HERE.  That idiom asks
// whether an `Expr` node's reference count is one and skips the memo when it
// is; the arena has no reference counts — a term is a `u32` handle into a
// per-constructor `Vec`, shared by construction — so the question has no
// answer in this crate.  The `Expr` tier had one — `ron::node::is_exclusive`,
// a hole read by `expr::beq_memoise` (task #98) — and task #97-SWAP-2 retired
// it with the tagged handle, so no reference count is read anywhere in the
// crate now; the memo policy of DESIGN.md §8.3 is the arena's own and
// unchanged.

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1021-1080 wscopedBXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:961-989 wscopedBGo` — probe the
/// scope memo (extraction rule 5: a `HashMap::get` match that produces a value
/// is its own function).
pub fn wscoped_memo_get(memo: &HashMap<EIdxNat, bool>, k: &EIdxNat) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1021-1080 wscopedBXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:961-989 wscopedBGo` — the cited
/// `memo'.insert (h, d) r`, on the owned table.
pub fn wscoped_memo_set(
    memo: HashMap<EIdxNat, bool>,
    k: EIdxNat,
    r: bool,
) -> HashMap<EIdxNat, bool> {
    let mut m: HashMap<EIdxNat, bool> = memo;
    m.insert(k, r);
    m
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1021-1080 wscopedBXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:961-989 wscopedBGo` — the
/// memoized scope walk.  `fvar` annotations are descended (at the annotation's
/// own index, not `d`), so the cached fvar range does not decide it and the
/// memo key carries `d`.
pub fn wscoped_b_go(
    pers: &PersTier,
    st: &AState,
    memo: HashMap<EIdxNat, bool>,
    fuel: u64,
    d: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WSCOPED_GO)))
    } else if expr::fvar_of_data(derived_e(pers, st, h)) == 0 {
        Ok((true, memo))
    } else {
        let k: EIdxNat = eidx_nat_key(h, d);
        match wscoped_memo_get(&memo, &k) {
            Some(r) => Ok((r, memo)),
            None => match view(pers, st, h) {
                Err(e) => Err(e),
                Ok(v) => match wscoped_b_node(pers, st, memo, fuel - 1, d, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => Ok((r, wscoped_memo_set(m, k, r))),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1021-1080 wscopedBXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:961-989 wscopedBGo` — the arms,
/// past the probe.  Split off so the `view`'s loans are dead at the memo's
/// join (extraction rule 5, `frontend::proj_rec`'s arrangement).
pub fn wscoped_b_node(
    pers: &PersTier,
    st: &AState,
    memo: HashMap<EIdxNat, bool>,
    fuel: u64,
    d: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match v {
        ENodeView::FVar(idx, ty) => {
            if idx < d {
                wscoped_b_go(pers, st, memo, fuel, idx, &ty)
            } else {
                Ok((false, memo))
            }
        }
        ENodeView::App(f, a) => wscoped_b_two(pers, st, memo, fuel, d, &f, &a),
        ENodeView::Lam(ty, body, _) => wscoped_b_two(pers, st, memo, fuel, d, &ty, &body),
        ENodeView::ForallE(ty, body, _) => wscoped_b_two(pers, st, memo, fuel, d, &ty, &body),
        ENodeView::LetE(ty, val, body) => match wscoped_b_go(pers, st, memo, fuel, d, &ty) {
            Err(e) => Err(e),
            Ok((false, m)) => Ok((false, m)),
            Ok((true, m)) => wscoped_b_two(pers, st, m, fuel, d, &val, &body),
        },
        ENodeView::Proj(_, _, sub) => wscoped_b_go(pers, st, memo, fuel, d, &sub),
        ENodeView::BVar(_) => Ok((true, memo)),
        ENodeView::Sort(_) => Ok((true, memo)),
        ENodeView::Const(_, _) => Ok((true, memo)),
        ENodeView::Lit(_) => Ok((true, memo)),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1021-1080 wscopedBXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:961-989 wscopedBGo` — the
/// two-child arms, whose `if rf then … else pure (false, memo)` is the cited
/// short-circuit.
pub fn wscoped_b_two(
    pers: &PersTier,
    st: &AState,
    memo: HashMap<EIdxNat, bool>,
    fuel: u64,
    d: u64,
    x: &EIdx,
    y: &EIdx,
) -> Result<(bool, HashMap<EIdxNat, bool>), CheckError> {
    match wscoped_b_go(pers, st, memo, fuel, d, x) {
        Err(e) => Err(e),
        Ok((false, m)) => Ok((false, m)),
        Ok((true, m)) => wscoped_b_go(pers, st, m, fuel, d, y),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1082-1087 wscopedBC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1051-1055 wscopedBFast` — the
/// executed `wscoped_b`: one memoized DAG walk from the empty memo.
pub fn wscoped_b_fast(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    d: u64,
    h: &EIdx,
) -> Result<bool, CheckError>  {
    let memo: HashMap<EIdxNat, bool> = HashMap::new();
    match wscoped_b_go(pers, st, memo, fuel, d, h) {
        Err(e) => Err(e),
        Ok(p) => Ok(p.0),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1122-1144 fvarLeavesGoC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1059-1086 fvarLeavesGo` — probe the
/// `seen` set (extraction rule 5).
pub fn fvl_seen(seen: &HashMap<EIdx, bool>, h: &EIdx) -> bool {
    match seen.get(h) {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1122-1144 fvarLeavesGoC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1059-1086 fvarLeavesGo` — the cited
/// `seen.insert h ()`, on the owned table.
pub fn fvl_record(seen: HashMap<EIdx, bool>, h: &EIdx) -> HashMap<EIdx, bool> {
    let mut m: HashMap<EIdx, bool> = seen;
    m.insert(h.dup2(), true);
    m
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1122-1144 fvarLeavesGoC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1059-1086 fvarLeavesGo` — the
/// reachable `fvar` leaves, accumulated with a `seen` set so a shared subterm
/// is walked once.
///
/// Deviation: the twin conses `(idx, ty)` onto its accumulator and this pushes
/// onto the `Vec`, so the two lists are each other's reverse.  The result is
/// used only as a membership base (`leaf_mem` below is its only reader), and a
/// `Vec` has no cons — the copying combinators `fvl_append`/`cons_eidx` would
/// make the accumulation quadratic for nothing.
pub fn fvar_leaves_go(
    pers: &PersTier,
    st: &AState,
    acc: Vec<(u64, EIdx)>,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(Vec<(u64, EIdx)>, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_FVAR_LEAVES_GO)))
    } else if expr::fvar_of_data(derived_e(pers, st, h)) == 0 {
        Ok((acc, seen))
    } else if fvl_seen(&seen, h) {
        Ok((acc, seen))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(v) => fvar_leaves_node(pers, st, acc, fvl_record(seen, h), fuel - 1, v),
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1122-1144 fvarLeavesGoC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1059-1086 fvarLeavesGo` — the
/// arms, past the probe and the `seen` insert (extraction rule 5).
pub fn fvar_leaves_node(
    pers: &PersTier,
    st: &AState,
    acc: Vec<(u64, EIdx)>,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(Vec<(u64, EIdx)>, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(idx, ty) => {
            let mut acc2 = acc;
            acc2.push((idx, ty.dup2()));
            fvar_leaves_go(pers, st, acc2, seen, fuel, &ty)
        }
        ENodeView::App(f, a) => fvar_leaves_two(pers, st, acc, seen, fuel, &f, &a),
        ENodeView::Lam(ty, body, _) => fvar_leaves_two(pers, st, acc, seen, fuel, &ty, &body),
        ENodeView::ForallE(ty, body, _) => fvar_leaves_two(pers, st, acc, seen, fuel, &ty, &body),
        ENodeView::LetE(ty, val, body) => match fvar_leaves_go(pers, st, acc, seen, fuel, &ty) {
            Err(e) => Err(e),
            Ok((a2, s2)) => fvar_leaves_two(pers, st, a2, s2, fuel, &val, &body),
        },
        ENodeView::Proj(_, _, sub) => fvar_leaves_go(pers, st, acc, seen, fuel, &sub),
        ENodeView::BVar(_) => Ok((acc, seen)),
        ENodeView::Sort(_) => Ok((acc, seen)),
        ENodeView::Const(_, _) => Ok((acc, seen)),
        ENodeView::Lit(_) => Ok((acc, seen)),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1122-1144 fvarLeavesGoC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1059-1086 fvarLeavesGo` — the
/// two-child arms, one `let (acc, seen) ←` pair in the twin.
pub fn fvar_leaves_two(
    pers: &PersTier,
    st: &AState,
    acc: Vec<(u64, EIdx)>,
    seen: HashMap<EIdx, bool>,
    fuel: u64,
    x: &EIdx,
    y: &EIdx,
) -> Result<(Vec<(u64, EIdx)>, HashMap<EIdx, bool>), CheckError> {
    match fvar_leaves_go(pers, st, acc, seen, fuel, x) {
        Err(e) => Err(e),
        Ok((a2, s2)) => fvar_leaves_go(pers, st, a2, s2, fuel, y),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1146-1147 fvarLeavesC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1146-1150 fvarLeavesFast` — the
/// executed `fvar_leaves`: one `seen`-guarded DAG walk.
pub fn fvar_leaves_fast(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<Vec<(u64, EIdx)>, CheckError>  {
    let seen: HashMap<EIdx, bool> = HashMap::new();
    match fvar_leaves_go(pers, st, Vec::new(), seen, fuel, h) {
        Err(e) => Err(e),
        Ok(p) => Ok(p.0),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1151-1154 leafMem
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1152-1159 leafMem` — is
/// `(idx, ty)` in the base leaf list?  con-leche compares the annotation with
/// `Expr.beq`; over handles it is handle equality, which is the same test
/// (`denoteE` is injective, DESIGN.md §8.3).
pub fn leaf_mem(bl: &Vec<(u64, EIdx)>, idx: u64, ty: &EIdx) -> bool {
    leaf_mem_from(bl, idx, ty, 0)
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1151-1154 leafMem
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1152-1159 leafMem` — the cursor
/// recursion the cited `List` recursion becomes (DESIGN.md §3.4).
pub fn leaf_mem_from(bl: &Vec<(u64, EIdx)>, idx: u64, ty: &EIdx, i: usize) -> bool {
    if i >= bl.len() {
        false
    } else if bl[i].0 == idx && bl[i].1.eq2(ty) {
        true
    } else {
        leaf_mem_from(bl, idx, ty, i + 1)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1189-1248 leavesSubXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1191 leavesSubGo` — probe the
/// subset memo (extraction rule 5).
pub fn leaves_sub_get(memo: &HashMap<EIdx, bool>, h: &EIdx) -> Option<bool> {
    match memo.get(h) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1189-1248 leavesSubXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1191 leavesSubGo` — the cited
/// `memo'.insert h r`, on the owned table.
pub fn leaves_sub_set(memo: HashMap<EIdx, bool>, h: &EIdx, r: bool) -> HashMap<EIdx, bool> {
    let mut m: HashMap<EIdx, bool> = memo;
    m.insert(h.dup2(), r);
    m
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1189-1248 leavesSubXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1191 leavesSubGo` — the
/// fabrication-side leaf-subset test: every reachable `fvar` leaf of the
/// walked term is one of `bl`.  Memoized on the node, because `bl` is fixed
/// for the call.
pub fn leaves_sub_go(
    pers: &PersTier,
    st: &AState,
    bl: &Vec<(u64, EIdx)>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    h: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LEAVES_SUB_GO)))
    } else if expr::fvar_of_data(derived_e(pers, st, h)) == 0 {
        Ok((true, memo))
    } else {
        match leaves_sub_get(&memo, h) {
            Some(r) => Ok((r, memo)),
            None => match view(pers, st, h) {
                Err(e) => Err(e),
                Ok(v) => match leaves_sub_node(pers, st, bl, memo, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((r, m)) => Ok((r, leaves_sub_set(m, h, r))),
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1189-1248 leavesSubXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1191 leavesSubGo` — the
/// arms, past the probe (extraction rule 5).
pub fn leaves_sub_node(
    pers: &PersTier,
    st: &AState,
    bl: &Vec<(u64, EIdx)>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    v: ENodeView,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match v {
        ENodeView::FVar(idx, ty) => {
            if leaf_mem(bl, idx, &ty) {
                leaves_sub_go(pers, st, bl, memo, fuel, &ty)
            } else {
                Ok((false, memo))
            }
        }
        ENodeView::App(f, a) => leaves_sub_two(pers, st, bl, memo, fuel, &f, &a),
        ENodeView::Lam(ty, body, _) => leaves_sub_two(pers, st, bl, memo, fuel, &ty, &body),
        ENodeView::ForallE(ty, body, _) => leaves_sub_two(pers, st, bl, memo, fuel, &ty, &body),
        ENodeView::LetE(ty, val, body) => match leaves_sub_go(pers, st, bl, memo, fuel, &ty) {
            Err(e) => Err(e),
            Ok((false, m)) => Ok((false, m)),
            Ok((true, m)) => leaves_sub_two(pers, st, bl, m, fuel, &val, &body),
        },
        ENodeView::Proj(_, _, sub) => leaves_sub_go(pers, st, bl, memo, fuel, &sub),
        ENodeView::BVar(_) => Ok((true, memo)),
        ENodeView::Sort(_) => Ok((true, memo)),
        ENodeView::Const(_, _) => Ok((true, memo)),
        ENodeView::Lit(_) => Ok((true, memo)),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1189-1248 leavesSubXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1191 leavesSubGo` — the
/// two-child arms and their short-circuit.
pub fn leaves_sub_two(
    pers: &PersTier,
    st: &AState,
    bl: &Vec<(u64, EIdx)>,
    memo: HashMap<EIdx, bool>,
    fuel: u64,
    x: &EIdx,
    y: &EIdx,
) -> Result<(bool, HashMap<EIdx, bool>), CheckError> {
    match leaves_sub_go(pers, st, bl, memo, fuel, x) {
        Err(e) => Err(e),
        Ok((false, m)) => Ok((false, m)),
        Ok((true, m)) => leaves_sub_go(pers, st, bl, m, fuel, y),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1256-1260 leafGuard
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1253-1264 leafGuard` — **the
/// fabrication leaf guard**: every `fvar` leaf of `fab` is a leaf of `base`.
/// Short-circuits on an `fvar`-free fabrication off the packed range, and
/// otherwise walks `fab` ONCE against `base`'s leaf list — never building
/// `fab`'s own list, and never running `arena::core`'s quadratic
/// `fvar_leaves_subset`, which stays as the specification of what this
/// decides.
pub fn leaf_guard(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    fab: &EIdx,
    base: &EIdx,
) -> Result<bool, CheckError>  {
    if expr::fvar_of_data(derived_e(pers, st, fab)) == 0 {
        Ok(true)
    } else {
        match fvar_leaves_fast(pers, st, fuel, base) {
            Err(e) => Err(e),
            Ok(bl) => {
                let memo: HashMap<EIdx, bool> = HashMap::new();
                match leaves_sub_go(pers, st, &bl, memo, fuel, fab) {
                    Err(e) => Err(e),
                    Ok(p) => Ok(p.0),
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The one-node readers: each is a single `view` and a test, no recursion
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:962-969 lamPw
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1270-1279 lamPw` — a λ node's
/// prop-ness annotation, `none` off λs.  `PropWhen` is a value and not a term,
/// so it crosses the signature unchanged.
pub fn lam_pw(pers: &PersTier, st: &AState, h: &EIdx) -> Result<Option<PropWhen>, CheckError> {
    if h.tag() == ETAG_LAM {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((_, _, m)) => Ok(Some(m.pw)),
        }
    } else {
        Ok(None)
    }
}

// ---------------------------------------------------------------------------
// Application spines
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:982-985 getAppFn
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1283-1292 getAppFn` — the head of
/// an application spine.
pub fn get_app_fn(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_APP_FN)))
    } else if h.tag() == ETAG_APP {
        match view_app(pers, st, h) {
            None => fail_dangling_e(),
            Some(p) => get_app_fn(pers, st, fuel - 1, &p.0),
        }
    } else {
        Ok(h.dup2())
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:987-990 getAppArgs
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1294-1305 getAppArgs` — the
/// arguments of an application spine, outermost last.  Lean's `as ++ [a]` is a
/// `push` here, which is the same list in one pass.
pub fn get_app_args(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<Vec<EIdx>, CheckError>  {
    get_app_args_go(pers, st, fuel, h, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:987-990 getAppArgs
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1294-1305 getAppArgs` — the
/// cursor recursion behind `get_app_args`.  `k` counts the arguments seen on
/// the way DOWN and is spent at the head as the vector's capacity (task
/// #97-P6-9): a `Vec` grown from empty reallocates once per doubling, and this
/// is on every reduction step.  A capacity is a representation difference the
/// refinement absorbs (DESIGN §8.6's twin-ledger rule).
pub fn get_app_args_go(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
    k: usize,
) -> Result<Vec<EIdx>, CheckError>  {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_APP_ARGS)))
    } else if h.tag() == ETAG_APP {
        match view_app(pers, st, h) {
            None => fail_dangling_e(),
            Some(p) => {
                let f: EIdx = p.0;
                let a: EIdx = p.1;
                match get_app_args_go(pers, st, fuel - 1, &f, k + 1) {
                    Err(e) => Err(e),
                    Ok(args) => {
                        let mut out: Vec<EIdx> = args;
                        out.push(a);
                        Ok(out)
                    }
                }
            }
        }
    } else {
        Ok(Vec::with_capacity(k))
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:992-995 mkAppN
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1307-1313 mkAppN` — apply to a
/// list of arguments.  Structural on the list, so no fuel; the `i = 0` wrapper
/// of the cursor recursion below.
pub fn mk_app_n(
    pers: &PersTier,
    st: &mut AState,
    f: &EIdx,
    args: &Vec<EIdx>,
) -> Result<EIdx, CheckError>  {
    mk_app_n_from(pers, st, f, args, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:992-995 mkAppN
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1307-1313 mkAppN` — the cursor
/// recursion behind `mk_app_n`.
pub fn mk_app_n_from(
    pers: &PersTier,
    st: &mut AState,
    f: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        Ok(f.dup2())
    } else {
        match intern_e_app(pers, st, f.dup2(), args[i].dup2()) {
            Err(e) => Err(e),
            Ok(g) => mk_app_n_from(pers, st, &g, args, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// Telescopes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:1337-1343 stripLams
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1329-1342 stripLams` — strip `k`
/// leading λs.  The recursion is structural on `k`, so no fuel; Lean's
/// `(ty, m) :: p.1` is `cons_binder`.
pub fn strip_lams(
    pers: &PersTier,
    st: &AState,
    k: u64,
    h: &EIdx,
) -> Result<Option<(Vec<(EIdx, BinderMeta)>, EIdx)>, CheckError> {
    if k == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        if h.tag() == ETAG_LAM {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, b, m)) => match strip_lams(pers, st, k - 1, &b) {
                    Err(e) => Err(e),
                    Ok(Some(p)) => Ok(Some((cons_binder(&ty, &m, &p.0), p.1))),
                    Ok(None) => Ok(None),
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1345-1351 stripPis
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1344-1357 stripPis` — strip `k`
/// leading `∀`s.
pub fn strip_pis(
    pers: &PersTier,
    st: &AState,
    k: u64,
    h: &EIdx,
) -> Result<Option<(Vec<(EIdx, BinderMeta)>, EIdx)>, CheckError> {
    if k == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((ty, b, m)) => match strip_pis(pers, st, k - 1, &b) {
                    Err(e) => Err(e),
                    Ok(Some(p)) => Ok(Some((cons_binder(&ty, &m, &p.0), p.1))),
                    Ok(None) => Ok(None),
                },
            }
        } else {
            Ok(None)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1353-1357 piResult
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1359-1371 piResult` — the body of
/// a syntactic `∀`-telescope.
pub fn pi_result(pers: &PersTier, st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PI_RESULT)))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind_i(pers, st, h) {
                None => fail_dangling_e(),
                Some((_, b, _)) => pi_result(pers, st, fuel - 1, &b),
            }
        } else {
            Ok(h.dup2())
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1487-1492 fvarTypeD
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1373-1381 fvarTypeD` — the type
/// annotation of a free-variable leaf (the expression itself otherwise).
pub fn fvar_type_d(pers: &PersTier, st: &AState, h: &EIdx) -> Result<EIdx, CheckError> {
    if h.tag() == ETAG_FVAR {
        match view_fvar_ty(pers, st, h) {
            None => fail_dangling_e(),
            Some(ty) => Ok(ty),
        }
    } else {
        Ok(h.dup2())
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1494-1502 instSpine
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1383-1389 instSpine` —
/// instantiate a telescope-context expression at an argument spine.
pub fn inst_spine(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    t: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    inst_spine_from(pers, st, fuel, args, 0, t, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1494-1502 instSpine
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1383-1389 instSpine` — the cursor
/// recursion behind `inst_spine`.  `t - 1` is Lean's truncating subtraction,
/// hence `sub_nat` (the cited arm carries no guard).
pub fn inst_spine_from(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    i: usize,
    t: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        Ok(e.dup2())
    } else {
        let a: EIdx = args[i].dup2();
        match instantiate1_fast(pers, st, fuel, e, &a, t) {
            Err(er) => Err(er),
            Ok(e2) => inst_spine_from(pers, st, fuel, args, i + 1, sub_nat(t, 1), &e2),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1504-1519 recRulePlain
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1391-1399 bvarRange` — the
/// comparand `(List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))`,
/// interned.  Structural on the count, so no fuel; `mI - 1 - k` is Lean's
/// truncating subtraction, hence `sub_nat`.
pub fn bvar_range(
    pers: &PersTier,
    st: &mut AState,
    m_i: u64,
    n: u64,
    k: u64,
) -> Result<Vec<EIdx>, CheckError> {
    if n == 0 {
        Ok(Vec::new())
    } else {
        match intern_e_bvar(pers, st, sub_nat(sub_nat(m_i, 1), k)) {
            Err(e) => Err(e),
            Ok(b) => match bvar_range(pers, st, m_i, n - 1, k + 1) {
                Err(e) => Err(e),
                Ok(rest) => Ok(cons_eidx(&b, &rest)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1504-1519 recRulePlain
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1401-1423 recRulePlain` — a
/// recursor rule is canonical when its constructor's parameters are exactly
/// the recursor's own leading arguments.  The `==` on the argument prefix is
/// index equality (the `==` inventory's line 1240): exactness makes it the
/// structural comparison con-leche writes.  The cited
/// `decide (cnP ≤ rP) && decide (rP ≤ mI)` is an `if` nest (task #3's pattern
/// 9).
pub fn rec_rule_plain(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    rec_ty: &EIdx,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
) -> Result<bool, CheckError> {
    if cn_p <= r_p && r_p <= m_i {
        match strip_pis(pers, st, m_i, rec_ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(p)) => if p.1.tag() == ETAG_FORALL_E {
                match view_bind(pers, st, &p.1) {
                    None => fail_dangling_e(),
                    Some((dom, _, _)) => match get_app_args(pers, st, fuel, &dom) {
                        Err(e) => Err(e),
                        Ok(args) => match bvar_range(pers, st, m_i, cn_p, 0) {
                            Err(e) => Err(e),
                            Ok(want) => Ok(eidx_take_beq(&args, &want)),
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` — **the syntactic
/// reading of a nested rule's instantiation**: the major's level and
/// parameter instantiations, read off the recursor type's major-premise
/// domain, the parameters lowered into the rule-prefix context (`rP`
/// binders), with the syntactic well-formedness guards `EnvWF` records for a
/// stored `.nested` rule.  `resolves` is the constructors' environment's
/// `constsResolveF` (its one instantiation, `tgtStoredRules`'s), so the port
/// takes that environment and its visibility bound.  The pins are lowered
/// before the guards run, as the cited `let` does.
#[allow(clippy::too_many_arguments)]
pub fn nested_rule_syn(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &crate::arena::env::IFEnv,
    lps: &Vec<NIdx>,
    ty_a: &EIdx,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    if r_p <= m_i {
        match strip_pis(pers, st, m_i, ty_a) {
            Err(e) => Err(e),
            Ok(None) => Ok(None),
            Ok(Some(q)) => {
                if q.1.tag() == ETAG_FORALL_E {
                    match view_bind(pers, st, &q.1) {
                        None => fail_dangling_e(),
                        Some((dom, _, _)) => match get_app_fn(pers, st, crate::arena::core::CORE_WALK_FUEL, &dom) {
                            Err(e) => Err(e),
                            Ok(hd) => {
                                if hd.tag() == ETAG_CONST {
                                    match view_const(pers, st, &hd) {
                                        None => fail_dangling_e(),
                                        Some((_, lvls)) => nested_rule_syn_at(
                                            pers, vis, st, fe, lps, &dom, &lvls, m_i - r_p, r_p, cn_p,
                                        ),
                                    }
                                } else {
                                    Ok(None)
                                }
                            }
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` — `pins :=
/// (args.take cnP).map (lowerBVars k 0)`, in order.
pub fn lower_list(
    pers: &PersTier,
    st: &mut AState,
    k: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match lower_bvars_fast(pers, st, crate::arena::core::CORE_WALK_FUEL, k, 0, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                lower_list(pers, st, k, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` —
/// `pins.map (liftLooseBVars k 0)`, in order.
pub fn lift_list(
    pers: &PersTier,
    st: &mut AState,
    k: u64,
    xs: &Vec<EIdx>,
    i: usize,
    out: Vec<EIdx>,
) -> Result<Vec<EIdx>, CheckError> {
    if i >= xs.len() {
        Ok(out)
    } else {
        let x: EIdx = xs[i].dup2();
        match lift_loose_bvars_fast(pers, st, crate::arena::core::CORE_WALK_FUEL, k, 0, &x) {
            Err(e) => Err(e),
            Ok(y) => {
                let mut o: Vec<EIdx> = out;
                o.push(y);
                lift_list(pers, st, k, xs, i + 1, o)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` — the pins'
/// guards from `i` on, in order, each conjunction left to right: fvar-free,
/// bounded by the prefix, resolving, level parameters declared.
#[allow(clippy::too_many_arguments)]
pub fn pins_wf(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &crate::arena::env::IFEnv,
    lps: &Vec<NIdx>,
    r_p: u64,
    pins: &Vec<EIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= pins.len() {
        Ok(true)
    } else {
        let p: EIdx = pins[i].dup2();
        match has_fvar_fast(pers, st, crate::arena::core::CORE_WALK_FUEL, &p) {
            Err(e) => Err(e),
            Ok(true) => Ok(false),
            Ok(false) => match loose_bvars_bounded_fast(pers, st, crate::arena::core::CORE_WALK_FUEL, r_p, &p) {
                Err(e) => Err(e),
                Ok(false) => Ok(false),
                Ok(true) => match crate::arena::checker_base::consts_resolve_f_fast(pers, vis, st, fe, &p) {
                    Err(e) => Err(e),
                    Ok(false) => Ok(false),
                    Ok(true) => match crate::arena::checker_base::all_level_params_defined(pers, st, lps, &p) {
                        Err(e) => Err(e),
                        Ok(false) => Ok(false),
                        Ok(true) => pins_wf(pers, vis, st, fe, lps, r_p, pins, i + 1),
                    },
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` —
/// `lvls.all (Level.allParamsDefined lps)`, the parameters' names read once.
pub fn levels_declared(
    pers: &PersTier,
    st: &AState,
    lps: &Vec<NIdx>,
    lvls: &Vec<LIdx>,
) -> Result<bool, CheckError> {
    match read_names(pers, st, lps) {
        Err(e) => Err(e),
        Ok(ps) => levels_declared_from(pers, st, &ps, lvls, 0),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: the cursor recursion behind `levels_declared`.
pub fn levels_declared_from(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<Name>,
    lvls: &Vec<LIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= lvls.len() {
        Ok(true)
    } else {
        match read_level(pers, st, &lvls[i]) {
            Err(e) => Err(e),
            Ok(l) => {
                if level::all_params_defined(ps, &l) {
                    levels_declared_from(pers, st, ps, lvls, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` — at the major's
/// domain `dom` headed by a constant at the levels `lvls`: the pins lowered,
/// then the cited five conjuncts in order (the arity, the lift-back
/// roundtrip, the trailing index variables, the pins' guards, the levels).
#[allow(clippy::too_many_arguments)]
pub fn nested_rule_syn_at(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &crate::arena::env::IFEnv,
    lps: &Vec<NIdx>,
    dom: &EIdx,
    lvls: &LsIdx,
    k: u64,
    r_p: u64,
    cn_p: u64,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    match get_app_args(pers, st, crate::arena::core::CORE_WALK_FUEL, dom) {
        Err(e) => Err(e),
        Ok(args) => {
            let pre: Vec<EIdx> = take_eidx_n(&args, cn_p);
            match lower_list(pers, st, k, &pre, 0, Vec::new()) {
                Err(e) => Err(e),
                Ok(pins) => {
                    if args.len() as u64 != cn_p + k {
                        Ok(None)
                    } else {
                        match lift_list(pers, st, k, &pins, 0, Vec::new()) {
                            Err(e) => Err(e),
                            Ok(back) => {
                                if !crate::arena::canon::eidx_vec_beq(&pre, &back, 0) {
                                    Ok(None)
                                } else {
                                    match bvar_range(pers, st, k, k, 0) {
                                        Err(e) => Err(e),
                                        Ok(want) => {
                                            let rest: Vec<EIdx> = crate::arena::core::drop_eidx_n(&args, cn_p);
                                            if !crate::arena::canon::eidx_vec_beq(&rest, &want, 0) {
                                                Ok(None)
                                            } else {
                                                nested_rule_syn_guards(pers, vis, st, fe, lps, lvls, r_p, pins)
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
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1521-1559 nestedRuleSyn
/// Lean twin: `proof/ConRon/Arena/CheckerBase.lean:477-499 nestedRuleSyn` — the pins' and
/// the levels' guards, and the reading.
#[allow(clippy::too_many_arguments)]
pub fn nested_rule_syn_guards(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    fe: &crate::arena::env::IFEnv,
    lps: &Vec<NIdx>,
    lvls: &LsIdx,
    r_p: u64,
    pins: Vec<EIdx>,
) -> Result<Option<(Vec<LIdx>, Vec<EIdx>)>, CheckError> {
    match pins_wf(pers, vis, st, fe, lps, r_p, &pins, 0) {
        Err(e) => Err(e),
        Ok(false) => Ok(None),
        Ok(true) => match view_ls(pers, st, lvls) {
            Err(e) => Err(e),
            Ok(ls) => match levels_declared(pers, st, lps, &ls) {
                Err(e) => Err(e),
                Ok(false) => Ok(None),
                Ok(true) => Ok(Some((ls, pins))),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The packed range fields and their saturated-branch recomputations
// (`ExprOps.lean:1293-1303`, `:1312-1323`, `:1368-1425`, `:1427-1439`)
//
// Both ranges are read in `O(1)` off the derived column; only on the saturated
// branch (a bound at or above `satRange = 32767`) does the arena walk, and
// that walk is memoized exactly as con-leche's is.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:1570-1580 Expr.bvarBound
/// con-leche: ConLeche/Kernel/ExprOps.lean:1645-1669 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1434-1459 bvarBoundGo` — the
/// memoized exact loose-bvar bound.  The memo is probed for every node, leaves
/// included, as con-leche probes it.  `y - 1` is Lean's truncating
/// subtraction, hence `sub_nat`.
pub fn bvar_bound_go(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    h: &EIdx,
) -> Result<u64, CheckError>  {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_BVAR_BOUND)))
    } else {
        match bvar_b_get(st, h) {
            Some(r) => Ok(r),
            None => {
                let body: Result<u64, CheckError> = match view(pers, st, h) {
                    Err(e) => Err(e),
                    Ok(ENodeView::BVar(i)) => Ok(i + 1),
                    Ok(ENodeView::FVar(_, _)) => Ok(0),
                    Ok(ENodeView::Sort(_)) => Ok(0),
                    Ok(ENodeView::Const(_, _)) => Ok(0),
                    Ok(ENodeView::Lit(_)) => Ok(0),
                    Ok(ENodeView::App(f, a)) => match bvar_bound_go(pers, st, fuel - 1, &f) {
                        Err(e) => Err(e),
                        Ok(x) => match bvar_bound_go(pers, st, fuel - 1, &a) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::Lam(ty, body, _)) => match bvar_bound_go(pers, st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(x) => match bvar_bound_go(pers, st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, sub_nat(y, 1))),
                        },
                    },
                    Ok(ENodeView::ForallE(ty, body, _)) => {
                        match bvar_bound_go(pers, st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match bvar_bound_go(pers, st, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(y) => Ok(expr::max_u64(x, sub_nat(y, 1))),
                            },
                        }
                    }
                    Ok(ENodeView::LetE(ty, val, body)) => {
                        match bvar_bound_go(pers, st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match bvar_bound_go(pers, st, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(y) => match bvar_bound_go(pers, st, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(z) => {
                                        Ok(expr::max_u64(expr::max_u64(x, y), sub_nat(z, 1)))
                                    }
                                },
                            },
                        }
                    }
                    Ok(ENodeView::Proj(_, _, sub)) => bvar_bound_go(pers, st, fuel - 1, &sub),
                };
                match body {
                    Err(e) => Err(e),
                    Ok(r) => {
                        bvar_b_set(st, h.dup2(), r);
                        Ok(r)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1671-1672 bvarBoundMemo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1511-1517 bvarBoundMemo` — the
/// top-level entry of the memoized walk.
pub fn bvar_bound_memo(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
) -> Result<u64, CheckError>  {
    bvar_b_clear(st);
    match bvar_bound_go(pers, st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            bvar_b_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1589-1600 Expr.fvarRange
/// con-leche: ConLeche/Kernel/ExprOps.lean:1674-1699 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1521-1543 fvarRangeGo` — the
/// memoized exact fvar range (`fvar` annotations are not descended into,
/// matching the abstraction traversals).
pub fn fvar_range_go(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    h: &EIdx,
) -> Result<u64, CheckError>  {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_FVAR_RANGE)))
    } else {
        match fvar_b_get(st, h) {
            Some(r) => Ok(r),
            None => {
                let body: Result<u64, CheckError> = match view(pers, st, h) {
                    Err(e) => Err(e),
                    Ok(ENodeView::FVar(idx, _)) => Ok(idx + 1),
                    Ok(ENodeView::BVar(_)) => Ok(0),
                    Ok(ENodeView::Sort(_)) => Ok(0),
                    Ok(ENodeView::Const(_, _)) => Ok(0),
                    Ok(ENodeView::Lit(_)) => Ok(0),
                    Ok(ENodeView::App(f, a)) => match fvar_range_go(pers, st, fuel - 1, &f) {
                        Err(e) => Err(e),
                        Ok(x) => match fvar_range_go(pers, st, fuel - 1, &a) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::Lam(ty, body, _)) => match fvar_range_go(pers, st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(x) => match fvar_range_go(pers, st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::ForallE(ty, body, _)) => {
                        match fvar_range_go(pers, st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match fvar_range_go(pers, st, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(y) => Ok(expr::max_u64(x, y)),
                            },
                        }
                    }
                    Ok(ENodeView::LetE(ty, val, body)) => {
                        match fvar_range_go(pers, st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match fvar_range_go(pers, st, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(y) => match fvar_range_go(pers, st, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(z) => Ok(expr::max_u64(expr::max_u64(x, y), z)),
                                },
                            },
                        }
                    }
                    Ok(ENodeView::Proj(_, _, sub)) => fvar_range_go(pers, st, fuel - 1, &sub),
                };
                match body {
                    Err(e) => Err(e),
                    Ok(r) => {
                        fvar_b_set(st, h.dup2(), r);
                        Ok(r)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1701-1702 fvarRangeMemo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1595-1601 fvarRangeMemo` — the
/// top-level entry of the memoized walk.
pub fn fvar_range_memo(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
) -> Result<u64, CheckError>  {
    fvar_b_clear(st);
    match fvar_range_go(pers, st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            fvar_b_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1704-1709 bvarB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1603-1610 bvarB` — **the
/// loose-bvar bound the checker reads**: the packed field, or — on the
/// saturated branch alone — the exact memoized recomputation.
pub fn bvar_b(pers: &PersTier, st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    let der: u64 = derived_e(pers, st, e);
    let r: u64 = expr::bvar_of_data(der);
    if r == expr::sat_range() {
        bvar_bound_memo(pers, st, fuel, e)
    } else {
        Ok(r)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1711-1716 fvarB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1612-1618 fvarB` — **the fvar
/// range the checker reads**: the packed field, or the exact memoized
/// recomputation on the saturated branch.
pub fn fvar_b(pers: &PersTier, st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    let der: u64 = derived_e(pers, st, e);
    let r: u64 = expr::fvar_of_data(der);
    if r == expr::sat_range() {
        fvar_range_memo(pers, st, fuel, e)
    } else {
        Ok(r)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1984-1985 hasFvarFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1620-1624 hasFvarFast` — the
/// executed `hasFvar`: the fvar-range field read.
pub fn has_fvar_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
) -> Result<bool, CheckError>  {
    match fvar_b(pers, st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r != 0),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1993-1994 looseBVarsBoundedFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1626-1630 looseBVarsBoundedFast`
/// — the executed `looseBVarsBounded`: the loose-bvar field read.
pub fn loose_bvars_bounded_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    k: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match bvar_b(pers, st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r <= k),
    }
}

// ---------------------------------------------------------------------------
// `abstract1` — `ExprOps.lean:760-776`, `:1789-1833`, `:1927-1929`
//
// The fvar-range cutoff comes first: a node whose whole subtree mentions no
// `fvar` at or above `d` is its own abstraction.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:838-854 abstract1
/// con-leche: ConLeche/Kernel/ExprOps.lean:2066-2110 abstract1Go
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1646-1666 abstract1Go` — close
/// a binder body: replace `fvar d …` leaves by `bvar k`, bumping `k` under
/// binders.  `fvar` annotations are not descended into.
pub fn abstract1_go(
    pers: &PersTier,
    st: &mut AState,
    d: u64,
    fuel: u64,
    h: &EIdx,
    k: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ABS1)))
    } else {
        match fvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(fb) => {
                if fb <= d {
                    Ok(h.dup2())
                } else {
                    let tg: u32 = h.tag();
                    if tg == ETAG_APP {
                        let ky: EIdxNat = eidx_nat_key(h, k);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_app(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let f: EIdx = p.0;
                                    let a: EIdx = p.1;
                                    match abstract1_go(pers, st, d, fuel - 1, &f, k) {
                                        Err(e) => Err(e),
                                        Ok(f2) => match abstract1_go(pers, st, d, fuel - 1, &a, k) {
                                            Err(e) => Err(e),
                                            Ok(a2) => {
                                                let same: bool = f2.eq2(&f) && a2.eq2(&a);
                                                match intern_rebuilt_app(pers, st, h, same, f2, a2) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        abs1_set(st, ky, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        },
                                    }
                                }
                            },
                        }
                    } else if e_tag_is_bind(tg) {
                        let ky: EIdxNat = eidx_nat_key(h, k);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_bind_i(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let ty: EIdx = p.0;
                                    let body: EIdx = p.1;
                                    let m: BMIdx = p.2;
                                    match abstract1_go(pers, st, d, fuel - 1, &ty, k) {
                                        Err(e) => Err(e),
                                        Ok(t) => {
                                            match abstract1_go(pers, st, d, fuel - 1, &body, k + 1)
                                            {
                                                Err(e) => Err(e),
                                                Ok(b2) => {
                                                    let same: bool =
                                                        t.eq2(&ty) && b2.eq2(&body);
                                                    match intern_rebuilt_bind_i(
                                                        pers, st, h, same, tg, t, b2, m,
                                                    ) {
                                                        Err(e) => Err(e),
                                                        Ok(r) => {
                                                            abs1_set(st, ky, &r);
                                                            Ok(r)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    } else if tg == ETAG_FVAR {
                        match view_fvar_idx(pers, st, h) {
                            None => fail_dangling_e(),
                            Some(idx) => {
                                if idx == d {
                                    intern_e_bvar(pers, st, k)
                                } else {
                                    Ok(h.dup2())
                                }
                            }
                        }
                    } else if tg == ETAG_LET_E {
                        let ky: EIdxNat = eidx_nat_key(h, k);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_let(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let ty: EIdx = p.0;
                                    let val: EIdx = p.1;
                                    let body: EIdx = p.2;
                                    match abstract1_go(pers, st, d, fuel - 1, &ty, k) {
                                        Err(e) => Err(e),
                                        Ok(t) => match abstract1_go(pers, st, d, fuel - 1, &val, k)
                                        {
                                            Err(e) => Err(e),
                                            Ok(w) => {
                                                match abstract1_go(
                                                    pers,
                                                    st,
                                                    d,
                                                    fuel - 1,
                                                    &body,
                                                    k + 1,
                                                ) {
                                                    Err(e) => Err(e),
                                                    Ok(b2) => {
                                                        let same: bool = t.eq2(&ty)
                                                            && w.eq2(&val)
                                                            && b2.eq2(&body);
                                                        match intern_rebuilt_let_e(pers, st, h, same, t, w, b2) {
                                                            Err(e) => Err(e),
                                                            Ok(r) => {
                                                                abs1_set(st, ky, &r);
                                                                Ok(r)
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        },
                                    }
                                }
                            },
                        }
                    } else if tg == ETAG_PROJ {
                        let ky: EIdxNat = eidx_nat_key(h, k);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_proj(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let n: NIdx = p.0;
                                    let i: u64 = p.1;
                                    let sub: EIdx = p.2;
                                    match abstract1_go(pers, st, d, fuel - 1, &sub, k) {
                                        Err(e) => Err(e),
                                        Ok(u) => {
                                            let same: bool = u.eq2(&sub);
                                            match intern_rebuilt_proj(pers, st, h, same, n, i, u) {
                                                Err(e) => Err(e),
                                                Ok(r) => {
                                                    abs1_set(st, ky, &r);
                                                    Ok(r)
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    } else {
                        Ok(h.dup2())
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2204-2206 abstract1Fast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1757-1763 abstract1Fast` — the
/// top-level entry.
pub fn abstract1_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    d: u64,
    k: u64,
) -> Result<EIdx, CheckError> {
    abs1_clear(st);
    match abstract1_go(pers, st, d, fuel, e, k) {
        Err(er) => Err(er),
        Ok(r) => {
            abs1_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `abstractRange`, the EXECUTED form — `Cached/ExprOpsC.lean:684-755`
//
// `abstract_range` above is con-leche's `Kernel/ExprOps.lean:791` spec: a bare
// structural descent.  The cached tier's `abstractRangeC` is the one the
// checker runs, and it is the same three devices `abstract1_go`/`abstract1C`
// already have here — the `fvarB <= d` cutoff at the node AND at every child
// (`abstractRangeP`'s first line, `enterAbsRP`), the per-call memo keyed by
// `(node, cursor)` (`abstractRangeXP`'s `MemoXP`), and the `k = 0` identity
// that skips the traversal outright (`abstractRangeC`'s own first clause).
//
// Task #97-P6-11 is what needed it: the annotation's binder-telescope loop
// calls `abstractRange` once per binder domain and once at the leaf, so the
// bare descent became the hottest walk of the run — on `Init` it turned
// 33.7 M construction attempts into 2 090.7 M, of which 99.9 % were cons-table
// hits.  With the three devices it is 27.4 M.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:676-692 abstractRangeP
/// con-leche: ConLeche/Cached/ExprOpsC.lean:707-738 abstractRangeXP
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1796-1817 abstractRangeGo` — the
/// memoized `abstractRange` walk: close the `k` free variables `d .. d + k - 1`
/// into `bvar`s at cursor `c`, innermost binder to the lowest index. The
/// `fvar_b <= d` cutoff is `abstractRangeP`'s own first line and
/// `enterAbsRP`'s; the `(h, c)` memo is `abstractRangeXP`'s, on the compound
/// arms only, exactly as `abstract1_go`'s is.
///
/// The memo table is `abstract1`'s (`abs1_*`).  The two walks never nest — both
/// are leaf walks over the store, calling nothing but `fvar_b`, `view` and
/// `intern` — and each entry point clears the table before and after itself, so
/// within one call the key `(h, c)` determines the result at the call's own
/// fixed `d` and `k`.
pub fn abstract_range_go(
    pers: &PersTier,
    st: &mut AState,
    d: u64,
    k: u64,
    fuel: u64,
    h: &EIdx,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ABS_RANGE)))
    } else {
        match fvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(fb) => {
                if fb <= d {
                    Ok(h.dup2())
                } else {
                    let tg: u32 = h.tag();
                    if tg == ETAG_APP {
                        let ky: EIdxNat = eidx_nat_key(h, c);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_app(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let f: EIdx = p.0;
                                    let a: EIdx = p.1;
                                    match abstract_range_go(pers, st, d, k, fuel - 1, &f, c) {
                                        Err(e) => Err(e),
                                        Ok(f2) => {
                                            match abstract_range_go(pers, st, d, k, fuel - 1, &a, c)
                                            {
                                                Err(e) => Err(e),
                                                Ok(a2) => {
                                                    let same: bool = f2.eq2(&f) && a2.eq2(&a);
                                                    match intern_rebuilt_app(pers, st, h, same, f2, a2) {
                                                        Err(e) => Err(e),
                                                        Ok(r) => {
                                                            abs1_set(st, ky, &r);
                                                            Ok(r)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    } else if e_tag_is_bind(tg) {
                        let ky: EIdxNat = eidx_nat_key(h, c);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_bind_i(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let ty: EIdx = p.0;
                                    let body: EIdx = p.1;
                                    let m: BMIdx = p.2;
                                    match abstract_range_go(pers, st, d, k, fuel - 1, &ty, c) {
                                        Err(e) => Err(e),
                                        Ok(t) => {
                                            match abstract_range_go(
                                                pers,
                                                st,
                                                d,
                                                k,
                                                fuel - 1,
                                                &body,
                                                c + 1,
                                            ) {
                                                Err(e) => Err(e),
                                                Ok(b2) => {
                                                    let same: bool = t.eq2(&ty) && b2.eq2(&body);
                                                    match intern_rebuilt_bind_i(
                                                        pers, st, h, same, tg, t, b2, m,
                                                    ) {
                                                        Err(e) => Err(e),
                                                        Ok(r) => {
                                                            abs1_set(st, ky, &r);
                                                            Ok(r)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    } else if tg == ETAG_FVAR {
                        match view_fvar_idx(pers, st, h) {
                            None => fail_dangling_e(),
                            Some(idx) => {
                                if d <= idx && idx < d + k {
                                    intern_e_bvar(pers, st, c + (d + k - 1 - idx))
                                } else {
                                    Ok(h.dup2())
                                }
                            }
                        }
                    } else if tg == ETAG_LET_E {
                        let ky: EIdxNat = eidx_nat_key(h, c);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_let(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let ty: EIdx = p.0;
                                    let val: EIdx = p.1;
                                    let body: EIdx = p.2;
                                    match abstract_range_go(pers, st, d, k, fuel - 1, &ty, c) {
                                        Err(e) => Err(e),
                                        Ok(t) => {
                                            match abstract_range_go(pers, st, d, k, fuel - 1, &val, c)
                                            {
                                                Err(e) => Err(e),
                                                Ok(w) => {
                                                    match abstract_range_go(
                                                        pers,
                                                        st,
                                                        d,
                                                        k,
                                                        fuel - 1,
                                                        &body,
                                                        c + 1,
                                                    ) {
                                                        Err(e) => Err(e),
                                                        Ok(b2) => {
                                                            let same: bool = t.eq2(&ty)
                                                                && w.eq2(&val)
                                                                && b2.eq2(&body);
                                                            match intern_rebuilt_let_e(pers, st, h, same, t, w, b2) {
                                                                Err(e) => Err(e),
                                                                Ok(r) => {
                                                                    abs1_set(st, ky, &r);
                                                                    Ok(r)
                                                                }
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
                    } else if tg == ETAG_PROJ {
                        let ky: EIdxNat = eidx_nat_key(h, c);
                        match abs1_get(st, &ky) {
                            Some(r) => Ok(r),
                            None => match view_proj(pers, st, h) {
                                None => fail_dangling_e(),
                                Some(p) => {
                                    let n: NIdx = p.0;
                                    let i: u64 = p.1;
                                    let sub: EIdx = p.2;
                                    match abstract_range_go(pers, st, d, k, fuel - 1, &sub, c) {
                                        Err(e) => Err(e),
                                        Ok(u) => {
                                            let same: bool = u.eq2(&sub);
                                            match intern_rebuilt_proj(pers, st, h, same, n, i, u) {
                                                Err(e) => Err(e),
                                                Ok(r) => {
                                                    abs1_set(st, ky, &r);
                                                    Ok(r)
                                                }
                                            }
                                        }
                                    }
                                }
                            },
                        }
                    } else {
                        Ok(h.dup2())
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:740-747 abstractRangeC
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1912-1923 abstractRangeFast` —
/// the top-level entry of the executed `abstractRange`: `k = 0` is the identity
/// and skips the traversal (con-leche's own clause, and what makes the
/// annotation telescope's OUTERMOST binder domain cost nothing), then the
/// per-call memo is cleared around the walk exactly as `abstract1_fast` clears
/// it.
pub fn abstract_range_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    d: u64,
    k: u64,
    c: u64,
) -> Result<EIdx, CheckError> {
    if k == 0 {
        Ok(e.dup2())
    } else {
        abs1_clear(st);
        match abstract_range_go(pers, st, d, k, fuel, e, c) {
            Err(er) => Err(er),
            Ok(r) => {
                abs1_clear(st);
                Ok(r)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `lowerBVars` — `ExprOps.lean:694-716`, `:2012-2049`, `:2144-2146`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:772-794 lowerBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:2286-2323 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1929-1954 lowerBVarsGo` — lower
/// every loose bound variable `>= cutoff + amount` by `amount`, with
/// con-leche's own `bvarB <= c + amount` cutoff.
pub fn lower_bvars_go(
    pers: &PersTier,
    st: &mut AState,
    amount: u64,
    fuel: u64,
    h: &EIdx,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LOWER)))
    } else {
        match bvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= c + amount {
                    Ok(h.dup2())
                } else {
                    match view(pers, st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(i)) => {
                            if i >= c + amount {
                                intern_e_bvar(pers, st, i - amount)
                            } else {
                                Ok(h.dup2())
                            }
                        }
                        Ok(ENodeView::FVar(_, _)) => Ok(h.dup2()),
                        Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
                        Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
                        Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
                        Ok(ENodeView::App(f, a)) => {
                            let k: EIdxNat = eidx_nat_key(h, c);
                            match lower_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match lower_bvars_go(pers, st, amount, fuel - 1, &f, c) {
                                    Err(e) => Err(e),
                                    Ok(f2) => match lower_bvars_go(pers, st, amount, fuel - 1, &a, c) {
                                        Err(e) => Err(e),
                                        Ok(a2) => match intern_e_app(pers, st, f2, a2) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                lower_set(st, k, &r);
                                                Ok(r)
                                            }
                                        },
                                    },
                                },
                            }
                        }
                        Ok(ENodeView::Lam(ty, body, m)) => {
                            let k: EIdxNat = eidx_nat_key(h, c);
                            match lower_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match lower_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match lower_bvars_go(pers, st, amount, fuel - 1, &body, c + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e_lam(pers, st, t, b, m) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        lower_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                        Ok(ENodeView::ForallE(ty, body, m)) => {
                            let k: EIdxNat = eidx_nat_key(h, c);
                            match lower_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match lower_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match lower_bvars_go(pers, st, amount, fuel - 1, &body, c + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e_forall_e(pers, st, t, b, m) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        lower_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                        Ok(ENodeView::LetE(ty, val, body)) => {
                            let k: EIdxNat = eidx_nat_key(h, c);
                            match lower_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match lower_bvars_go(pers, st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => match lower_bvars_go(pers, st, amount, fuel - 1, &val, c) {
                                        Err(e) => Err(e),
                                        Ok(w) => {
                                            match lower_bvars_go(pers, st, amount, fuel - 1, &body, c + 1)
                                            {
                                                Err(e) => Err(e),
                                                Ok(b) => {
                                                    match intern_e_let_e(pers, st, t, w, b) {
                                                        Err(e) => Err(e),
                                                        Ok(r) => {
                                                            lower_set(st, k, &r);
                                                            Ok(r)
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    },
                                },
                            }
                        }
                        Ok(ENodeView::Proj(n, i, sub)) => {
                            let k: EIdxNat = eidx_nat_key(h, c);
                            match lower_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match lower_bvars_go(pers, st, amount, fuel - 1, &sub, c) {
                                    Err(e) => Err(e),
                                    Ok(u) => match intern_e_proj(pers, st, n, i, u) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            lower_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2418-2420 lowerBVarsFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2054-2060 lowerBVarsFast` — the
/// top-level entry.
pub fn lower_bvars_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    amount: u64,
    c: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    lower_clear(st);
    match lower_bvars_go(pers, st, amount, fuel, e, c) {
        Err(er) => Err(er),
        Ok(r) => {
            lower_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `instantiate1Lift` — `ExprOps.lean:718-739`, `:2222-2261`, `:2356-2358`
//
// The general capture-avoiding substitution: unlike `instantiate1`, the
// replacement's own loose `bvar`s are lifted past the binders crossed on the
// way, which is what makes it usable on let-values.  It is the module's one
// NESTED walk — its `bvar` arm runs `liftLooseBVars`, which is why the two
// have separate memo tables.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:796-817 instantiate1Lift
/// con-leche: ConLeche/Kernel/ExprOps.lean:2494-2533 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2072-2101 instantiate1LiftGo` —
/// replace `bvar d` by `v`, lifting `v`'s loose `bvar`s past the binders
/// crossed on the way, with con-leche's own `bvarB <= d` cutoff.
pub fn instantiate1_lift_go(
    pers: &PersTier,
    st: &mut AState,
    v: &EIdx,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST1_LIFT)))
    } else {
        match bvar_b(pers, st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= d {
                    Ok(h.dup2())
                } else {
                    match view(pers, st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(i)) => {
                            if i == d {
                                lift_loose_bvars_fast(pers, st, fuel - 1, d, 0, v)
                            } else if i > d {
                                intern_e_bvar(pers, st, i - 1)
                            } else {
                                Ok(h.dup2())
                            }
                        }
                        Ok(ENodeView::FVar(_, _)) => Ok(h.dup2()),
                        Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
                        Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
                        Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
                        Ok(ENodeView::App(f, a)) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match inst1_l_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match instantiate1_lift_go(pers, st, v, fuel - 1, &f, d) {
                                    Err(e) => Err(e),
                                    Ok(f2) => {
                                        match instantiate1_lift_go(pers, st, v, fuel - 1, &a, d) {
                                            Err(e) => Err(e),
                                            Ok(a2) => {
                                                match intern_e_app(pers, st, f2, a2) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        inst1_l_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                        Ok(ENodeView::Lam(ty, body, m)) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match inst1_l_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match instantiate1_lift_go(pers, st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(pers, st, v, fuel - 1, &body, d + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e_lam(pers, st, t, b, m) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        inst1_l_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                        Ok(ENodeView::ForallE(ty, body, m)) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match inst1_l_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match instantiate1_lift_go(pers, st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(pers, st, v, fuel - 1, &body, d + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e_forall_e(pers, st, t, b, m) {
                                                    Err(e) => Err(e),
                                                    Ok(r) => {
                                                        inst1_l_set(st, k, &r);
                                                        Ok(r)
                                                    }
                                                }
                                            }
                                        }
                                    }
                                },
                            }
                        }
                        Ok(ENodeView::LetE(ty, val, body)) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match inst1_l_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match instantiate1_lift_go(pers, st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(pers, st, v, fuel - 1, &val, d) {
                                            Err(e) => Err(e),
                                            Ok(w) => {
                                                match instantiate1_lift_go(
                                                    pers,
                                                    st,
                                                    v,
                                                    fuel - 1,
                                                    &body,
                                                    d + 1,
                                                ) {
                                                    Err(e) => Err(e),
                                                    Ok(b) => {
                                                        match intern_e_let_e(pers, st, t, w, b) {
                                                            Err(e) => Err(e),
                                                            Ok(r) => {
                                                                inst1_l_set(st, k, &r);
                                                                Ok(r)
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
                        Ok(ENodeView::Proj(n, i, sub)) => {
                            let k: EIdxNat = eidx_nat_key(h, d);
                            match inst1_l_get(st, &k) {
                                Some(r) => Ok(r),
                                None => match instantiate1_lift_go(pers, st, v, fuel - 1, &sub, d) {
                                    Err(e) => Err(e),
                                    Ok(u) => match intern_e_proj(pers, st, n, i, u) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst1_l_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                },
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2628-2630 instantiate1LiftFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2205-2211 instantiate1LiftFast`
/// — the top-level entry.
pub fn instantiate1_lift_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    v: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst1_l_clear(st);
    match instantiate1_lift_go(pers, st, v, fuel, e, d) {
        Err(er) => Err(er),
        Ok(r) => {
            inst1_l_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2637-2650 instPisAtLift
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2213-2225 instPisAtLift` —
/// instantiate the leading `∀`-binders at *open* arguments.
pub fn inst_pis_at_lift(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    inst_pis_at_lift_from(pers, st, fuel, args, 0, h)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2637-2650 instPisAtLift
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2213-2225 instPisAtLift` — the
/// cursor recursion behind `inst_pis_at_lift`.
pub fn inst_pis_at_lift_from(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(h.dup2()))
    } else {
        if h.tag() == ETAG_FORALL_E {
            match view_bind(pers, st, h) {
                None => fail_dangling_e(),
                Some((_, body, _)) => {
                    let a: EIdx = args[i].dup2();
                    match instantiate1_lift_fast(pers, st, fuel, &body, &a, 0) {
                        Err(e) => Err(e),
                        Ok(b) => inst_pis_at_lift_from(pers, st, fuel, args, i + 1, &b),
                    }
                },
            }
        } else {
            Ok(None)
        }
    }
}

// ---------------------------------------------------------------------------
// `instantiateLevelParams` — `ExprOps.lean:2564-2603`, `:2718-2720`
//
// **The one twin that touches a level algorithm** (DESIGN.md §8.3 lesson 4).
// The substitution's names and levels are read back ONCE, at the entry, and
// the walk then runs con-leche's own `Level.subst` and `Level.substPW` on
// transient trees and re-interns the result.  The `ks`/`us` are therefore
// `Vec<Name>` and `Vec<Level>`, not `Vec<NIdx>` and `LsIdx`.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Level.lean:30-41 subst
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2237-2244 substLevelList` —
/// `vs.map (Level.subst ks us)` as explicit recursion.  con-leche writes the
/// `.map`; a closure is what DESIGN.md §3.4 forbids, and §3.4's own rule for a
/// `List` recursion is a helper, so the twin has one and so does this.
pub fn subst_level_list(ks: &Vec<Name>, us: &Vec<Level>, vs: &Vec<Level>) -> Vec<Level> {
    subst_level_list_from(ks, us, vs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Level.lean:30-41 subst
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2237-2244 substLevelList` — the
/// cursor recursion behind `subst_level_list`.
pub fn subst_level_list_from(
    ks: &Vec<Name>,
    us: &Vec<Level>,
    vs: &Vec<Level>,
    i: usize,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= vs.len() {
        out
    } else {
        let mut o: Vec<Level> = out;
        o.push(level::subst(ks, us, &vs[i]));
        subst_level_list_from(ks, us, vs, i + 1, o)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2831-2870 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2246-2261 substLMemoAt` —
/// `substLMemoAt`, `instLPGo`'s `.sort` arm's level work behind a memo on the
/// level handle.
///
/// `ks` and `us` are fixed for the whole `instLPFast` call, so a level handle
/// determines its own answer and the substitution vector is not in the key —
/// DESIGN.md §8.3's own rule for the per-call memos, and `inst_lp_clear` is
/// what makes it true.  A hit is one `u32`; a miss reads the level back (now
/// itself memoised per declaration), runs `Level.subst` on the transient tree
/// and re-interns.  A `.sort` node recurs once per OCCURRENCE in a term and
/// the same universe occurs over and over.
pub fn subst_l_memo_at(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<Name>,
    us: &Vec<Level>,
    u: &LIdx,
) -> Result<LIdx, CheckError> {
    match inst_lp_l_get(st, u) {
        Some(r) => Ok(r),
        None => match read_level_m(pers, st, u) {
            Err(e) => Err(e),
            Ok(l) => {
                let l2: Level = level::subst(ks, us, &l);
                match intern_level(pers, st, &l2) {
                    Err(e) => Err(e),
                    Ok(hl) => {
                        inst_lp_l_set(st, u.dup2(), &hl);
                        Ok(hl)
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2831-2870 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2263-2273 substLsMemoAt` —
/// `substLsMemoAt`, the `.const` arm's twin of `substLMemoAt` at an interned
/// universe-argument LIST. The list is one interned object, so the memo saves
/// the readback, the per-element substitution, the re-interning AND the two
/// `Vec<Level>` copies the readback memo would otherwise hand out and drop.
pub fn subst_ls_memo_at(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<Name>,
    us: &Vec<Level>,
    vs: &LsIdx,
) -> Result<LsIdx, CheckError> {
    match inst_lp_ls_get(st, vs) {
        Some(r) => Ok(r),
        None => match read_levels_m(pers, st, vs) {
            Err(e) => Err(e),
            Ok(ls) => {
                let ls2: Vec<Level> = subst_level_list(ks, us, &ls);
                match intern_levels(pers, st, &ls2) {
                    Err(e) => Err(e),
                    Ok(vs2) => {
                        inst_lp_ls_set(st, vs.dup2(), &vs2);
                        Ok(vs2)
                    }
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2831-2870 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2277-2309 instLPGo` —
/// substitute level parameters throughout an expression, with con-leche's own
/// `hasLP = false` cutoff (the whole subtree is level-parameter free, so the
/// substitution is the identity on it).  `.sort` and `.const` read their
/// levels back, run `Level.subst` on the transient trees and re-intern;
/// nothing else in this module touches a level.
pub fn inst_lp_go(
    pers: &PersTier,
    st: &mut AState,
    ks: &Vec<Name>,
    us: &Vec<Level>,
    fuel: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LP)))
    } else {
        let der: u64 = derived_e(pers, st, h);
        if !expr::lp_of_data(der) {
            Ok(h.dup2())
        } else {
            match view(pers, st, h) {
                Err(e) => Err(e),
                Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
                Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
                Ok(ENodeView::Sort(u)) => match subst_l_memo_at(pers, st, ks, us, &u) {
                    Err(e) => Err(e),
                    Ok(hl) => {
                        let same: bool = hl.eq2(&u);
                        intern_rebuilt_sort(pers, st, h, same, hl)
                    }
                },
                Ok(ENodeView::Const(n, vs)) => match subst_ls_memo_at(pers, st, ks, us, &vs) {
                    Err(e) => Err(e),
                    Ok(vs2) => {
                        let same: bool = vs2.eq2(&vs);
                        intern_rebuilt_const(pers, st, h, same, n, vs2)
                    }
                },
                Ok(ENodeView::FVar(i, ty)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => {
                                let same: bool = t.eq2(&ty);
                                match intern_rebuilt_fvar(pers, st, h, same, i, t) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst_lp_set(st, k, &r);
                                        Ok(r)
                                    }
                                }
                            }
                        },
                    }
                }
                Ok(ENodeView::App(f, a)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &f) {
                            Err(e) => Err(e),
                            Ok(f2) => match inst_lp_go(pers, st, ks, us, fuel - 1, &a) {
                                Err(e) => Err(e),
                                Ok(a2) => {
                                    let same: bool = f2.eq2(&f) && a2.eq2(&a);
                                    match intern_rebuilt_app(pers, st, h, same, f2, a2) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst_lp_set(st, k, &r);
                                            Ok(r)
                                        }
                                    }
                                }
                            },
                        },
                    }
                }
                Ok(ENodeView::Lam(ty, body, m)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(pers, st, ks, us, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b2) => {
                                    let m2: BinderMeta =
                                        expr::binder_meta(level::subst_pw(ks, us, &m.pw));
                                    let same: bool = t.eq2(&ty)
                                        && b2.eq2(&body)
                                        && expr::binder_meta_beq(&m2, &m);
                                    match intern_rebuilt_lam(pers, st, h, same, t, b2, m2) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst_lp_set(st, k, &r);
                                            Ok(r)
                                        }
                                    }
                                }
                            },
                        },
                    }
                }
                Ok(ENodeView::ForallE(ty, body, m)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(pers, st, ks, us, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b2) => {
                                    let m2: BinderMeta =
                                        expr::binder_meta(level::subst_pw(ks, us, &m.pw));
                                    let same: bool = t.eq2(&ty)
                                        && b2.eq2(&body)
                                        && expr::binder_meta_beq(&m2, &m);
                                    match intern_rebuilt_forall_e(pers, st, h, same, t, b2, m2) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst_lp_set(st, k, &r);
                                            Ok(r)
                                        }
                                    }
                                }
                            },
                        },
                    }
                }
                Ok(ENodeView::LetE(ty, val, body)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(pers, st, ks, us, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(w) => match inst_lp_go(pers, st, ks, us, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(b2) => {
                                        let same: bool =
                                            t.eq2(&ty) && w.eq2(&val) && b2.eq2(&body);
                                        match intern_rebuilt_let_e(pers, st, h, same, t, w, b2) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                inst_lp_set(st, k, &r);
                                                Ok(r)
                                            }
                                        }
                                    }
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::Proj(n, i, sub)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(pers, st, ks, us, fuel - 1, &sub) {
                            Err(e) => Err(e),
                            Ok(u2) => {
                                let same: bool = u2.eq2(&sub);
                                match intern_rebuilt_proj(pers, st, h, same, n, i, u2) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst_lp_set(st, k, &r);
                                        Ok(r)
                                    }
                                }
                            }
                        },
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2985-2987 Expr.instLPFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:2428-2445 instLPFast` — the
/// top-level entry: read the substitution back out of the store once, walk,
/// drop the memo.
pub fn inst_lp_fast(
    pers: &PersTier,
    st: &mut AState,
    fuel: u64,
    ks: &Vec<NIdx>,
    us: &LsIdx,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    // **The cutoff hoisted over the readback** (task #97-P6-10), the shape
    // task #97-P6-9's item 5 has at `instantiate_list`'s `.bvar` clause.
    // `inst_lp_go`'s own first act is `hasLP e = false → e`, and the walk is
    // the only consumer of `ks_p`/`us_p`; so on a level-parameter-free term
    // both readbacks — a `Vec<Name>` out of the name store, node by node and
    // string by string, and a `Vec<Level>` out of the level store — are
    // computed and dropped.  Deciding the cutoff FIRST is the same value by
    // the walk's own equation, in `O(1)` off the derived word.
    if !expr::lp_of_data(derived_e(pers, st, e)) {
        Ok(e.dup2())
    } else {
        match read_names_m(pers, st, ks) {
            Err(er) => Err(er),
            Ok(ks_p) => match read_levels_m(pers, st, us) {
                Err(er) => Err(er),
                Ok(us_p) => {
                    inst_lp_clear(st);
                    match inst_lp_go(pers, st, &ks_p, &us_p, fuel, e) {
                        Err(er) => Err(er),
                        Ok(r) => {
                            inst_lp_clear(st);
                            Ok(r)
                        }
                    }
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Tests: `proof/ConRon/Arena/ExprOpsTest.lean`'s 183 `#guard`s
//
// The twin's differential check, re-expressed.  For every twin with a
// con-leche counterpart on `Expr`:
//
// > intern a term, run the twin, read the result back with `denote_e`, and
// > compare with `con_ron_core::kernel::expr_ops`' own function applied to the
// > *denotation of the input*.
//
// The expected side is COMPUTED, never written out, so a check cannot drift
// from the twin; what IS written by hand is the fixture's own denotation
// (`fixture_denotes_what_it_should`, nineteen assertions), which is what makes
// the computed expectations trustworthy.  The comparison partner is
// `con-ron-core`'s `kernel::expr_ops` — the SHIPPING checker's `ExprOps`, port
// of the same con-leche file — so an agreement here is an agreement between
// the arena and the tree-shaped checker on the same term, not between two
// readings of the same code.
//
// `Denote.lean`'s `denoteE` has no shipped counterpart (task #97-P4a: the
// readback is the arena's own verification), so it lives here, exactly as
// `arena::store`'s `mod tests` keeps its own.  The name/level readbacks it
// needs are `arena::monad`'s shipped ones.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {

    // The literal containment `Kernel/Core.lean` spells the scope guard's
    // last test with (`fab.fvarLeaves.all (fun l => major.fvarLeaves.contains
    // l)`): the oracle `leaf_guard` is checked against (task #105 moved it
    // here from `arena::core`, where nothing but this test called it).
    fn fvar_leaves_subset(xs: &Vec<(u64, EIdx)>, ys: &Vec<(u64, EIdx)>) -> bool {
        xs.iter().all(|x| ys.iter().any(|y| y.0 == x.0 && y.1.eq2(&x.1)))
    }

    // The pure `fvarLeaves` (con-leche `Kernel/ExprOps.lean:899-911`, twin
    // `Arena/ExprOps.lean` `fvarLeaves`): the oracle `fvar_leaves_fast`,
    // `leaf_guard` and `fab_scope_ok` are checked against below.  Test-only
    // since task #105 — the checker runs the memoized one.
    const M_FUEL_FVAR_LEAVES: [u32; 26] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 102, 118, 97,
        114, 76, 101, 97, 118, 101, 115,
    ];

    /// `fvarLeaves`' `x ++ y`: the cursor recursion that copies `xs` onto `out`.
    fn fvl_copy_from(
        xs: &Vec<(u64, EIdx)>,
        i: usize,
        out: Vec<(u64, EIdx)>,
    ) -> Vec<(u64, EIdx)> {
        if i >= xs.len() {
            out
        } else {
            let mut o: Vec<(u64, EIdx)> = out;
            o.push((xs[i].0, xs[i].1.dup2()));
            fvl_copy_from(xs, i + 1, o)
        }
    }

    /// `x ++ y`.
    fn fvl_append(x: &Vec<(u64, EIdx)>, y: &Vec<(u64, EIdx)>) -> Vec<(u64, EIdx)> {
        fvl_copy_from(y, 0, fvl_copy_from(x, 0, Vec::new()))
    }

    /// reachable `fvar` leaves, hereditarily through their annotations.  Lean's
    /// `::` and `++` are the copying combinators above.
    fn fvar_leaves(
        pers: &PersTier,
        st: &AState,
        fuel: u64,
        h: &EIdx,
    ) -> Result<Vec<(u64, EIdx)>, CheckError> {
        if fuel == 0 {
            fail(CheckError::Internal(code_points(&M_FUEL_FVAR_LEAVES)))
        } else {
            match view(pers, st, h) {
                Err(e) => Err(e),
                Ok(ENodeView::FVar(idx, ty)) => match fvar_leaves(pers, st, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(rest) => {
                        let mut out: Vec<(u64, EIdx)> = Vec::new();
                        out.push((idx, ty.dup2()));
                        Ok(fvl_copy_from(&rest, 0, out))
                    }
                },
                Ok(ENodeView::App(f, a)) => match fvar_leaves(pers, st, fuel - 1, &f) {
                    Err(e) => Err(e),
                    Ok(x) => match fvar_leaves(pers, st, fuel - 1, &a) {
                        Err(e) => Err(e),
                        Ok(y) => Ok(fvl_append(&x, &y)),
                    },
                },
                Ok(ENodeView::Lam(ty, b, _)) => match fvar_leaves(pers, st, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(x) => match fvar_leaves(pers, st, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(y) => Ok(fvl_append(&x, &y)),
                    },
                },
                Ok(ENodeView::ForallE(ty, b, _)) => match fvar_leaves(pers, st, fuel - 1, &ty) {
                    Err(e) => Err(e),
                    Ok(x) => match fvar_leaves(pers, st, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(y) => Ok(fvl_append(&x, &y)),
                    },
                },
                Ok(ENodeView::LetE(t, v, b)) => match fvar_leaves(pers, st, fuel - 1, &t) {
                    Err(e) => Err(e),
                    Ok(x) => match fvar_leaves(pers, st, fuel - 1, &v) {
                        Err(e) => Err(e),
                        Ok(y) => match fvar_leaves(pers, st, fuel - 1, &b) {
                            Err(e) => Err(e),
                            Ok(z) => Ok(fvl_append(&fvl_append(&x, &y), &z)),
                        },
                    },
                },
                Ok(ENodeView::Proj(_, _, sub)) => fvar_leaves(pers, st, fuel - 1, &sub),
                Ok(ENodeView::BVar(_)) => Ok(Vec::new()),
                Ok(ENodeView::Sort(_)) => Ok(Vec::new()),
                Ok(ENodeView::Const(_, _)) => Ok(Vec::new()),
                Ok(ENodeView::Lit(_)) => Ok(Vec::new()),
            }
        }
    }
    use super::*;
    use crate::arena::monad::{
        AState, denote_l, denote_ls, denote_n, intern_e_lit, intern_e_sort, intern_l_node, intern_ls_node, intern_n_node,
    };
    use crate::arena::store::{EStore, LNodeView, NNodeView};
    use crate::kernel::expr::Expr;

    use crate::kernel::prop_when;
    use crate::kernel::level as core_level;
    use crate::kernel::name;
    use crate::ron::nat;

    /// The fuel every check runs at.  The fixture's deepest term is six nodes
    /// deep; 100 is a comfortable margin, as it is in the twin's `F`.
    const F: u64 = 100;

    /// `Result::unwrap` needs `E: Debug`, and `CheckError` deliberately has
    /// none (DESIGN.md §3.4).
    fn ok<T>(r: Result<T, CheckError>) -> T {
        match r {
            Ok(x) => x,
            Err(_) => panic!("the arena declined an operation the test expected it to take"),
        }
    }

    /// A string as the `Vec<u32>` of code points the verified core uses.
    fn cp(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    // --- the expression readback (`Denote.lean:183-206`), test-only ---------

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
                    (Some(s), Some(x)) => Some(expr::proj(s, k, x)),
                    _ => None,
                }
            }
        }
    }

    fn denote_e(pers: &PersTier, st: &EStore, i: &EIdx) -> Option<Expr> {
        denote_e_aux(pers, st, st.node_count(pers) as u64 + 1, i)
    }

    /// The twin's `E h`: the denotation of a fixture handle.
    fn den(pers: &PersTier, st: &AState, h: &EIdx) -> Expr {
        match denote_e(pers, &st.store, h) {
            Some(e) => e,
            None => panic!("a fixture handle does not denote"),
        }
    }

    /// The twin's `L h`.
    fn den_l(pers: &PersTier, st: &AState, h: &LIdx) -> Level {
        match denote_l(pers, st.store.ls(), h) {
            Some(u) => u,
            None => panic!("a fixture level handle does not denote"),
        }
    }

    /// The twin's `N h`.
    fn den_n(pers: &PersTier, st: &AState, h: &NIdx) -> Name {
        match denote_n(pers, st.store.ns(), h) {
            Some(n) => n,
            None => panic!("a fixture name handle does not denote"),
        }
    }

    // --- the brief's `intern_expr`: an `Expr` tree walked into the store -----

    /// Intern a whole `Expr` tree, node by node, and answer its handle.  The
    /// inverse of `denote_e` on well-formed input, which is what
    /// `intern_expr_round_trips` checks; it is also how a test that starts
    /// from a `con-ron-core` term rather than from a handle gets into the
    /// arena.
    fn intern_expr(pers: &PersTier, st: &mut AState, e: &Expr) -> EIdx {
        match expr::view(e) {
            expr::ExprView::Bvar(i) => ok(intern_e_bvar(pers, st, *i)),
            expr::ExprView::Fvar(i, ty) => {
                let t = intern_expr(pers, st, ty);
                ok(intern_e_fvar(pers, st, *i, t))
            }
            expr::ExprView::Sort(u) => {
                let hu = ok(crate::arena::monad::intern_level(pers, st, u));
                ok(intern_e_sort(pers, st, hu))
            }
            expr::ExprView::Const(n, us) => {
                let hn = ok(crate::arena::monad::intern_name(pers, st, n));
                let hus = ok(crate::arena::monad::intern_levels(pers, st, us));
                ok(intern_e_const(pers, st, hn, hus))
            }
            expr::ExprView::App(f, a) => {
                let hf = intern_expr(pers, st, f);
                let ha = intern_expr(pers, st, a);
                ok(intern_e_app(pers, st, hf, ha))
            }
            expr::ExprView::Lam(ty, b, m) => {
                let ht = intern_expr(pers, st, ty);
                let hb = intern_expr(pers, st, b);
                ok(intern_e_lam(pers, st, ht, hb, expr::binder_meta_dup(m)))
            }
            expr::ExprView::ForallE(ty, b, m) => {
                let ht = intern_expr(pers, st, ty);
                let hb = intern_expr(pers, st, b);
                ok(intern_e_forall_e(pers, st, ht, hb, expr::binder_meta_dup(m)))
            }
            expr::ExprView::LetE(ty, v, b) => {
                let ht = intern_expr(pers, st, ty);
                let hv = intern_expr(pers, st, v);
                let hb = intern_expr(pers, st, b);
                ok(intern_e_let_e(pers, st, ht, hv, hb))
            }
            expr::ExprView::Lit(l) => ok(intern_e_lit(pers, st, expr::literal_dup(l))),
            expr::ExprView::Proj(n, i, sub) => {
                let hn = ok(crate::arena::monad::intern_name(pers, st, n));
                let hs = intern_expr(pers, st, sub);
                ok(intern_e_proj(pers, st, hn, *i, hs))
            }
        }
    }

    // --- the comparison shapes ---------------------------------------------

    fn eq_e(pers: &PersTier, st: &AState, got: &EIdx, want: &Expr) -> bool {
        expr::beq(&den(pers, st, got), want)
    }

    // --- the fixture --------------------------------------------------------

    /// The handles the checks below name — the twin's `Fx`, built by the same
    /// `intern` calls in the same order, so that a handle here is the same
    /// machine word as a handle there.
    struct Fx {
        pu: LIdx,
        us_z: LsIdx,
        foo: NIdx,
        s0: EIdx,
        s1: EIdx,
        su: EIdx,
        cf: EIdx,
        cb: EIdx,
        lit7: EIdx,
        fv0: EIdx,
        fv1: EIdx,
        pj: EIdx,
        lam_t: EIdx,
        all_t: EIdx,
        let_t: EIdx,
        big: EIdx,
        pi_t: EIdx,
        pi_s: EIdx,
        lam_t2: EIdx,
        spine: EIdx,
    }

    /// Two sorts, a parameter sort, two constants, three loose `bvar`s, two
    /// `fvar`s with annotations, a literal, and the composite terms the checks
    /// walk (a λ over a `let` over a `∀` over a `proj` over a spine; a
    /// two-binder `∀`-telescope and its λ twin; an application spine).
    fn fixture() -> (AState, Fx) {
        let pers: &PersTier = &PersTier::empty();
        let mut st = AState::init(EStore::empty());
        let nev = || expr::binder_meta(prop_when::never());
        let z = ok(intern_l_node(pers, &mut st, LNodeView::Zero));
        let one = ok(intern_l_node(pers, &mut st, LNodeView::Succ(z.dup2())));
        let anon = ok(intern_n_node(pers, &mut st, NNodeView::Anonymous));
        let foo = ok(intern_n_node(pers, &mut st, NNodeView::Str(anon.dup2(), cp("foo"))));
        let bar = ok(intern_n_node(pers, &mut st, NNodeView::Str(anon.dup2(), cp("bar"))));
        let u_n = ok(intern_n_node(pers, &mut st, NNodeView::Str(anon.dup2(), cp("u"))));
        let pu = ok(intern_l_node(pers, &mut st, LNodeView::Param(u_n.dup2())));
        let us_z = ok(intern_ls_node(pers, &mut st, vec![z.dup2()]));
        let us_u = ok(intern_ls_node(pers, &mut st, vec![pu.dup2()]));
        let s0 = ok(intern_e_sort(pers, &mut st, z.dup2()));
        let s1 = ok(intern_e_sort(pers, &mut st, one.dup2()));
        let su = ok(intern_e_sort(pers, &mut st, pu.dup2()));
        let cf = ok(intern_e_const(pers, &mut st, foo.dup2(), us_z.dup2()));
        let cb = ok(intern_e_const(pers, &mut st, bar.dup2(), us_u.dup2()));
        let b0 = ok(intern_e_bvar(pers, &mut st, 0));
        let b1 = ok(intern_e_bvar(pers, &mut st, 1));
        let b2 = ok(intern_e_bvar(pers, &mut st, 2));
        let lit7 = ok(intern_e_lit(pers, &mut st, expr::literal_nat(nat::from_u64(7))));
        let fv0 = ok(intern_e_fvar(pers, &mut st, 0, s0.dup2()));
        let fv1 = ok(intern_e_fvar(pers, &mut st, 1, s1.dup2()));
        let ap1 = ok(intern_e_app(pers, &mut st, cf.dup2(), b0.dup2()));
        let pj = ok(intern_e_proj(pers, &mut st, foo.dup2(), 0, ap1.dup2()));
        let lam_t = ok(intern_e_lam(pers, &mut st, s0.dup2(), ap1.dup2(), nev()));
        let apbf = ok(intern_e_app(pers, &mut st, b1.dup2(), fv0.dup2()));
        let all_t = ok(intern_e_forall_e(pers, &mut st, s0.dup2(), apbf.dup2(), nev()));
        let apbb = ok(intern_e_app(pers, &mut st, b0.dup2(), b1.dup2()));
        let let_t = ok(intern_e_let_e(pers, &mut st, s0.dup2(), cf.dup2(), apbb.dup2()));
        let apcb = ok(intern_e_app(pers, &mut st, cb.dup2(), b0.dup2()));
        let apfv = ok(intern_e_app(pers, &mut st, fv1.dup2(), b0.dup2()));
        let apb2 = ok(intern_e_app(pers, &mut st, b2.dup2(), apfv.dup2()));
        let pj2 = ok(intern_e_proj(pers, &mut st, foo.dup2(), 0, apb2.dup2()));
        let inner = ok(intern_e_forall_e(pers, &mut st, s1.dup2(), pj2.dup2(), nev()));
        let let_b = ok(intern_e_let_e(pers, &mut st, su.dup2(), apcb.dup2(), inner.dup2()));
        let big = ok(intern_e_lam(pers, &mut st, s0.dup2(), let_b.dup2(), nev()));
        let apb10 = ok(intern_e_app(pers, &mut st, b1.dup2(), b0.dup2()));
        let pi_in = ok(intern_e_forall_e(pers, &mut st, s1.dup2(), apb10.dup2(), nev()));
        let pi_t = ok(intern_e_forall_e(pers, &mut st, s0.dup2(), pi_in.dup2(), nev()));
        let pi_s = ok(intern_e_forall_e(pers, &mut st, s0.dup2(), s1.dup2(), nev()));
        let lam_in = ok(intern_e_lam(pers, &mut st, s1.dup2(), apb10.dup2(), nev()));
        let lam_t2 = ok(intern_e_lam(pers, &mut st, s0.dup2(), lam_in.dup2(), nev()));
        let sp1 = ok(intern_e_app(pers, &mut st, cf.dup2(), fv0.dup2()));
        let spine = ok(intern_e_app(pers, &mut st, sp1.dup2(), b0.dup2()));
        let fx = Fx {
            pu,
            us_z,
            foo,
            s0,
            s1,
            su,
            cf,
            cb,
            lit7,
            fv0,
            fv1,
            pj,
            lam_t,
            all_t,
            let_t,
            big,
            pi_t,
            pi_s,
            lam_t2,
            spine,
        };
        (st, fx)
    }

    // --- the fixture denotes what it should (19) ----------------------------
    //
    // The one place a con-leche value is written out by hand; the checks
    // below read the fixture's handles, which is only meaningful because
    // these hold.

    #[test]
    fn fixture_denotes_what_it_should() {
        let pers: &PersTier = &PersTier::empty();
        let (st, fx) = fixture();
        let anon = name::anonymous();
        let nfoo = name::mk_str(name::anonymous(), cp("foo"));
        let nbar = name::mk_str(name::anonymous(), cp("bar"));
        let nu = name::mk_str(name::anonymous(), cp("u"));
        let nev = || expr::binder_meta(prop_when::never());
        assert!(eq_e(pers, &st, &fx.s0, &expr::sort(core_level::zero())));
        assert!(eq_e(
            pers,
            &st,
            &fx.s1,
            &expr::sort(core_level::succ(core_level::zero()))
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.su,
            &expr::sort(core_level::param(name::dup(&nu)))
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.cf,
            &expr::mk_const(name::dup(&nfoo), vec![core_level::zero()])
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.cb,
            &expr::mk_const(
                name::dup(&nbar),
                vec![core_level::param(name::dup(&nu))]
            )
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.fv1,
            &expr::fvar(1, expr::sort(core_level::succ(core_level::zero())))
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.lit7,
            &expr::lit(expr::literal_nat(nat::from_u64(7)))
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.lam_t,
            &expr::lam(
                expr::sort(core_level::zero()),
                expr::app(
                    expr::mk_const(name::dup(&nfoo), vec![core_level::zero()]),
                    expr::bvar(0)
                ),
                nev()
            )
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.big,
            &expr::lam(
                expr::sort(core_level::zero()),
                expr::let_e(
                    expr::sort(core_level::param(name::dup(&nu))),
                    expr::app(
                        expr::mk_const(
                            name::dup(&nbar),
                            vec![core_level::param(name::dup(&nu))]
                        ),
                        expr::bvar(0)
                    ),
                    expr::forall_e(
                        expr::sort(core_level::succ(core_level::zero())),
                        expr::proj(
                            name::dup(&nfoo),
                            0,
                            expr::app(
                                expr::bvar(2),
                                expr::app(
                                    expr::fvar(
                                        1,
                                        expr::sort(core_level::succ(core_level::zero()))
                                    ),
                                    expr::bvar(0)
                                )
                            )
                        ),
                        nev()
                    )
                ),
                nev()
            )
        ));
        assert!(eq_e(
            pers,
            &st,
            &fx.pi_t,
            &expr::forall_e(
                expr::sort(core_level::zero()),
                expr::forall_e(
                    expr::sort(core_level::succ(core_level::zero())),
                    expr::app(expr::bvar(1), expr::bvar(0)),
                    nev()
                ),
                nev()
            )
        ));
        assert!(denote_e(pers, &st.store, &fx.let_t).is_some());
        assert!(denote_e(pers, &st.store, &fx.all_t).is_some());
        assert!(denote_e(pers, &st.store, &fx.pj).is_some());
        assert!(denote_e(pers, &st.store, &fx.spine).is_some());
        assert!(denote_e(pers, &st.store, &fx.lam_t2).is_some());
        assert!(denote_e(pers, &st.store, &fx.pi_s).is_some());
        assert!(name::beq(&den_n(pers, &st, &fx.foo), &nfoo));
        assert!(core_level::beq(
            &den_l(pers, &st, &fx.pu),
            &core_level::param(name::dup(&nu))
        ));
        assert!(match denote_ls(pers, st.store.ls_s(), &fx.us_z) {
            Some(us) => us.len() == 1 && core_level::beq(&us[0], &core_level::zero()),
            None => false,
        });
        let _ = anon;
    }

    /// The brief's `intern_expr`, checked against the readback: interning a
    /// tree and denoting it back is the identity.  Not one of the twin's
    /// `#guard`s — it is what licenses using `intern_expr` at all.
    #[test]
    fn intern_expr_round_trips() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, fx) = fixture();
        let e = den(pers, &st, &fx.big);
        let h = intern_expr(pers, &mut st, &e);
        assert!(eq_e(pers, &st, &h, &e));
        // hash-consing: the tree came out of the store, so it goes back in at
        // the same handle.
        assert!(h.eq2(&fx.big));
    }

    // --- the scope queries, MEMOIZED against the pure ones (16) -------------

    /// Task #97g's item 5, differentially: each memoized walk against the
    /// unmemoized one it replaces, on the same subjects.  The memo may only
    /// change the COST — `wscoped_b_fast` is `wscoped_b`, `leaf_guard` is
    /// `fvar_leaves_subset` over the two leaf lists, and `fvar_leaves_fast` is
    /// `fvar_leaves` as a SET (the `seen` guard drops the duplicates a shared
    /// subterm contributes, which is the whole point of it, and the list is
    /// used only as a membership base).
    #[test]
    fn t_scope_queries_memoized() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, fx) = fixture();

        // the `fvar_b == 0` short-circuit answers `true` without a walk
        assert!(ok(wscoped_b_fast(pers, &st, F, 0, &fx.s0)));

        // `fvar_leaves_fast` is `fvar_leaves` as a set
        for h in [&fx.big, &fx.fv1, &fx.fv0, &fx.all_t, &fx.let_t, &fx.s0] {
            let slow = ok(fvar_leaves(pers, &st, F, h));
            let fast = ok(fvar_leaves_fast(pers, &st, F, h));
            assert!(
                slow.iter().all(|l| leaf_mem(&fast, l.0, &l.1)),
                "every pure leaf is a memoized one"
            );
            assert!(
                fast.iter().all(|l| leaf_mem(&slow, l.0, &l.1)),
                "and back"
            );
        }

        // `leaf_guard fab base` is `fvar_leaves_subset (leaves fab) (leaves base)`
        for p in [
            (&fx.fv1, &fx.big),
            (&fx.big, &fx.fv1),
            (&fx.big, &fx.big),
            (&fx.s0, &fx.big),
            (&fx.fv0, &fx.fv1),
        ] {
            let want = fvar_leaves_subset(
                &ok(fvar_leaves(pers, &st, F, p.0)),
                &ok(fvar_leaves(pers, &st, F, p.1)),
            );
            assert_eq!(ok(leaf_guard(pers, &st, F, p.0, p.1)), want, "the leaf guard");
        }

        // and the three tests `fab_scope_ok` is, against the spelling task
        // #97-P4d ported from the spec tier
        for p in [(&fx.fv1, &fx.big), (&fx.big, &fx.fv1), (&fx.s0, &fx.s0)] {
            let memo = ok(crate::arena::core::fab_scope_ok(pers, &mut st, 5, p.0, p.1));
            let slow = ok(wscoped_b_fast(pers, &st, F, 5, p.0))
                && ok(loose_bvars_bounded_fast(pers, &mut st, F, 0, p.0))
                && fvar_leaves_subset(
                    &ok(fvar_leaves(pers, &st, F, p.0)),
                    &ok(fvar_leaves(pers, &st, F, p.1)),
                );
            assert_eq!(memo, slow, "fab_scope_ok is the pure predicate");
        }
    }

    // --- the store primitives of `Monad.lean` (6) ---------------------------

    #[test]
    fn t_monad_primitives() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, fx) = fixture();

        match ok(view(pers, &st, &fx.big)) {
            ENodeView::Lam(ty, body, _) => {
                assert!(ty.eq2(&fx.s0));
                assert!(!body.eq2(&fx.s0));
            }
            _ => panic!("`big` is a λ"),
        }
        let u = ok(crate::arena::monad::read_level(pers, &st, &fx.pu));
        assert!(core_level::beq(
            &u,
            &core_level::param(name::mk_str(name::anonymous(), cp("u")))
        ));
        let n = ok(crate::arena::monad::read_name(pers, &st, &fx.foo));
        assert!(name::beq(&n, &name::mk_str(name::anonymous(), cp("foo"))));

        let l = core_level::succ(core_level::succ(core_level::zero()));
        let hl = ok(crate::arena::monad::intern_level(pers, &mut st, &l));
        assert!(core_level::beq(&den_l(pers, &st, &hl), &l));

        let nm = name::mk_str(name::mk_str(name::anonymous(), cp("a")), cp("b"));
        let hn = ok(crate::arena::monad::intern_name(pers, &mut st, &nm));
        assert!(name::beq(&den_n(pers, &st, &hn), &nm));

        let us = vec![
            core_level::zero(),
            core_level::param(name::mk_str(name::anonymous(), cp("u"))),
        ];
        let hus = ok(crate::arena::monad::intern_levels(pers, &mut st, &us));
        let back = ok(crate::arena::monad::read_levels(pers, &st, &hus));
        assert!(back.len() == 2);
        assert!(core_level::beq(&back[0], &us[0]));
        assert!(core_level::beq(&back[1], &us[1]));
    }

    // --- fuel exhaustion fails rather than answering wrongly -----------------

    /// Fuel: `big`'s loose-bvar bound is 0, so the derived-word cutoff
    /// answers it at any fuel (with `big` itself); `let_t`'s is 1, so the walk
    /// really descends and fuel 1 runs out.
    #[test]
    fn t_fuel_exhaustion() {
        let pers: &PersTier = &PersTier::empty();
        let (mut st, fx) = fixture();
        let r = ok(instantiate1_fast(pers, &mut st, 1, &fx.big, &fx.cf, 0));
        assert!(r.eq2(&fx.big));
        assert!(instantiate1_fast(pers, &mut st, 1, &fx.let_t, &fx.cf, 0).is_err());
    }
}
