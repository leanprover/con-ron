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
//! `instantiate_list`, `lift_loose_bvars`, `reset_meta` and `rename_consts`
//! have none, here as there: a cutoff the original does not have needs its
//! own licence proved.
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
//! * **`f : NIdx → NIdx` is a trait bound**, as
//!   `con_ron_core::kernel::expr_ops::rename_consts`' `NameToName` is: §3.4
//!   forbids the closure.  It is the module's one higher-order argument and
//!   con-leche's own (`renameConsts (f : Name → Name)`).
//! * **A twin that cannot fail returns its value** (`arena::monad`'s note):
//!   `exprPtrBEq`, `LIdx.hasParam` and `Expr.hasLevelParam` read the derived
//!   column and nothing else.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{
    abs1_clear, abs1_get, abs1_set, bvar_b_clear, bvar_b_get, bvar_b_set, derived_e, derived_l,
    eidx_nat_key, fail, fvar_b_clear, fvar_b_get, fvar_b_set, inst1_clear, inst1_get, inst1_l_clear,
    inst1_l_get, inst1_l_set, inst1_set, inst_l_clear, inst_l_get, inst_l_set, inst_lp_clear,
    inst_lp_get, inst_lp_set, intern_e, intern_level, intern_levels, lift_clear, lift_get, lift_set,
    lower_clear, lower_get, lower_set, read_level, read_levels, read_names, rename_clear,
    rename_get, rename_set, reset_clear, reset_get, reset_set, view, AState, EIdxNat,
};
use crate::arena::store::ENodeView;
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::BinderMeta;
use con_ron_core::kernel::expr_ops::sub_nat;
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::Level;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;
use con_ron_core::kernel::prop_when::PropWhen;
use con_ron_core::ron::hashmap::{Dup, Eq2};

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
/// `"fuel exhausted: resetMeta"`, as code points.
const M_FUEL_RESET: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 115,
    101, 116, 77, 101, 116, 97,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: sizeB"`, as code points.
const M_FUEL_SIZE_B: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 115, 105, 122,
    101, 66,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: abstractRange"`, as code points.
const M_FUEL_ABS_RANGE: [u32; 29] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 98, 115, 116,
    114, 97, 99, 116, 82, 97, 110, 103, 101,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: sizeF"`, as code points.
const M_FUEL_SIZE_F: [u32; 21] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 115, 105, 122,
    101, 70,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: fvarLeaves"`, as code points.
const M_FUEL_FVAR_LEAVES: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 102, 118, 97,
    114, 76, 101, 97, 118, 101, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: wscopedB"`, as code points.
const M_FUEL_WSCOPED: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 115, 99,
    111, 112, 101, 100, 66,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: looseBVarsBounded"`, as code points.
const M_FUEL_LOOSE: [u32; 33] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 111, 111,
    115, 101, 66, 86, 97, 114, 115, 66, 111, 117, 110, 100, 101, 100,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: hasFvar"`, as code points.
const M_FUEL_HAS_FVAR: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 104, 97, 115, 70,
    118, 97, 114,
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
/// `"fuel exhausted: renameConsts"`, as code points.
const M_FUEL_RENAME: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 110,
    97, 109, 101, 67, 111, 110, 115, 116, 115,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: piResult"`, as code points.
const M_FUEL_PI_RESULT: [u32; 24] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 82,
    101, 115, 117, 108, 116,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: piArity"`, as code points.
const M_FUEL_PI_ARITY: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 65,
    114, 105, 116, 121,
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: resultSort"`, as code points.
const M_FUEL_RESULT_SORT: [u32; 26] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 114, 101, 115,
    117, 108, 116, 83, 111, 114, 116,
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
pub fn take_eidx(xs: &Vec<EIdx>, k: usize) -> Vec<EIdx> {
    eidx_copy_upto(xs, k, 0, Vec::new())
}

/// con-leche: none — `x :: xs` over a `Vec<EIdx>`
/// Lean conses in `O(1)` and shares the tail; a `Vec` has no cons, so the
/// tail is copied.  Every call site is a telescope arity, not a term size.
pub fn cons_eidx(a: &EIdx, xs: &Vec<EIdx>) -> Vec<EIdx> {
    let mut out: Vec<EIdx> = Vec::new();
    out.push(a.dup2());
    eidx_copy_upto(xs, xs.len(), 0, out)
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

/// con-leche: none — `List.append` over a `Vec<(Nat × EIdx)>`
/// `fvarLeaves`' `x ++ y`: the cursor recursion that copies `xs` onto `out`.
pub fn fvl_copy_from(
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

/// con-leche: none — `List.append` over a `Vec<(Nat × EIdx)>`
/// `x ++ y`.
pub fn fvl_append(x: &Vec<(u64, EIdx)>, y: &Vec<(u64, EIdx)>) -> Vec<(u64, EIdx)> {
    fvl_copy_from(y, 0, fvl_copy_from(x, 0, Vec::new()))
}

// ---------------------------------------------------------------------------
// `instantiate1` — `ExprOps.lean:29-45`, `:80-116`, `:182-184`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:97-158 instantiate1Go` —
/// replace `bvar d` by `v`, lowering loose `bvar`s above `d` by one.  The
/// derived-word cutoff comes first (`bvarB <= d`, read off the packed word in
/// `O(1)`); the five leaf kinds answer without touching the memo; everything
/// else probes the memo, runs the body one level down and inserts.
///
/// `else .bvar i` is `Ok(h.dup2())`: the node is already interned and
/// `denoteE` is injective, so rebuilding it yields the same handle.
pub fn instantiate1_go(
    st: &mut AState,
    v: &EIdx,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST1)))
    } else {
        let der: u64 = derived_e(st, h);
        let b: u64 = expr::bvar_of_data(der);
        if b < expr::sat_range() && b <= d {
            Ok(h.dup2())
        } else {
            match view(st, h) {
                Err(e) => Err(e),
                Ok(ENodeView::BVar(i)) => {
                    if i == d {
                        Ok(v.dup2())
                    } else if i > d {
                        intern_e(st, ENodeView::BVar(i - 1))
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
                    match inst1_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match instantiate1_go(st, v, fuel - 1, &f, d) {
                            Err(e) => Err(e),
                            Ok(f2) => match instantiate1_go(st, v, fuel - 1, &a, d) {
                                Err(e) => Err(e),
                                Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst1_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::Lam(ty, body, m)) => {
                    let k: EIdxNat = eidx_nat_key(h, d);
                    match inst1_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match instantiate1_go(st, v, fuel - 1, &ty, d) {
                            Err(e) => Err(e),
                            Ok(t) => match instantiate1_go(st, v, fuel - 1, &body, d + 1) {
                                Err(e) => Err(e),
                                Ok(b2) => match intern_e(st, ENodeView::Lam(t, b2, m)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst1_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::ForallE(ty, body, m)) => {
                    let k: EIdxNat = eidx_nat_key(h, d);
                    match inst1_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match instantiate1_go(st, v, fuel - 1, &ty, d) {
                            Err(e) => Err(e),
                            Ok(t) => match instantiate1_go(st, v, fuel - 1, &body, d + 1) {
                                Err(e) => Err(e),
                                Ok(b2) => match intern_e(st, ENodeView::ForallE(t, b2, m)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst1_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::LetE(ty, val, body)) => {
                    let k: EIdxNat = eidx_nat_key(h, d);
                    match inst1_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match instantiate1_go(st, v, fuel - 1, &ty, d) {
                            Err(e) => Err(e),
                            Ok(t) => match instantiate1_go(st, v, fuel - 1, &val, d) {
                                Err(e) => Err(e),
                                Ok(w) => match instantiate1_go(st, v, fuel - 1, &body, d + 1) {
                                    Err(e) => Err(e),
                                    Ok(b2) => match intern_e(st, ENodeView::LetE(t, w, b2)) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst1_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::Proj(n, i, sub)) => {
                    let k: EIdxNat = eidx_nat_key(h, d);
                    match inst1_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match instantiate1_go(st, v, fuel - 1, &sub, d) {
                            Err(e) => Err(e),
                            Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst1_set(st, k, &r);
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:163-167 instantiate1Fast` — the
/// top-level entry: `(instantiate1Go v {} e d).1`, i.e. the memo is fresh
/// before and dropped after, because it depends on the substituted term.
pub fn instantiate1_fast(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    v: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst1_clear(st);
    match instantiate1_go(st, v, fuel, e, d) {
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
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:214-217 instantiateList` (and
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
pub fn inst_list_cutoff(st: &AState, h: &EIdx, k: u64) -> bool {
    let der: u64 = derived_e(st, h);
    let b: u64 = expr::bvar_of_data(der);
    b < expr::sat_range() && b <= k
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:179-211 instantiateList` — the
/// unmemoized bulk instantiation.  con-leche's termination measure is
/// `(vs.length, sizeOf e)`; the single fuel counter decreases on both kinds of
/// recursive call, which is that order flattened.  **Two twins, not one**:
/// `instantiate_list_go`'s `bvar` arm calls this one, because that arm
/// recurses into the replacement with a *shorter* list and the memo is keyed
/// for the outer one.
pub fn instantiate_list(
    st: &mut AState,
    vs: &Vec<EIdx>,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LIST)))
    } else if inst_list_cutoff(st, h, d) {
        Ok(h.dup2())
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(j)) => {
                if j < d {
                    Ok(h.dup2())
                } else {
                    let n: u64 = vs.len() as u64;
                    if j - d < n {
                        let i: usize = (j - d) as usize;
                        let pre: Vec<EIdx> = take_eidx(vs, i);
                        let vi: EIdx = vs[i].dup2();
                        instantiate_list(st, &pre, fuel - 1, &vi, d)
                    } else {
                        intern_e(st, ENodeView::BVar(j - n))
                    }
                }
            }
            Ok(ENodeView::FVar(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::App(f, a)) => match instantiate_list(st, vs, fuel - 1, &f, d) {
                Err(e) => Err(e),
                Ok(f2) => match instantiate_list(st, vs, fuel - 1, &a, d) {
                    Err(e) => Err(e),
                    Ok(a2) => intern_e(st, ENodeView::App(f2, a2)),
                },
            },
            Ok(ENodeView::Lam(ty, body, m)) => match instantiate_list(st, vs, fuel - 1, &ty, d) {
                Err(e) => Err(e),
                Ok(t) => match instantiate_list(st, vs, fuel - 1, &body, d + 1) {
                    Err(e) => Err(e),
                    Ok(b) => intern_e(st, ENodeView::Lam(t, b, m)),
                },
            },
            Ok(ENodeView::ForallE(ty, body, m)) => {
                match instantiate_list(st, vs, fuel - 1, &ty, d) {
                    Err(e) => Err(e),
                    Ok(t) => match instantiate_list(st, vs, fuel - 1, &body, d + 1) {
                        Err(e) => Err(e),
                        Ok(b) => intern_e(st, ENodeView::ForallE(t, b, m)),
                    },
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                match instantiate_list(st, vs, fuel - 1, &ty, d) {
                    Err(e) => Err(e),
                    Ok(t) => match instantiate_list(st, vs, fuel - 1, &val, d) {
                        Err(e) => Err(e),
                        Ok(w) => match instantiate_list(st, vs, fuel - 1, &body, d + 1) {
                            Err(e) => Err(e),
                            Ok(b) => intern_e(st, ENodeView::LetE(t, w, b)),
                        },
                    },
                }
            }
            Ok(ENodeView::Proj(n, i, sub)) => match instantiate_list(st, vs, fuel - 1, &sub, d) {
                Err(e) => Err(e),
                Ok(u) => intern_e(st, ENodeView::Proj(n, i, u)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:216-269 instantiateListGo` —
/// the memoized bulk instantiation.  The `bvar` arm delegates to the pure walk
/// above, exactly as con-leche's does.
pub fn instantiate_list_go(
    st: &mut AState,
    vs: &Vec<EIdx>,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LIST)))
    } else if inst_list_cutoff(st, h, d) {
        Ok(h.dup2())
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => instantiate_list(st, vs, fuel - 1, h, d),
            Ok(ENodeView::FVar(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::App(f, a)) => {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst_l_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match instantiate_list_go(st, vs, fuel - 1, &f, d) {
                        Err(e) => Err(e),
                        Ok(f2) => match instantiate_list_go(st, vs, fuel - 1, &a, d) {
                            Err(e) => Err(e),
                            Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_l_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Lam(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst_l_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match instantiate_list_go(st, vs, fuel - 1, &ty, d) {
                        Err(e) => Err(e),
                        Ok(t) => match instantiate_list_go(st, vs, fuel - 1, &body, d + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::Lam(t, b, m)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_l_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::ForallE(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst_l_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match instantiate_list_go(st, vs, fuel - 1, &ty, d) {
                        Err(e) => Err(e),
                        Ok(t) => match instantiate_list_go(st, vs, fuel - 1, &body, d + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::ForallE(t, b, m)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_l_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst_l_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match instantiate_list_go(st, vs, fuel - 1, &ty, d) {
                        Err(e) => Err(e),
                        Ok(t) => match instantiate_list_go(st, vs, fuel - 1, &val, d) {
                            Err(e) => Err(e),
                            Ok(w) => match instantiate_list_go(st, vs, fuel - 1, &body, d + 1) {
                                Err(e) => Err(e),
                                Ok(b) => match intern_e(st, ENodeView::LetE(t, w, b)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst_l_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Proj(n, i, sub)) => {
                let k: EIdxNat = eidx_nat_key(h, d);
                match inst_l_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match instantiate_list_go(st, vs, fuel - 1, &sub, d) {
                        Err(e) => Err(e),
                        Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                inst_l_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:273-278 instantiateListFast` —
/// the top-level entry.
pub fn instantiate_list_fast(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    vs: &Vec<EIdx>,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst_l_clear(st);
    match instantiate_list_go(st, vs, fuel, e, d) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:285-338 liftLooseBVarsGo` —
/// bump every loose bound variable `>= cutoff` by `amount`.
pub fn lift_loose_bvars_go(
    st: &mut AState,
    amount: u64,
    fuel: u64,
    h: &EIdx,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LIFT)))
    } else if inst_list_cutoff(st, h, c) {
        Ok(h.dup2())
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(i)) => {
                if i >= c {
                    intern_e(st, ENodeView::BVar(i + amount))
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
                    None => match lift_loose_bvars_go(st, amount, fuel - 1, &a, c) {
                        Err(e) => Err(e),
                        Ok(a2) => match lift_loose_bvars_go(st, amount, fuel - 1, &b, c) {
                            Err(e) => Err(e),
                            Ok(b2) => match intern_e(st, ENodeView::App(a2, b2)) {
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
                    None => match lift_loose_bvars_go(st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(st, amount, fuel - 1, &body, c + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::Lam(t, b, m)) {
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
                    None => match lift_loose_bvars_go(st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(st, amount, fuel - 1, &body, c + 1) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::ForallE(t, b, m)) {
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
                    None => match lift_loose_bvars_go(st, amount, fuel - 1, &ty, c) {
                        Err(e) => Err(e),
                        Ok(t) => match lift_loose_bvars_go(st, amount, fuel - 1, &val, c) {
                            Err(e) => Err(e),
                            Ok(w) => {
                                match lift_loose_bvars_go(st, amount, fuel - 1, &body, c + 1) {
                                    Err(e) => Err(e),
                                    Ok(b) => match intern_e(st, ENodeView::LetE(t, w, b)) {
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
                    None => match lift_loose_bvars_go(st, amount, fuel - 1, &sub, c) {
                        Err(e) => Err(e),
                        Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:342-346 liftLooseBVarsFast` —
/// the top-level entry.
pub fn lift_loose_bvars_fast(
    st: &mut AState,
    fuel: u64,
    amount: u64,
    c: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    lift_clear(st);
    match lift_loose_bvars_go(st, amount, fuel, e, c) {
        Err(er) => Err(er),
        Ok(r) => {
            lift_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `resetMeta` — `ExprOps.lean:552-559`, `:579-615`, `:687-688`
//
// The memo has no cursor in con-leche; the twin keys it at `0` so that every
// handle-valued memo has one shape, and so does this.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:357-417 resetMetaGo` — reset
/// every binder's prop-ness datum to the parse placeholder; the `fvar`
/// annotation is descended into.
pub fn reset_meta_go(st: &mut AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_RESET)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::FVar(i, ty)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match intern_e(st, ENodeView::FVar(i, t)) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                reset_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
            Ok(ENodeView::App(f, a)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &f) {
                        Err(e) => Err(e),
                        Ok(f2) => match reset_meta_go(st, fuel - 1, &a) {
                            Err(e) => Err(e),
                            Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    reset_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Lam(ty, body, _)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match reset_meta_go(st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(b) => {
                                let m: BinderMeta = expr::binder_meta(prop_when::never());
                                match intern_e(st, ENodeView::Lam(t, b, m)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        reset_set(st, k, &r);
                                        Ok(r)
                                    }
                                }
                            }
                        },
                    },
                }
            }
            Ok(ENodeView::ForallE(ty, body, _)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match reset_meta_go(st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(b) => {
                                let m: BinderMeta = expr::binder_meta(prop_when::never());
                                match intern_e(st, ENodeView::ForallE(t, b, m)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        reset_set(st, k, &r);
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
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match reset_meta_go(st, fuel - 1, &val) {
                            Err(e) => Err(e),
                            Ok(w) => match reset_meta_go(st, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b) => match intern_e(st, ENodeView::LetE(t, w, b)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        reset_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Proj(n, i, sub)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match reset_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match reset_meta_go(st, fuel - 1, &sub) {
                        Err(e) => Err(e),
                        Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                reset_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:421-425 resetMetaFast` — the
/// top-level entry.
pub fn reset_meta_fast(st: &mut AState, fuel: u64, e: &EIdx) -> Result<EIdx, CheckError> {
    reset_clear(st);
    match reset_meta_go(st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            reset_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// The measures and the scope predicates
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:432-452 sizeB` — node count
/// with `fvar` a leaf (its annotated type ignored): the termination measure
/// for recursion into instantiated binder bodies.
pub fn size_b(st: &AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_SIZE_B)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(1),
            Ok(ENodeView::FVar(_, _)) => Ok(1),
            Ok(ENodeView::Sort(_)) => Ok(1),
            Ok(ENodeView::Const(_, _)) => Ok(1),
            Ok(ENodeView::Lit(_)) => Ok(1),
            Ok(ENodeView::App(f, a)) => match size_b(st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(x) => match size_b(st, fuel - 1, &a) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::Lam(ty, body, _)) => match size_b(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_b(st, fuel - 1, &body) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::ForallE(ty, body, _)) => match size_b(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_b(st, fuel - 1, &body) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::LetE(ty, val, body)) => match size_b(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_b(st, fuel - 1, &val) {
                    Err(e) => Err(e),
                    Ok(y) => match size_b(st, fuel - 1, &body) {
                        Err(e) => Err(e),
                        Ok(z) => Ok(x + y + z + 1),
                    },
                },
            },
            Ok(ENodeView::Proj(_, _, sub)) => match size_b(st, fuel - 1, &sub) {
                Err(e) => Err(e),
                Ok(x) => Ok(x + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:457-487 abstractRange` — bulk
/// abstraction: close `k` binders in one traversal.  Unmemoized in con-leche,
/// in the twin and here.
pub fn abstract_range(
    st: &mut AState,
    fuel: u64,
    h: &EIdx,
    d: u64,
    k: u64,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ABS_RANGE)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
            Ok(ENodeView::FVar(idx, _)) => {
                if d <= idx && idx < d + k {
                    intern_e(st, ENodeView::BVar(c + (d + k - 1 - idx)))
                } else {
                    Ok(h.dup2())
                }
            }
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::App(f, a)) => match abstract_range(st, fuel - 1, &f, d, k, c) {
                Err(e) => Err(e),
                Ok(f2) => match abstract_range(st, fuel - 1, &a, d, k, c) {
                    Err(e) => Err(e),
                    Ok(a2) => intern_e(st, ENodeView::App(f2, a2)),
                },
            },
            Ok(ENodeView::Lam(ty, body, m)) => match abstract_range(st, fuel - 1, &ty, d, k, c) {
                Err(e) => Err(e),
                Ok(t) => match abstract_range(st, fuel - 1, &body, d, k, c + 1) {
                    Err(e) => Err(e),
                    Ok(b) => intern_e(st, ENodeView::Lam(t, b, m)),
                },
            },
            Ok(ENodeView::ForallE(ty, body, m)) => {
                match abstract_range(st, fuel - 1, &ty, d, k, c) {
                    Err(e) => Err(e),
                    Ok(t) => match abstract_range(st, fuel - 1, &body, d, k, c + 1) {
                        Err(e) => Err(e),
                        Ok(b) => intern_e(st, ENodeView::ForallE(t, b, m)),
                    },
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => match abstract_range(st, fuel - 1, &ty, d, k, c) {
                Err(e) => Err(e),
                Ok(t) => match abstract_range(st, fuel - 1, &val, d, k, c) {
                    Err(e) => Err(e),
                    Ok(w) => match abstract_range(st, fuel - 1, &body, d, k, c + 1) {
                        Err(e) => Err(e),
                        Ok(b) => intern_e(st, ENodeView::LetE(t, w, b)),
                    },
                },
            },
            Ok(ENodeView::Proj(n, i, sub)) => match abstract_range(st, fuel - 1, &sub, d, k, c) {
                Err(e) => Err(e),
                Ok(u) => intern_e(st, ENodeView::Proj(n, i, u)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:491-514 sizeF` — full node
/// count, `fvar` annotations included.
pub fn size_f(st: &AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_SIZE_F)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(1),
            Ok(ENodeView::Sort(_)) => Ok(1),
            Ok(ENodeView::Const(_, _)) => Ok(1),
            Ok(ENodeView::Lit(_)) => Ok(1),
            Ok(ENodeView::FVar(_, ty)) => match size_f(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => Ok(x + 1),
            },
            Ok(ENodeView::App(f, a)) => match size_f(st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(x) => match size_f(st, fuel - 1, &a) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::Lam(ty, body, _)) => match size_f(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_f(st, fuel - 1, &body) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::ForallE(ty, body, _)) => match size_f(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_f(st, fuel - 1, &body) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(x + y + 1),
                },
            },
            Ok(ENodeView::LetE(ty, val, body)) => match size_f(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match size_f(st, fuel - 1, &val) {
                    Err(e) => Err(e),
                    Ok(y) => match size_f(st, fuel - 1, &body) {
                        Err(e) => Err(e),
                        Ok(z) => Ok(x + y + z + 1),
                    },
                },
            },
            Ok(ENodeView::Proj(_, _, sub)) => match size_f(st, fuel - 1, &sub) {
                Err(e) => Err(e),
                Ok(x) => Ok(x + 1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:518-539 fvarLeaves` — all
/// reachable `fvar` leaves, hereditarily through their annotations.  Lean's
/// `::` and `++` are the copying combinators above.
pub fn fvar_leaves(
    st: &AState,
    fuel: u64,
    h: &EIdx,
) -> Result<Vec<(u64, EIdx)>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_FVAR_LEAVES)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::FVar(idx, ty)) => match fvar_leaves(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(rest) => {
                    let mut out: Vec<(u64, EIdx)> = Vec::new();
                    out.push((idx, ty.dup2()));
                    Ok(fvl_copy_from(&rest, 0, out))
                }
            },
            Ok(ENodeView::App(f, a)) => match fvar_leaves(st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(x) => match fvar_leaves(st, fuel - 1, &a) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(fvl_append(&x, &y)),
                },
            },
            Ok(ENodeView::Lam(ty, b, _)) => match fvar_leaves(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match fvar_leaves(st, fuel - 1, &b) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(fvl_append(&x, &y)),
                },
            },
            Ok(ENodeView::ForallE(ty, b, _)) => match fvar_leaves(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => match fvar_leaves(st, fuel - 1, &b) {
                    Err(e) => Err(e),
                    Ok(y) => Ok(fvl_append(&x, &y)),
                },
            },
            Ok(ENodeView::LetE(t, v, b)) => match fvar_leaves(st, fuel - 1, &t) {
                Err(e) => Err(e),
                Ok(x) => match fvar_leaves(st, fuel - 1, &v) {
                    Err(e) => Err(e),
                    Ok(y) => match fvar_leaves(st, fuel - 1, &b) {
                        Err(e) => Err(e),
                        Ok(z) => Ok(fvl_append(&fvl_append(&x, &y), &z)),
                    },
                },
            },
            Ok(ENodeView::Proj(_, _, sub)) => fvar_leaves(st, fuel - 1, &sub),
            Ok(ENodeView::BVar(_)) => Ok(Vec::new()),
            Ok(ENodeView::Sort(_)) => Ok(Vec::new()),
            Ok(ENodeView::Const(_, _)) => Ok(Vec::new()),
            Ok(ENodeView::Lit(_)) => Ok(Vec::new()),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:545-567 wscopedB` — the scope
/// check: every reachable `fvar` index is below `d`, hereditarily through
/// annotations.  con-leche's `&&` is short-circuiting, and so is the explicit
/// `if` chain here.
pub fn wscoped_b(st: &AState, fuel: u64, d: u64, h: &EIdx) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_WSCOPED)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::FVar(idx, ty)) => {
                if idx < d {
                    wscoped_b(st, fuel - 1, idx, &ty)
                } else {
                    Ok(false)
                }
            }
            Ok(ENodeView::App(f, a)) => match wscoped_b(st, fuel - 1, d, &f) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        wscoped_b(st, fuel - 1, d, &a)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::Lam(ty, body, _)) => match wscoped_b(st, fuel - 1, d, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        wscoped_b(st, fuel - 1, d, &body)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::ForallE(ty, body, _)) => match wscoped_b(st, fuel - 1, d, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        wscoped_b(st, fuel - 1, d, &body)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::LetE(ty, val, body)) => match wscoped_b(st, fuel - 1, d, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        match wscoped_b(st, fuel - 1, d, &val) {
                            Err(e) => Err(e),
                            Ok(y) => {
                                if y {
                                    wscoped_b(st, fuel - 1, d, &body)
                                } else {
                                    Ok(false)
                                }
                            }
                        }
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::Proj(_, _, sub)) => wscoped_b(st, fuel - 1, d, &sub),
            Ok(ENodeView::BVar(_)) => Ok(true),
            Ok(ENodeView::Sort(_)) => Ok(true),
            Ok(ENodeView::Const(_, _)) => Ok(true),
            Ok(ENodeView::Lit(_)) => Ok(true),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:573-592 looseBVarsBounded` —
/// the pure walk.  It is the SPECIFICATION; what executes is the `O(1)` field
/// read `loose_bvars_bounded_fast` below, exactly as in con-leche (the
/// `@[csimp]` pair).
pub fn loose_bvars_bounded(
    st: &AState,
    fuel: u64,
    k: u64,
    h: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LOOSE)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(i)) => Ok(i < k),
            Ok(ENodeView::FVar(_, _)) => Ok(true),
            Ok(ENodeView::Sort(_)) => Ok(true),
            Ok(ENodeView::Const(_, _)) => Ok(true),
            Ok(ENodeView::Lit(_)) => Ok(true),
            Ok(ENodeView::App(f, a)) => match loose_bvars_bounded(st, fuel - 1, k, &f) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        loose_bvars_bounded(st, fuel - 1, k, &a)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::Lam(ty, body, _)) => match loose_bvars_bounded(st, fuel - 1, k, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        loose_bvars_bounded(st, fuel - 1, k + 1, &body)
                    } else {
                        Ok(false)
                    }
                }
            },
            Ok(ENodeView::ForallE(ty, body, _)) => {
                match loose_bvars_bounded(st, fuel - 1, k, &ty) {
                    Err(e) => Err(e),
                    Ok(x) => {
                        if x {
                            loose_bvars_bounded(st, fuel - 1, k + 1, &body)
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                match loose_bvars_bounded(st, fuel - 1, k, &ty) {
                    Err(e) => Err(e),
                    Ok(x) => {
                        if x {
                            match loose_bvars_bounded(st, fuel - 1, k, &val) {
                                Err(e) => Err(e),
                                Ok(y) => {
                                    if y {
                                        loose_bvars_bounded(st, fuel - 1, k + 1, &body)
                                    } else {
                                        Ok(false)
                                    }
                                }
                            }
                        } else {
                            Ok(false)
                        }
                    }
                }
            }
            Ok(ENodeView::Proj(_, _, sub)) => loose_bvars_bounded(st, fuel - 1, k, &sub),
        }
    }
}

// ---------------------------------------------------------------------------
// The one-node readers: each is a single `view` and a test, no recursion
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:600-603 isLam` — is the
/// expression a λ?
pub fn is_lam(st: &AState, h: &EIdx) -> Result<bool, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lam(_, _, _)) => Ok(true),
        Ok(_) => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:608-611 lamPw` — a λ node's
/// prop-ness annotation, `none` off λs.  `PropWhen` is a value and not a term,
/// so it crosses the signature unchanged.
pub fn lam_pw(st: &AState, h: &EIdx) -> Result<Option<PropWhen>, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::Lam(_, _, m)) => Ok(Some(m.pw)),
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:615-618 forallPw` — the ∀ twin
/// of `lam_pw`.
pub fn forall_pw(st: &AState, h: &EIdx) -> Result<Option<PropWhen>, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::ForallE(_, _, m)) => Ok(Some(m.pw)),
        Ok(_) => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:622-639 hasFvar` — the pure
/// walk; what executes is `has_fvar_fast` below (the fvar-range field read).
pub fn has_fvar(st: &AState, fuel: u64, h: &EIdx) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_HAS_FVAR)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(false),
            Ok(ENodeView::Sort(_)) => Ok(false),
            Ok(ENodeView::Const(_, _)) => Ok(false),
            Ok(ENodeView::Lit(_)) => Ok(false),
            Ok(ENodeView::FVar(_, _)) => Ok(true),
            Ok(ENodeView::App(f, a)) => match has_fvar(st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        Ok(true)
                    } else {
                        has_fvar(st, fuel - 1, &a)
                    }
                }
            },
            Ok(ENodeView::Lam(ty, body, _)) => match has_fvar(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        Ok(true)
                    } else {
                        has_fvar(st, fuel - 1, &body)
                    }
                }
            },
            Ok(ENodeView::ForallE(ty, body, _)) => match has_fvar(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        Ok(true)
                    } else {
                        has_fvar(st, fuel - 1, &body)
                    }
                }
            },
            Ok(ENodeView::LetE(ty, val, body)) => match has_fvar(st, fuel - 1, &ty) {
                Err(e) => Err(e),
                Ok(x) => {
                    if x {
                        Ok(true)
                    } else {
                        match has_fvar(st, fuel - 1, &val) {
                            Err(e) => Err(e),
                            Ok(y) => {
                                if y {
                                    Ok(true)
                                } else {
                                    has_fvar(st, fuel - 1, &body)
                                }
                            }
                        }
                    }
                }
            },
            Ok(ENodeView::Proj(_, _, sub)) => has_fvar(st, fuel - 1, &sub),
        }
    }
}

// ---------------------------------------------------------------------------
// Application spines
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:645-650 getAppFn` — the head of
/// an application spine.
pub fn get_app_fn(st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_APP_FN)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::App(f, _)) => get_app_fn(st, fuel - 1, &f),
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:654-661 getAppArgs` — the
/// arguments of an application spine, outermost last.  Lean's `as ++ [a]` is a
/// `push` here, which is the same list in one pass.
pub fn get_app_args(st: &AState, fuel: u64, h: &EIdx) -> Result<Vec<EIdx>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_APP_ARGS)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::App(f, a)) => match get_app_args(st, fuel - 1, &f) {
                Err(e) => Err(e),
                Ok(args) => {
                    let mut out: Vec<EIdx> = args;
                    out.push(a);
                    Ok(out)
                }
            },
            Ok(_) => Ok(Vec::new()),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:665-669 mkAppN` — apply to a
/// list of arguments.  Structural on the list, so no fuel; the `i = 0` wrapper
/// of the cursor recursion below.
pub fn mk_app_n(st: &mut AState, f: &EIdx, args: &Vec<EIdx>) -> Result<EIdx, CheckError> {
    mk_app_n_from(st, f, args, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:665-669 mkAppN` — the cursor
/// recursion behind `mk_app_n`.
pub fn mk_app_n_from(
    st: &mut AState,
    f: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<EIdx, CheckError> {
    if i >= args.len() {
        Ok(f.dup2())
    } else {
        match intern_e(st, ENodeView::App(f.dup2(), args[i].dup2())) {
            Err(e) => Err(e),
            Ok(g) => mk_app_n_from(st, &g, args, i + 1),
        }
    }
}

// ---------------------------------------------------------------------------
// `renameConsts` — `ExprOps.lean:930-956`, `:999-1036`, `:1109-1111`
// ---------------------------------------------------------------------------

/// con-leche: none — replaces the `f : NIdx → NIdx` argument of `renameConsts`
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:686 renameConstsGo` — the
/// one-method trait that stands for a Lean function argument (DESIGN.md §3.4
/// forbids closures), exactly as `con_ron_core::kernel::expr_ops`'s
/// `NameToName` does for con-leche's `f : Name → Name`.  Aeneas renders it as
/// a one-field structure threaded as a dictionary.
///
/// The renaming is on name HANDLES, not on names: the twin's census column
/// says so, and it is what the one call site — P4d's modeled-block contract,
/// whose map is a table lookup — can supply.
pub trait NIdxToNIdx {
    /// con-leche: none — the `f` of `renameConsts f`
    fn rename(&self, n: &NIdx) -> NIdx;
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
/// con-leche: ConLeche/Kernel/ExprOps.lean:999-1036 renameConstsGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:686-746 renameConstsGo` —
/// rename constants throughout; levels, binders and `proj` struct names
/// untouched (con-leche's task #175 wiring W5).  The `const` arm is a leaf
/// here as it is in con-leche — it rebuilds one node and does not recurse —
/// so it is not memoized.
pub fn rename_consts_go<F>(
    st: &mut AState,
    f: &F,
    fuel: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError>
where
    F: NIdxToNIdx,
{
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_RENAME)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
            Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
            Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
            Ok(ENodeView::Const(n, us)) => {
                let n2: NIdx = f.rename(&n);
                intern_e(st, ENodeView::Const(n2, us))
            }
            Ok(ENodeView::FVar(i, ty)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match intern_e(st, ENodeView::FVar(i, t)) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                rename_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
            Ok(ENodeView::App(a, b)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &a) {
                        Err(e) => Err(e),
                        Ok(a2) => match rename_consts_go(st, f, fuel - 1, &b) {
                            Err(e) => Err(e),
                            Ok(b2) => match intern_e(st, ENodeView::App(a2, b2)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    rename_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Lam(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match rename_consts_go(st, f, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::Lam(t, b, m)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    rename_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::ForallE(ty, body, m)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match rename_consts_go(st, f, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(b) => match intern_e(st, ENodeView::ForallE(t, b, m)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    rename_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::LetE(ty, val, body)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(t) => match rename_consts_go(st, f, fuel - 1, &val) {
                            Err(e) => Err(e),
                            Ok(w) => match rename_consts_go(st, f, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b) => match intern_e(st, ENodeView::LetE(t, w, b)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        rename_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    },
                }
            }
            Ok(ENodeView::Proj(n, i, sub)) => {
                let k: EIdxNat = eidx_nat_key(h, 0);
                match rename_get(st, &k) {
                    Some(r) => Ok(r),
                    None => match rename_consts_go(st, f, fuel - 1, &sub) {
                        Err(e) => Err(e),
                        Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
                            Err(e) => Err(e),
                            Ok(r) => {
                                rename_set(st, k, &r);
                                Ok(r)
                            }
                        },
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1109-1111 renameConstsFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:750-754 renameConstsFast` — the
/// top-level entry.
pub fn rename_consts_fast<F>(
    st: &mut AState,
    fuel: u64,
    f: &F,
    e: &EIdx,
) -> Result<EIdx, CheckError>
where
    F: NIdxToNIdx,
{
    rename_clear(st);
    match rename_consts_go(st, f, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            rename_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// Telescopes
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:1118-1124 stripLams
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:760-768 stripLams` — strip `k`
/// leading λs.  The recursion is structural on `k`, so no fuel; Lean's
/// `(ty, m) :: p.1` is `cons_binder`.
pub fn strip_lams(
    st: &AState,
    k: u64,
    h: &EIdx,
) -> Result<Option<(Vec<(EIdx, BinderMeta)>, EIdx)>, CheckError> {
    if k == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(ty, b, m)) => match strip_lams(st, k - 1, &b) {
                Err(e) => Err(e),
                Ok(Some(p)) => Ok(Some((cons_binder(&ty, &m, &p.0), p.1))),
                Ok(None) => Ok(None),
            },
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1126-1132 stripPis
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:772-780 stripPis` — strip `k`
/// leading `∀`s.
pub fn strip_pis(
    st: &AState,
    k: u64,
    h: &EIdx,
) -> Result<Option<(Vec<(EIdx, BinderMeta)>, EIdx)>, CheckError> {
    if k == 0 {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, b, m)) => match strip_pis(st, k - 1, &b) {
                Err(e) => Err(e),
                Ok(Some(p)) => Ok(Some((cons_binder(&ty, &m, &p.0), p.1))),
                Ok(None) => Ok(None),
            },
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1134-1138 piResult
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:784-789 piResult` — the body of
/// a syntactic `∀`-telescope.
pub fn pi_result(st: &AState, fuel: u64, h: &EIdx) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PI_RESULT)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(_, b, _)) => pi_result(st, fuel - 1, &b),
            Ok(_) => Ok(h.dup2()),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1140-1144 instPis
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:794-801 instPis` — instantiate
/// a `∀`-telescope with arguments, in order.  Structural on the argument list;
/// the fuel is the one `instantiate1_fast` needs.  The `i = 0` wrapper of the
/// cursor recursion below.
pub fn inst_pis(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
) -> Result<Option<EIdx>, CheckError> {
    inst_pis_from(st, fuel, e, args, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1140-1144 instPis
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:794-801 instPis` — the cursor
/// recursion behind `inst_pis`.
pub fn inst_pis_from(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    args: &Vec<EIdx>,
    i: usize,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(e.dup2()))
    } else {
        match view(st, e) {
            Err(er) => Err(er),
            Ok(ENodeView::ForallE(_, body, _)) => {
                let a: EIdx = args[i].dup2();
                match instantiate1_fast(st, fuel, &body, &a, 0) {
                    Err(er) => Err(er),
                    Ok(b) => inst_pis_from(st, fuel, &b, args, i + 1),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1146-1154 instPisAt
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:807-816 instPisAt` —
/// instantiate the leading `∀`-binders at the given arguments, returning each
/// binder's domain with the fully instantiated residual.  con-leche's
/// `Option.map` over a pure body is an explicit `match`, as it is in the twin:
/// the body is monadic.
pub fn inst_pis_at(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    inst_pis_at_from(st, fuel, args, 0, h)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1146-1154 instPisAt
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:807-816 instPisAt` — the cursor
/// recursion behind `inst_pis_at`.  The domain is consed on the way OUT, as
/// the twin conses it, and not pushed on the way in.
pub fn inst_pis_at_from(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if i >= args.len() {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => {
                let a: EIdx = args[i].dup2();
                match instantiate1_fast(st, fuel, &body, &a, 0) {
                    Err(e) => Err(e),
                    Ok(b) => match inst_pis_at_from(st, fuel, args, i + 1, &b) {
                        Err(e) => Err(e),
                        Ok(Some(p)) => Ok(Some((cons_eidx(&dom, &p.0), p.1))),
                        Ok(None) => Ok(None),
                    },
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1156-1162 instLamsAt
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:820-829 instLamsAt` —
/// `inst_pis_at` for λ-binders.
pub fn inst_lams_at(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    inst_lams_at_from(st, fuel, args, 0, h)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1156-1162 instLamsAt
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:820-829 instLamsAt` — the
/// cursor recursion behind `inst_lams_at`.
pub fn inst_lams_at_from(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if i >= args.len() {
        Ok(Some((Vec::new(), h.dup2())))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(dom, body, _)) => {
                let a: EIdx = args[i].dup2();
                match instantiate1_fast(st, fuel, &body, &a, 0) {
                    Err(e) => Err(e),
                    Ok(b) => match inst_lams_at_from(st, fuel, args, i + 1, &b) {
                        Err(e) => Err(e),
                        Ok(Some(p)) => Ok(Some((cons_eidx(&dom, &p.0), p.1))),
                        Ok(None) => Ok(None),
                    },
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1179-1188 instPisAtFGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:834-847 instPisAtFGo` — the
/// core of `inst_pis_at_f`: `acc` holds the pending substitutions, innermost
/// binder first, so each domain receives them in one `instantiateList` pass
/// instead of one `instantiate1` pass per argument.
///
/// **The domain is instantiated AFTER the recursive call**, as the twin does
/// it (`con_ron_core::kernel::expr_ops::inst_pis_at_f_go` does it before,
/// which is fine for pure `Expr`s and is not fine here: interning in a
/// different order gives the same denotation but different handles, and this
/// port is in lockstep with the twin at the handle).
pub fn inst_pis_at_f_go(
    st: &mut AState,
    fuel: u64,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if i >= args.len() {
        match instantiate_list_fast(st, fuel, h, acc, 0) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some((Vec::new(), r))),
        }
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(dom, body, _)) => {
                let acc2: Vec<EIdx> = cons_eidx(&args[i], acc);
                match inst_pis_at_f_go(st, fuel, &acc2, args, i + 1, &body) {
                    Err(e) => Err(e),
                    Ok(Some(p)) => match instantiate_list_fast(st, fuel, &dom, acc, 0) {
                        Err(e) => Err(e),
                        Ok(d) => Ok(Some((cons_eidx(&d, &p.0), p.1))),
                    },
                    Ok(None) => Ok(None),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1190-1194 instPisAtF
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:851-855 instPisAtF` — one-pass
/// `inst_pis_at`, with the cited fall-back to the sequential definition when
/// the raw telescope is shorter than the argument list.
pub fn inst_pis_at_f(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    e: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    let acc: Vec<EIdx> = Vec::new();
    match inst_pis_at_f_go(st, fuel, &acc, args, 0, e) {
        Err(er) => Err(er),
        Ok(Some(r)) => Ok(Some(r)),
        Ok(None) => inst_pis_at(st, fuel, args, e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1196-1202 instLamsAtFGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:859-872 instLamsAtFGo` — the λ
/// counterpart of `inst_pis_at_f_go`.
pub fn inst_lams_at_f_go(
    st: &mut AState,
    fuel: u64,
    acc: &Vec<EIdx>,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    if i >= args.len() {
        match instantiate_list_fast(st, fuel, h, acc, 0) {
            Err(e) => Err(e),
            Ok(r) => Ok(Some((Vec::new(), r))),
        }
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::Lam(dom, body, _)) => {
                let acc2: Vec<EIdx> = cons_eidx(&args[i], acc);
                match inst_lams_at_f_go(st, fuel, &acc2, args, i + 1, &body) {
                    Err(e) => Err(e),
                    Ok(Some(p)) => match instantiate_list_fast(st, fuel, &dom, acc, 0) {
                        Err(e) => Err(e),
                        Ok(d) => Ok(Some((cons_eidx(&d, &p.0), p.1))),
                    },
                    Ok(None) => Ok(None),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1204-1208 instLamsAtF
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:876-880 instLamsAtF` — one-pass
/// `inst_lams_at`.
pub fn inst_lams_at_f(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    e: &EIdx,
) -> Result<Option<(Vec<EIdx>, EIdx)>, CheckError> {
    let acc: Vec<EIdx> = Vec::new();
    match inst_lams_at_f_go(st, fuel, &acc, args, 0, e) {
        Err(er) => Err(er),
        Ok(Some(r)) => Ok(Some(r)),
        Ok(None) => inst_lams_at(st, fuel, args, e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1210-1215 fvarTypeD
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:884-887 fvarTypeD` — the type
/// annotation of a free-variable leaf (the expression itself otherwise).
pub fn fvar_type_d(st: &AState, h: &EIdx) -> Result<EIdx, CheckError> {
    match view(st, h) {
        Err(e) => Err(e),
        Ok(ENodeView::FVar(_, ty)) => Ok(ty),
        Ok(_) => Ok(h.dup2()),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1217-1225 instSpine
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:891-895 instSpine` —
/// instantiate a telescope-context expression at an argument spine.
pub fn inst_spine(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    t: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    inst_spine_from(st, fuel, args, 0, t, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1217-1225 instSpine
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:891-895 instSpine` — the cursor
/// recursion behind `inst_spine`.  `t - 1` is Lean's truncating subtraction,
/// hence `sub_nat` (the cited arm carries no guard).
pub fn inst_spine_from(
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
        match instantiate1_fast(st, fuel, e, &a, t) {
            Err(er) => Err(er),
            Ok(e2) => inst_spine_from(st, fuel, args, i + 1, sub_nat(t, 1), &e2),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1227-1242 recRulePlain
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:900-905 bvarRange` — the
/// comparand `(List.range cnP).map (fun k => Expr.bvar (mI - 1 - k))`,
/// interned.  Structural on the count, so no fuel; `mI - 1 - k` is Lean's
/// truncating subtraction, hence `sub_nat`.
pub fn bvar_range(
    st: &mut AState,
    m_i: u64,
    n: u64,
    k: u64,
) -> Result<Vec<EIdx>, CheckError> {
    if n == 0 {
        Ok(Vec::new())
    } else {
        match intern_e(st, ENodeView::BVar(sub_nat(sub_nat(m_i, 1), k))) {
            Err(e) => Err(e),
            Ok(b) => match bvar_range(st, m_i, n - 1, k + 1) {
                Err(e) => Err(e),
                Ok(rest) => Ok(cons_eidx(&b, &rest)),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1227-1242 recRulePlain
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:912-924 recRulePlain` — a
/// recursor rule is canonical when its constructor's parameters are exactly
/// the recursor's own leading arguments.  The `==` on the argument prefix is
/// index equality (the `==` inventory's line 1240): exactness makes it the
/// structural comparison con-leche writes.  The cited
/// `decide (cnP ≤ rP) && decide (rP ≤ mI)` is an `if` nest (task #3's pattern
/// 9).
pub fn rec_rule_plain(
    st: &mut AState,
    fuel: u64,
    rec_ty: &EIdx,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
) -> Result<bool, CheckError> {
    if cn_p <= r_p && r_p <= m_i {
        match strip_pis(st, m_i, rec_ty) {
            Err(e) => Err(e),
            Ok(None) => Ok(false),
            Ok(Some(p)) => match view(st, &p.1) {
                Err(e) => Err(e),
                Ok(ENodeView::ForallE(dom, _, _)) => match get_app_args(st, fuel, &dom) {
                    Err(e) => Err(e),
                    Ok(args) => match bvar_range(st, m_i, cn_p, 0) {
                        Err(e) => Err(e),
                        Ok(want) => Ok(eidx_take_beq(&args, &want)),
                    },
                },
                Ok(_) => Ok(false),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1244-1259 pisToLams
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:930-940 pisToLams` — convert
/// the first `k` `∀`-binders into λ-binders over a body; the copied binder
/// metadata keeps only the display info, so the result carries the parse
/// placeholder and every consumer must annotate it.
pub fn pis_to_lams(
    st: &mut AState,
    k: u64,
    h: &EIdx,
    body: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(body.dup2()))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, rest, _)) => match pis_to_lams(st, k - 1, &rest, body) {
                Err(e) => Err(e),
                Ok(Some(b)) => {
                    let m: BinderMeta = expr::binder_meta(prop_when::never());
                    match intern_e(st, ENodeView::Lam(ty, b, m)) {
                        Err(e) => Err(e),
                        Ok(r) => Ok(Some(r)),
                    }
                }
                Ok(None) => Ok(None),
            },
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1261-1267 replacePiBody
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:944-954 replacePiBody` —
/// replace the body under the first `k` `∀`-binders, domains and prop-ness
/// data kept.
pub fn replace_pi_body(
    st: &mut AState,
    k: u64,
    h: &EIdx,
    b: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if k == 0 {
        Ok(Some(b.dup2()))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(ty, rest, m)) => match replace_pi_body(st, k - 1, &rest, b) {
                Err(e) => Err(e),
                Ok(Some(r)) => {
                    let m2: BinderMeta = expr::binder_meta(m.pw);
                    match intern_e(st, ENodeView::ForallE(ty, r, m2)) {
                        Err(e) => Err(e),
                        Ok(x) => Ok(Some(x)),
                    }
                }
                Ok(None) => Ok(None),
            },
            Ok(_) => Ok(None),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1269-1272 piArity
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:958-965 piArity` — the length
/// of the leading `∀`-telescope.
pub fn pi_arity(st: &AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_PI_ARITY)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(_, b, _)) => match pi_arity(st, fuel - 1, &b) {
                Err(e) => Err(e),
                Ok(n) => Ok(n + 1),
            },
            Ok(_) => Ok(0),
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1274-1278 resultSort
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:969-975 resultSort` — the
/// result sort at the end of a `∀`-telescope.
pub fn result_sort(st: &AState, fuel: u64, h: &EIdx) -> Result<Option<LIdx>, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_RESULT_SORT)))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(_, b, _)) => result_sort(st, fuel - 1, &b),
            Ok(ENodeView::Sort(u)) => Ok(Some(u)),
            Ok(_) => Ok(None),
        }
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1293-1303 Expr.bvarBound
/// con-leche: ConLeche/Kernel/ExprOps.lean:1368-1392 bvarBoundGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:990-1015 bvarBoundGo` — the
/// memoized exact loose-bvar bound.  The memo is probed for every node, leaves
/// included, as con-leche probes it.  `y - 1` is Lean's truncating
/// subtraction, hence `sub_nat`.
pub fn bvar_bound_go(st: &mut AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_BVAR_BOUND)))
    } else {
        match bvar_b_get(st, h) {
            Some(r) => Ok(r),
            None => {
                let body: Result<u64, CheckError> = match view(st, h) {
                    Err(e) => Err(e),
                    Ok(ENodeView::BVar(i)) => Ok(i + 1),
                    Ok(ENodeView::FVar(_, _)) => Ok(0),
                    Ok(ENodeView::Sort(_)) => Ok(0),
                    Ok(ENodeView::Const(_, _)) => Ok(0),
                    Ok(ENodeView::Lit(_)) => Ok(0),
                    Ok(ENodeView::App(f, a)) => match bvar_bound_go(st, fuel - 1, &f) {
                        Err(e) => Err(e),
                        Ok(x) => match bvar_bound_go(st, fuel - 1, &a) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::Lam(ty, body, _)) => match bvar_bound_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(x) => match bvar_bound_go(st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, sub_nat(y, 1))),
                        },
                    },
                    Ok(ENodeView::ForallE(ty, body, _)) => {
                        match bvar_bound_go(st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match bvar_bound_go(st, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(y) => Ok(expr::max_u64(x, sub_nat(y, 1))),
                            },
                        }
                    }
                    Ok(ENodeView::LetE(ty, val, body)) => {
                        match bvar_bound_go(st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match bvar_bound_go(st, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(y) => match bvar_bound_go(st, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(z) => {
                                        Ok(expr::max_u64(expr::max_u64(x, y), sub_nat(z, 1)))
                                    }
                                },
                            },
                        }
                    }
                    Ok(ENodeView::Proj(_, _, sub)) => bvar_bound_go(st, fuel - 1, &sub),
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1394-1395 bvarBoundMemo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1019-1023 bvarBoundMemo` — the
/// top-level entry of the memoized walk.
pub fn bvar_bound_memo(st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    bvar_b_clear(st);
    match bvar_bound_go(st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            bvar_b_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1312-1323 Expr.fvarRange
/// con-leche: ConLeche/Kernel/ExprOps.lean:1397-1422 fvarRangeGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1029-1054 fvarRangeGo` — the
/// memoized exact fvar range (`fvar` annotations are not descended into,
/// matching the abstraction traversals).
pub fn fvar_range_go(st: &mut AState, fuel: u64, h: &EIdx) -> Result<u64, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_FVAR_RANGE)))
    } else {
        match fvar_b_get(st, h) {
            Some(r) => Ok(r),
            None => {
                let body: Result<u64, CheckError> = match view(st, h) {
                    Err(e) => Err(e),
                    Ok(ENodeView::FVar(idx, _)) => Ok(idx + 1),
                    Ok(ENodeView::BVar(_)) => Ok(0),
                    Ok(ENodeView::Sort(_)) => Ok(0),
                    Ok(ENodeView::Const(_, _)) => Ok(0),
                    Ok(ENodeView::Lit(_)) => Ok(0),
                    Ok(ENodeView::App(f, a)) => match fvar_range_go(st, fuel - 1, &f) {
                        Err(e) => Err(e),
                        Ok(x) => match fvar_range_go(st, fuel - 1, &a) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::Lam(ty, body, _)) => match fvar_range_go(st, fuel - 1, &ty) {
                        Err(e) => Err(e),
                        Ok(x) => match fvar_range_go(st, fuel - 1, &body) {
                            Err(e) => Err(e),
                            Ok(y) => Ok(expr::max_u64(x, y)),
                        },
                    },
                    Ok(ENodeView::ForallE(ty, body, _)) => {
                        match fvar_range_go(st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match fvar_range_go(st, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(y) => Ok(expr::max_u64(x, y)),
                            },
                        }
                    }
                    Ok(ENodeView::LetE(ty, val, body)) => {
                        match fvar_range_go(st, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(x) => match fvar_range_go(st, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(y) => match fvar_range_go(st, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(z) => Ok(expr::max_u64(expr::max_u64(x, y), z)),
                                },
                            },
                        }
                    }
                    Ok(ENodeView::Proj(_, _, sub)) => fvar_range_go(st, fuel - 1, &sub),
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1424-1425 fvarRangeMemo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1058-1062 fvarRangeMemo` — the
/// top-level entry of the memoized walk.
pub fn fvar_range_memo(st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    fvar_b_clear(st);
    match fvar_range_go(st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => {
            fvar_b_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1427-1432 bvarB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1068-1071 bvarB` — **the
/// loose-bvar bound the checker reads**: the packed field, or — on the
/// saturated branch alone — the exact memoized recomputation.
pub fn bvar_b(st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    let der: u64 = derived_e(st, e);
    let r: u64 = expr::bvar_of_data(der);
    if r == expr::sat_range() {
        bvar_bound_memo(st, fuel, e)
    } else {
        Ok(r)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1434-1439 fvarB
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1076-1079 fvarB` — **the fvar
/// range the checker reads**: the packed field, or the exact memoized
/// recomputation on the saturated branch.
pub fn fvar_b(st: &mut AState, fuel: u64, e: &EIdx) -> Result<u64, CheckError> {
    let der: u64 = derived_e(st, e);
    let r: u64 = expr::fvar_of_data(der);
    if r == expr::sat_range() {
        fvar_range_memo(st, fuel, e)
    } else {
        Ok(r)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1707-1708 hasFvarFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1083-1085 hasFvarFast` — the
/// executed `hasFvar`: the fvar-range field read.
pub fn has_fvar_fast(st: &mut AState, fuel: u64, e: &EIdx) -> Result<bool, CheckError> {
    match fvar_b(st, fuel, e) {
        Err(er) => Err(er),
        Ok(r) => Ok(r != 0),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1716-1717 looseBVarsBoundedFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1089-1091 looseBVarsBoundedFast`
/// — the executed `looseBVarsBounded`: the loose-bvar field read.
pub fn loose_bvars_bounded_fast(
    st: &mut AState,
    fuel: u64,
    k: u64,
    e: &EIdx,
) -> Result<bool, CheckError> {
    match bvar_b(st, fuel, e) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:760-776 abstract1
/// con-leche: ConLeche/Kernel/ExprOps.lean:1789-1833 abstract1Go
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1102-1159 abstract1Go` — close
/// a binder body: replace `fvar d …` leaves by `bvar k`, bumping `k` under
/// binders.  `fvar` annotations are not descended into.
pub fn abstract1_go(
    st: &mut AState,
    d: u64,
    fuel: u64,
    h: &EIdx,
    k: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_ABS1)))
    } else {
        match fvar_b(st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(fb) => {
                if fb <= d {
                    Ok(h.dup2())
                } else {
                    match view(st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
                        Ok(ENodeView::FVar(idx, _)) => {
                            if idx == d {
                                intern_e(st, ENodeView::BVar(k))
                            } else {
                                Ok(h.dup2())
                            }
                        }
                        Ok(ENodeView::Sort(_)) => Ok(h.dup2()),
                        Ok(ENodeView::Const(_, _)) => Ok(h.dup2()),
                        Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
                        Ok(ENodeView::App(f, a)) => {
                            let ky: EIdxNat = eidx_nat_key(h, k);
                            match abs1_get(st, &ky) {
                                Some(r) => Ok(r),
                                None => match abstract1_go(st, d, fuel - 1, &f, k) {
                                    Err(e) => Err(e),
                                    Ok(f2) => match abstract1_go(st, d, fuel - 1, &a, k) {
                                        Err(e) => Err(e),
                                        Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                abs1_set(st, ky, &r);
                                                Ok(r)
                                            }
                                        },
                                    },
                                },
                            }
                        }
                        Ok(ENodeView::Lam(ty, body, m)) => {
                            let ky: EIdxNat = eidx_nat_key(h, k);
                            match abs1_get(st, &ky) {
                                Some(r) => Ok(r),
                                None => match abstract1_go(st, d, fuel - 1, &ty, k) {
                                    Err(e) => Err(e),
                                    Ok(t) => match abstract1_go(st, d, fuel - 1, &body, k + 1) {
                                        Err(e) => Err(e),
                                        Ok(b) => match intern_e(st, ENodeView::Lam(t, b, m)) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                abs1_set(st, ky, &r);
                                                Ok(r)
                                            }
                                        },
                                    },
                                },
                            }
                        }
                        Ok(ENodeView::ForallE(ty, body, m)) => {
                            let ky: EIdxNat = eidx_nat_key(h, k);
                            match abs1_get(st, &ky) {
                                Some(r) => Ok(r),
                                None => match abstract1_go(st, d, fuel - 1, &ty, k) {
                                    Err(e) => Err(e),
                                    Ok(t) => match abstract1_go(st, d, fuel - 1, &body, k + 1) {
                                        Err(e) => Err(e),
                                        Ok(b) => match intern_e(st, ENodeView::ForallE(t, b, m)) {
                                            Err(e) => Err(e),
                                            Ok(r) => {
                                                abs1_set(st, ky, &r);
                                                Ok(r)
                                            }
                                        },
                                    },
                                },
                            }
                        }
                        Ok(ENodeView::LetE(ty, val, body)) => {
                            let ky: EIdxNat = eidx_nat_key(h, k);
                            match abs1_get(st, &ky) {
                                Some(r) => Ok(r),
                                None => match abstract1_go(st, d, fuel - 1, &ty, k) {
                                    Err(e) => Err(e),
                                    Ok(t) => match abstract1_go(st, d, fuel - 1, &val, k) {
                                        Err(e) => Err(e),
                                        Ok(w) => {
                                            match abstract1_go(st, d, fuel - 1, &body, k + 1) {
                                                Err(e) => Err(e),
                                                Ok(b) => {
                                                    match intern_e(st, ENodeView::LetE(t, w, b)) {
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
                                },
                            }
                        }
                        Ok(ENodeView::Proj(n, i, sub)) => {
                            let ky: EIdxNat = eidx_nat_key(h, k);
                            match abs1_get(st, &ky) {
                                Some(r) => Ok(r),
                                None => match abstract1_go(st, d, fuel - 1, &sub, k) {
                                    Err(e) => Err(e),
                                    Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            abs1_set(st, ky, &r);
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:1927-1929 abstract1Fast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1163-1167 abstract1Fast` — the
/// top-level entry.
pub fn abstract1_fast(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    d: u64,
    k: u64,
) -> Result<EIdx, CheckError> {
    abs1_clear(st);
    match abstract1_go(st, d, fuel, e, k) {
        Err(er) => Err(er),
        Ok(r) => {
            abs1_clear(st);
            Ok(r)
        }
    }
}

// ---------------------------------------------------------------------------
// `lowerBVars` — `ExprOps.lean:694-716`, `:2012-2049`, `:2144-2146`
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:2012-2049 lowerBVarsGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1175-1232 lowerBVarsGo` — lower
/// every loose bound variable `>= cutoff + amount` by `amount`, with
/// con-leche's own `bvarB <= c + amount` cutoff.
pub fn lower_bvars_go(
    st: &mut AState,
    amount: u64,
    fuel: u64,
    h: &EIdx,
    c: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_LOWER)))
    } else {
        match bvar_b(st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= c + amount {
                    Ok(h.dup2())
                } else {
                    match view(st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(i)) => {
                            if i >= c + amount {
                                intern_e(st, ENodeView::BVar(i - amount))
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
                                None => match lower_bvars_go(st, amount, fuel - 1, &f, c) {
                                    Err(e) => Err(e),
                                    Ok(f2) => match lower_bvars_go(st, amount, fuel - 1, &a, c) {
                                        Err(e) => Err(e),
                                        Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
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
                                None => match lower_bvars_go(st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match lower_bvars_go(st, amount, fuel - 1, &body, c + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e(st, ENodeView::Lam(t, b, m)) {
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
                                None => match lower_bvars_go(st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match lower_bvars_go(st, amount, fuel - 1, &body, c + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e(st, ENodeView::ForallE(t, b, m)) {
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
                                None => match lower_bvars_go(st, amount, fuel - 1, &ty, c) {
                                    Err(e) => Err(e),
                                    Ok(t) => match lower_bvars_go(st, amount, fuel - 1, &val, c) {
                                        Err(e) => Err(e),
                                        Ok(w) => {
                                            match lower_bvars_go(st, amount, fuel - 1, &body, c + 1)
                                            {
                                                Err(e) => Err(e),
                                                Ok(b) => {
                                                    match intern_e(st, ENodeView::LetE(t, w, b)) {
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
                                None => match lower_bvars_go(st, amount, fuel - 1, &sub, c) {
                                    Err(e) => Err(e),
                                    Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:2144-2146 lowerBVarsFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1236-1240 lowerBVarsFast` — the
/// top-level entry.
pub fn lower_bvars_fast(
    st: &mut AState,
    fuel: u64,
    amount: u64,
    c: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    lower_clear(st);
    match lower_bvars_go(st, amount, fuel, e, c) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
/// con-leche: ConLeche/Kernel/ExprOps.lean:2222-2261 instantiate1LiftGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1254-1314 instantiate1LiftGo` —
/// replace `bvar d` by `v`, lifting `v`'s loose `bvar`s past the binders
/// crossed on the way, with con-leche's own `bvarB <= d` cutoff.
pub fn instantiate1_lift_go(
    st: &mut AState,
    v: &EIdx,
    fuel: u64,
    h: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST1_LIFT)))
    } else {
        match bvar_b(st, fuel - 1, h) {
            Err(e) => Err(e),
            Ok(bb) => {
                if bb <= d {
                    Ok(h.dup2())
                } else {
                    match view(st, h) {
                        Err(e) => Err(e),
                        Ok(ENodeView::BVar(i)) => {
                            if i == d {
                                lift_loose_bvars_fast(st, fuel - 1, d, 0, v)
                            } else if i > d {
                                intern_e(st, ENodeView::BVar(i - 1))
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
                                None => match instantiate1_lift_go(st, v, fuel - 1, &f, d) {
                                    Err(e) => Err(e),
                                    Ok(f2) => {
                                        match instantiate1_lift_go(st, v, fuel - 1, &a, d) {
                                            Err(e) => Err(e),
                                            Ok(a2) => {
                                                match intern_e(st, ENodeView::App(f2, a2)) {
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
                                None => match instantiate1_lift_go(st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(st, v, fuel - 1, &body, d + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e(st, ENodeView::Lam(t, b, m)) {
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
                                None => match instantiate1_lift_go(st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(st, v, fuel - 1, &body, d + 1) {
                                            Err(e) => Err(e),
                                            Ok(b) => {
                                                match intern_e(st, ENodeView::ForallE(t, b, m)) {
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
                                None => match instantiate1_lift_go(st, v, fuel - 1, &ty, d) {
                                    Err(e) => Err(e),
                                    Ok(t) => {
                                        match instantiate1_lift_go(st, v, fuel - 1, &val, d) {
                                            Err(e) => Err(e),
                                            Ok(w) => {
                                                match instantiate1_lift_go(
                                                    st,
                                                    v,
                                                    fuel - 1,
                                                    &body,
                                                    d + 1,
                                                ) {
                                                    Err(e) => Err(e),
                                                    Ok(b) => {
                                                        match intern_e(
                                                            st,
                                                            ENodeView::LetE(t, w, b),
                                                        ) {
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
                                None => match instantiate1_lift_go(st, v, fuel - 1, &sub, d) {
                                    Err(e) => Err(e),
                                    Ok(u) => match intern_e(st, ENodeView::Proj(n, i, u)) {
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:2356-2358 instantiate1LiftFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1318-1322 instantiate1LiftFast`
/// — the top-level entry.
pub fn instantiate1_lift_fast(
    st: &mut AState,
    fuel: u64,
    e: &EIdx,
    v: &EIdx,
    d: u64,
) -> Result<EIdx, CheckError> {
    inst1_l_clear(st);
    match instantiate1_lift_go(st, v, fuel, e, d) {
        Err(er) => Err(er),
        Ok(r) => {
            inst1_l_clear(st);
            Ok(r)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2365-2378 instPisAtLift
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1326-1333 instPisAtLift` —
/// instantiate the leading `∀`-binders at *open* arguments.
pub fn inst_pis_at_lift(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    inst_pis_at_lift_from(st, fuel, args, 0, h)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2365-2378 instPisAtLift
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1326-1333 instPisAtLift` — the
/// cursor recursion behind `inst_pis_at_lift`.
pub fn inst_pis_at_lift_from(
    st: &mut AState,
    fuel: u64,
    args: &Vec<EIdx>,
    i: usize,
    h: &EIdx,
) -> Result<Option<EIdx>, CheckError> {
    if i >= args.len() {
        Ok(Some(h.dup2()))
    } else {
        match view(st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::ForallE(_, body, _)) => {
                let a: EIdx = args[i].dup2();
                match instantiate1_lift_fast(st, fuel, &body, &a, 0) {
                    Err(e) => Err(e),
                    Ok(b) => inst_pis_at_lift_from(st, fuel, args, i + 1, &b),
                }
            }
            Ok(_) => Ok(None),
        }
    }
}

// ---------------------------------------------------------------------------
// Equality, and the two derived bits
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:2382-2388 exprPtrBEq
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1343 exprPtrBEq` — structural
/// expression equality with a physical-equality shortcut.  In the arena it IS
/// index equality: `denoteE` is injective (`denoteE_inj`, task #97a), so two
/// handles denote one term exactly when they are the same handle, and the
/// pointer test and the structural test collapse into one machine-word
/// comparison.  No state is read, so this twin takes neither the state nor a
/// `Result`.
pub fn expr_ptr_beq(a: &EIdx, b: &EIdx) -> bool {
    a.eq2(b)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2399-2406 Level.hasParam
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1350-1352 LIdx.hasParam` —
/// whether a level mentions any parameter.  con-leche walks the level; the
/// arena reads the bit the level store already carries (`LDer.has_param`,
/// exact by `LStore.derived_exact`), which is DESIGN.md §8.3's
/// level-substitution cutoff in `O(1)`.  A free function rather than an
/// inherent method, so that the state stays the first argument as it is
/// everywhere else in this module.
pub fn lidx_has_param(st: &AState, h: &LIdx) -> bool {
    derived_l(st, h).has_param
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2420-2435 Expr.hasLevelParam
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1358-1360 EIdx.hasLevelParam` —
/// whether an expression mentions any level parameter.  Again a field read:
/// this is exactly the `hasLP` bit of the packed derived word, and
/// `Expr.hasLP_eq` is con-leche's own proof that the two agree.
pub fn eidx_has_level_param(st: &AState, h: &EIdx) -> bool {
    expr::lp_of_data(derived_e(st, h))
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

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1376-1379 substLevelList` —
/// `vs.map (Level.subst ks us)` as explicit recursion.  con-leche writes the
/// `.map`; a closure is what DESIGN.md §3.4 forbids, and §3.4's own rule for a
/// `List` recursion is a helper, so the twin has one and so does this.
pub fn subst_level_list(ks: &Vec<Name>, us: &Vec<Level>, vs: &Vec<Level>) -> Vec<Level> {
    subst_level_list_from(ks, us, vs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1376-1379 substLevelList` — the
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:2564-2603 Expr.instLPGo
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1387-1457 instLPGo` —
/// substitute level parameters throughout an expression, with con-leche's own
/// `hasLP = false` cutoff (the whole subtree is level-parameter free, so the
/// substitution is the identity on it).  `.sort` and `.const` read their
/// levels back, run `Level.subst` on the transient trees and re-intern;
/// nothing else in this module touches a level.
pub fn inst_lp_go(
    st: &mut AState,
    ks: &Vec<Name>,
    us: &Vec<Level>,
    fuel: u64,
    h: &EIdx,
) -> Result<EIdx, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_INST_LP)))
    } else {
        let der: u64 = derived_e(st, h);
        if !expr::lp_of_data(der) {
            Ok(h.dup2())
        } else {
            match view(st, h) {
                Err(e) => Err(e),
                Ok(ENodeView::BVar(_)) => Ok(h.dup2()),
                Ok(ENodeView::Lit(_)) => Ok(h.dup2()),
                Ok(ENodeView::Sort(u)) => match read_level(st, &u) {
                    Err(e) => Err(e),
                    Ok(l) => {
                        let l2: Level = level::subst(ks, us, &l);
                        match intern_level(st, &l2) {
                            Err(e) => Err(e),
                            Ok(hl) => intern_e(st, ENodeView::Sort(hl)),
                        }
                    }
                },
                Ok(ENodeView::Const(n, vs)) => match read_levels(st, &vs) {
                    Err(e) => Err(e),
                    Ok(ls) => {
                        let ls2: Vec<Level> = subst_level_list(ks, us, &ls);
                        match intern_levels(st, &ls2) {
                            Err(e) => Err(e),
                            Ok(vs2) => intern_e(st, ENodeView::Const(n, vs2)),
                        }
                    }
                },
                Ok(ENodeView::FVar(i, ty)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match intern_e(st, ENodeView::FVar(i, t)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_lp_set(st, k, &r);
                                    Ok(r)
                                }
                            },
                        },
                    }
                }
                Ok(ENodeView::App(f, a)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(st, ks, us, fuel - 1, &f) {
                            Err(e) => Err(e),
                            Ok(f2) => match inst_lp_go(st, ks, us, fuel - 1, &a) {
                                Err(e) => Err(e),
                                Ok(a2) => match intern_e(st, ENodeView::App(f2, a2)) {
                                    Err(e) => Err(e),
                                    Ok(r) => {
                                        inst_lp_set(st, k, &r);
                                        Ok(r)
                                    }
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::Lam(ty, body, m)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(st, ks, us, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b) => {
                                    let m2: BinderMeta =
                                        expr::binder_meta(level::subst_pw(ks, us, &m.pw));
                                    match intern_e(st, ENodeView::Lam(t, b, m2)) {
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
                        None => match inst_lp_go(st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(st, ks, us, fuel - 1, &body) {
                                Err(e) => Err(e),
                                Ok(b) => {
                                    let m2: BinderMeta =
                                        expr::binder_meta(level::subst_pw(ks, us, &m.pw));
                                    match intern_e(st, ENodeView::ForallE(t, b, m2)) {
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
                        None => match inst_lp_go(st, ks, us, fuel - 1, &ty) {
                            Err(e) => Err(e),
                            Ok(t) => match inst_lp_go(st, ks, us, fuel - 1, &val) {
                                Err(e) => Err(e),
                                Ok(w) => match inst_lp_go(st, ks, us, fuel - 1, &body) {
                                    Err(e) => Err(e),
                                    Ok(b) => match intern_e(st, ENodeView::LetE(t, w, b)) {
                                        Err(e) => Err(e),
                                        Ok(r) => {
                                            inst_lp_set(st, k, &r);
                                            Ok(r)
                                        }
                                    },
                                },
                            },
                        },
                    }
                }
                Ok(ENodeView::Proj(n, i, sub)) => {
                    let k: EIdxNat = eidx_nat_key(h, 0);
                    match inst_lp_get(st, &k) {
                        Some(r) => Ok(r),
                        None => match inst_lp_go(st, ks, us, fuel - 1, &sub) {
                            Err(e) => Err(e),
                            Ok(u2) => match intern_e(st, ENodeView::Proj(n, i, u2)) {
                                Err(e) => Err(e),
                                Ok(r) => {
                                    inst_lp_set(st, k, &r);
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

/// con-leche: ConLeche/Kernel/ExprOps.lean:2718-2720 Expr.instLPFast
/// Lean twin: `proof/ConRon/Arena/ExprOps.lean:1462-1468 instLPFast` — the
/// top-level entry: read the substitution back out of the store once, walk,
/// drop the memo.
pub fn inst_lp_fast(
    st: &mut AState,
    fuel: u64,
    ks: &Vec<NIdx>,
    us: &LsIdx,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match read_names(st, ks) {
        Err(er) => Err(er),
        Ok(ks_p) => match read_levels(st, us) {
            Err(er) => Err(er),
            Ok(us_p) => {
                inst_lp_clear(st);
                match inst_lp_go(st, &ks_p, &us_p, fuel, e) {
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
    use super::*;
    use crate::arena::monad::{
        denote_l, denote_ls, denote_n, intern_l_node, intern_n_node, intern_ls_node, AState,
    };
    use crate::arena::store::{EStore, LNodeView, NNodeView};
    use con_ron_core::kernel::expr::Expr;
    use con_ron_core::kernel::expr_ops as core_ops;
    use con_ron_core::kernel::expr_ops::NameToName;
    use con_ron_core::kernel::level as core_level;
    use con_ron_core::kernel::name;
    use con_ron_core::ron::nat;

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

    fn denote_e_aux(st: &EStore, fuel: u64, i: &EIdx) -> Option<Expr> {
        if fuel == 0 {
            return None;
        }
        match st.view(i) {
            None => None,
            Some(ENodeView::BVar(k)) => Some(expr::bvar(k)),
            Some(ENodeView::FVar(k, ty)) => {
                denote_e_aux(st, fuel - 1, &ty).map(|t| expr::fvar(k, t))
            }
            Some(ENodeView::Sort(u)) => denote_l(st.ls(), &u).map(expr::sort),
            Some(ENodeView::Const(n, us)) => {
                match (denote_n(st.ns(), &n), denote_ls(st.ls_s(), &us)) {
                    (Some(a), Some(b)) => Some(expr::mk_const(a, b)),
                    _ => None,
                }
            }
            Some(ENodeView::App(g, a)) => {
                match (denote_e_aux(st, fuel - 1, &g), denote_e_aux(st, fuel - 1, &a)) {
                    (Some(x), Some(y)) => Some(expr::app(x, y)),
                    _ => None,
                }
            }
            Some(ENodeView::Lam(ty, b, m)) => {
                match (denote_e_aux(st, fuel - 1, &ty), denote_e_aux(st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::lam(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::ForallE(ty, b, m)) => {
                match (denote_e_aux(st, fuel - 1, &ty), denote_e_aux(st, fuel - 1, &b)) {
                    (Some(x), Some(y)) => Some(expr::forall_e(x, y, m)),
                    _ => None,
                }
            }
            Some(ENodeView::LetE(ty, v, b)) => match (
                denote_e_aux(st, fuel - 1, &ty),
                denote_e_aux(st, fuel - 1, &v),
                denote_e_aux(st, fuel - 1, &b),
            ) {
                (Some(x), Some(y), Some(z)) => Some(expr::let_e(x, y, z)),
                _ => None,
            },
            Some(ENodeView::Lit(l)) => Some(expr::lit(l)),
            Some(ENodeView::Proj(n, k, e)) => {
                match (denote_n(st.ns(), &n), denote_e_aux(st, fuel - 1, &e)) {
                    (Some(s), Some(x)) => Some(expr::proj(s, k, x)),
                    _ => None,
                }
            }
        }
    }

    fn denote_e(st: &EStore, i: &EIdx) -> Option<Expr> {
        denote_e_aux(st, st.node_count() as u64 + 1, i)
    }

    /// The twin's `E h`: the denotation of a fixture handle.
    fn den(st: &AState, h: &EIdx) -> Expr {
        match denote_e(&st.store, h) {
            Some(e) => e,
            None => panic!("a fixture handle does not denote"),
        }
    }

    /// The twin's `L h`.
    fn den_l(st: &AState, h: &LIdx) -> Level {
        match denote_l(st.store.ls(), h) {
            Some(u) => u,
            None => panic!("a fixture level handle does not denote"),
        }
    }

    /// The twin's `N h`.
    fn den_n(st: &AState, h: &NIdx) -> Name {
        match denote_n(st.store.ns(), h) {
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
    fn intern_expr(st: &mut AState, e: &Expr) -> EIdx {
        match expr::view(e) {
            expr::ExprView::Bvar(i) => ok(intern_e(st, ENodeView::BVar(*i))),
            expr::ExprView::Fvar(i, ty) => {
                let t = intern_expr(st, ty);
                ok(intern_e(st, ENodeView::FVar(*i, t)))
            }
            expr::ExprView::Sort(u) => {
                let hu = ok(crate::arena::monad::intern_level(st, u));
                ok(intern_e(st, ENodeView::Sort(hu)))
            }
            expr::ExprView::Const(n, us) => {
                let hn = ok(crate::arena::monad::intern_name(st, n));
                let hus = ok(crate::arena::monad::intern_levels(st, us));
                ok(intern_e(st, ENodeView::Const(hn, hus)))
            }
            expr::ExprView::App(f, a) => {
                let hf = intern_expr(st, f);
                let ha = intern_expr(st, a);
                ok(intern_e(st, ENodeView::App(hf, ha)))
            }
            expr::ExprView::Lam(ty, b, m) => {
                let ht = intern_expr(st, ty);
                let hb = intern_expr(st, b);
                ok(intern_e(st, ENodeView::Lam(ht, hb, expr::binder_meta_dup(m))))
            }
            expr::ExprView::ForallE(ty, b, m) => {
                let ht = intern_expr(st, ty);
                let hb = intern_expr(st, b);
                ok(intern_e(st, ENodeView::ForallE(ht, hb, expr::binder_meta_dup(m))))
            }
            expr::ExprView::LetE(ty, v, b) => {
                let ht = intern_expr(st, ty);
                let hv = intern_expr(st, v);
                let hb = intern_expr(st, b);
                ok(intern_e(st, ENodeView::LetE(ht, hv, hb)))
            }
            expr::ExprView::Lit(l) => ok(intern_e(st, ENodeView::Lit(expr::literal_dup(l)))),
            expr::ExprView::Proj(n, i, sub) => {
                let hn = ok(crate::arena::monad::intern_name(st, n));
                let hs = intern_expr(st, sub);
                ok(intern_e(st, ENodeView::Proj(hn, *i, hs)))
            }
        }
    }

    // --- the comparison shapes ---------------------------------------------

    fn eq_e(st: &AState, got: &EIdx, want: &Expr) -> bool {
        expr::beq(&den(st, got), want)
    }

    fn eq_le(st: &AState, got: &Vec<EIdx>, want: &Vec<Expr>) -> bool {
        got.len() == want.len()
            && (0..got.len()).all(|i| expr::beq(&den(st, &got[i]), &want[i]))
    }

    fn eq_ope(st: &AState, got: &Option<EIdx>, want: &Option<Expr>) -> bool {
        match (got, want) {
            (Some(g), Some(w)) => eq_e(st, g, w),
            (None, None) => true,
            _ => false,
        }
    }

    fn eq_pair(
        st: &AState,
        got: &Option<(Vec<EIdx>, EIdx)>,
        want: &Option<(Vec<Expr>, Expr)>,
    ) -> bool {
        match (got, want) {
            (Some(g), Some(w)) => eq_le(st, &g.0, &w.0) && eq_e(st, &g.1, &w.1),
            (None, None) => true,
            _ => false,
        }
    }

    fn eq_binders(
        st: &AState,
        got: &Option<(Vec<(EIdx, BinderMeta)>, EIdx)>,
        want: &Option<(Vec<(Expr, BinderMeta)>, Expr)>,
    ) -> bool {
        match (got, want) {
            (Some(g), Some(w)) => {
                g.0.len() == w.0.len()
                    && (0..g.0.len()).all(|i| {
                        expr::beq(&den(st, &g.0[i].0), &w.0[i].0)
                            && expr::binder_meta_beq(&g.0[i].1, &w.0[i].1)
                    })
                    && eq_e(st, &g.1, &w.1)
            }
            (None, None) => true,
            _ => false,
        }
    }

    fn eq_fvl(st: &AState, got: &Vec<(u64, EIdx)>, want: &Vec<(u64, Expr)>) -> bool {
        got.len() == want.len()
            && (0..got.len())
                .all(|i| got[i].0 == want[i].0 && expr::beq(&den(st, &got[i].1), &want[i].1))
    }

    fn eq_opw(got: &Option<PropWhen>, want: &Option<PropWhen>) -> bool {
        match (got, want) {
            (Some(g), Some(w)) => prop_when::beq(g, w),
            (None, None) => true,
            _ => false,
        }
    }

    fn eq_ol(st: &AState, got: &Option<LIdx>, want: &Option<Level>) -> bool {
        match (got, want) {
            (Some(g), Some(w)) => core_level::beq(&den_l(st, g), w),
            (None, None) => true,
            _ => false,
        }
    }

    // --- the fixture --------------------------------------------------------

    /// The handles the checks below name — the twin's `Fx`, built by the same
    /// `intern` calls in the same order, so that a handle here is the same
    /// machine word as a handle there.
    struct Fx {
        z: LIdx,
        one: LIdx,
        pu: LIdx,
        foo: NIdx,
        bar: NIdx,
        u_n: NIdx,
        us_z: LsIdx,
        us_u: LsIdx,
        s0: EIdx,
        s1: EIdx,
        su: EIdx,
        cf: EIdx,
        cb: EIdx,
        b0: EIdx,
        b1: EIdx,
        b2: EIdx,
        lit7: EIdx,
        fv0: EIdx,
        fv1: EIdx,
        ap1: EIdx,
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
        let mut st = AState::init(EStore::empty());
        let nev = || expr::binder_meta(prop_when::never());
        let z = ok(intern_l_node(&mut st, LNodeView::Zero));
        let one = ok(intern_l_node(&mut st, LNodeView::Succ(z.dup2())));
        let anon = ok(intern_n_node(&mut st, NNodeView::Anonymous));
        let foo = ok(intern_n_node(&mut st, NNodeView::Str(anon.dup2(), cp("foo"))));
        let bar = ok(intern_n_node(&mut st, NNodeView::Str(anon.dup2(), cp("bar"))));
        let u_n = ok(intern_n_node(&mut st, NNodeView::Str(anon.dup2(), cp("u"))));
        let pu = ok(intern_l_node(&mut st, LNodeView::Param(u_n.dup2())));
        let us_z = ok(intern_ls_node(&mut st, vec![z.dup2()]));
        let us_u = ok(intern_ls_node(&mut st, vec![pu.dup2()]));
        let s0 = ok(intern_e(&mut st, ENodeView::Sort(z.dup2())));
        let s1 = ok(intern_e(&mut st, ENodeView::Sort(one.dup2())));
        let su = ok(intern_e(&mut st, ENodeView::Sort(pu.dup2())));
        let cf = ok(intern_e(&mut st, ENodeView::Const(foo.dup2(), us_z.dup2())));
        let cb = ok(intern_e(&mut st, ENodeView::Const(bar.dup2(), us_u.dup2())));
        let b0 = ok(intern_e(&mut st, ENodeView::BVar(0)));
        let b1 = ok(intern_e(&mut st, ENodeView::BVar(1)));
        let b2 = ok(intern_e(&mut st, ENodeView::BVar(2)));
        let lit7 = ok(intern_e(
            &mut st,
            ENodeView::Lit(expr::literal_nat(nat::from_u64(7))),
        ));
        let fv0 = ok(intern_e(&mut st, ENodeView::FVar(0, s0.dup2())));
        let fv1 = ok(intern_e(&mut st, ENodeView::FVar(1, s1.dup2())));
        let ap1 = ok(intern_e(&mut st, ENodeView::App(cf.dup2(), b0.dup2())));
        let pj = ok(intern_e(&mut st, ENodeView::Proj(foo.dup2(), 0, ap1.dup2())));
        let lam_t = ok(intern_e(
            &mut st,
            ENodeView::Lam(s0.dup2(), ap1.dup2(), nev()),
        ));
        let apbf = ok(intern_e(&mut st, ENodeView::App(b1.dup2(), fv0.dup2())));
        let all_t = ok(intern_e(
            &mut st,
            ENodeView::ForallE(s0.dup2(), apbf.dup2(), nev()),
        ));
        let apbb = ok(intern_e(&mut st, ENodeView::App(b0.dup2(), b1.dup2())));
        let let_t = ok(intern_e(
            &mut st,
            ENodeView::LetE(s0.dup2(), cf.dup2(), apbb.dup2()),
        ));
        let apcb = ok(intern_e(&mut st, ENodeView::App(cb.dup2(), b0.dup2())));
        let apfv = ok(intern_e(&mut st, ENodeView::App(fv1.dup2(), b0.dup2())));
        let apb2 = ok(intern_e(&mut st, ENodeView::App(b2.dup2(), apfv.dup2())));
        let pj2 = ok(intern_e(
            &mut st,
            ENodeView::Proj(foo.dup2(), 0, apb2.dup2()),
        ));
        let inner = ok(intern_e(
            &mut st,
            ENodeView::ForallE(s1.dup2(), pj2.dup2(), nev()),
        ));
        let let_b = ok(intern_e(
            &mut st,
            ENodeView::LetE(su.dup2(), apcb.dup2(), inner.dup2()),
        ));
        let big = ok(intern_e(
            &mut st,
            ENodeView::Lam(s0.dup2(), let_b.dup2(), nev()),
        ));
        let apb10 = ok(intern_e(&mut st, ENodeView::App(b1.dup2(), b0.dup2())));
        let pi_in = ok(intern_e(
            &mut st,
            ENodeView::ForallE(s1.dup2(), apb10.dup2(), nev()),
        ));
        let pi_t = ok(intern_e(
            &mut st,
            ENodeView::ForallE(s0.dup2(), pi_in.dup2(), nev()),
        ));
        let pi_s = ok(intern_e(
            &mut st,
            ENodeView::ForallE(s0.dup2(), s1.dup2(), nev()),
        ));
        let lam_in = ok(intern_e(
            &mut st,
            ENodeView::Lam(s1.dup2(), apb10.dup2(), nev()),
        ));
        let lam_t2 = ok(intern_e(
            &mut st,
            ENodeView::Lam(s0.dup2(), lam_in.dup2(), nev()),
        ));
        let sp1 = ok(intern_e(&mut st, ENodeView::App(cf.dup2(), fv0.dup2())));
        let spine = ok(intern_e(&mut st, ENodeView::App(sp1.dup2(), b0.dup2())));
        let fx = Fx {
            z,
            one,
            pu,
            foo,
            bar,
            u_n,
            us_z,
            us_u,
            s0,
            s1,
            su,
            cf,
            cb,
            b0,
            b1,
            b2,
            lit7,
            fv0,
            fv1,
            ap1,
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

    /// The fixture's renaming, on handles (the twin's `renH`).
    struct RenH {
        foo: EIdxRenameKey,
    }

    /// The `foo ↦ bar` pair `RenH` needs, as two handles.
    struct EIdxRenameKey {
        from: NIdx,
        to: NIdx,
    }

    impl NIdxToNIdx for RenH {
        fn rename(&self, n: &NIdx) -> NIdx {
            if n.eq2(&self.foo.from) {
                self.foo.to.dup2()
            } else {
                n.dup2()
            }
        }
    }

    /// The same renaming, on names (the twin's `renP`).
    struct RenP {
        from: Name,
        to: Name,
    }

    impl NameToName for RenP {
        fn rename(&self, n: &Name) -> Name {
            if name::beq(n, &self.from) {
                name::dup(&self.to)
            } else {
                name::dup(n)
            }
        }
    }

    // --- the fixture denotes what it should (19) ----------------------------
    //
    // The one place a con-leche value is written out by hand.  Everything
    // after this compares the twin's answer against `con-ron-core`'s function
    // applied to `den(h)`, which is only meaningful because these hold.

    #[test]
    fn fixture_denotes_what_it_should() {
        let (st, fx) = fixture();
        let anon = name::anonymous();
        let nfoo = name::mk_str(name::anonymous(), cp("foo"));
        let nbar = name::mk_str(name::anonymous(), cp("bar"));
        let nu = name::mk_str(name::anonymous(), cp("u"));
        let nev = || expr::binder_meta(prop_when::never());
        assert!(eq_e(&st, &fx.s0, &expr::sort(core_level::zero())));
        assert!(eq_e(
            &st,
            &fx.s1,
            &expr::sort(core_level::succ(core_level::zero()))
        ));
        assert!(eq_e(
            &st,
            &fx.su,
            &expr::sort(core_level::param(name::dup(&nu)))
        ));
        assert!(eq_e(
            &st,
            &fx.cf,
            &expr::mk_const(name::dup(&nfoo), vec![core_level::zero()])
        ));
        assert!(eq_e(
            &st,
            &fx.cb,
            &expr::mk_const(
                name::dup(&nbar),
                vec![core_level::param(name::dup(&nu))]
            )
        ));
        assert!(eq_e(
            &st,
            &fx.fv1,
            &expr::fvar(1, expr::sort(core_level::succ(core_level::zero())))
        ));
        assert!(eq_e(
            &st,
            &fx.lit7,
            &expr::lit(expr::literal_nat(nat::from_u64(7)))
        ));
        assert!(eq_e(
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
        assert!(denote_e(&st.store, &fx.let_t).is_some());
        assert!(denote_e(&st.store, &fx.all_t).is_some());
        assert!(denote_e(&st.store, &fx.pj).is_some());
        assert!(denote_e(&st.store, &fx.spine).is_some());
        assert!(denote_e(&st.store, &fx.lam_t2).is_some());
        assert!(denote_e(&st.store, &fx.pi_s).is_some());
        assert!(name::beq(&den_n(&st, &fx.foo), &nfoo));
        assert!(core_level::beq(
            &den_l(&st, &fx.pu),
            &core_level::param(name::dup(&nu))
        ));
        assert!(match denote_ls(st.store.ls_s(), &fx.us_z) {
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
        let (mut st, fx) = fixture();
        let e = den(&st, &fx.big);
        let h = intern_expr(&mut st, &e);
        assert!(eq_e(&st, &h, &e));
        // hash-consing: the tree came out of the store, so it goes back in at
        // the same handle.
        assert!(expr_ptr_beq(&h, &fx.big));
    }

    // --- `instantiate1` (8) --------------------------------------------------

    #[test]
    fn t_instantiate1() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let cf = den(&st, &fx.cf);
        let let_t = den(&st, &fx.let_t);
        let s1 = den(&st, &fx.s1);
        let b2 = den(&st, &fx.b2);
        let b0 = den(&st, &fx.b0);
        let lit7 = den(&st, &fx.lit7);
        let pj = den(&st, &fx.pj);
        let fv0 = den(&st, &fx.fv0);

        let w = core_ops::instantiate1(&big, &cf, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.big, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&big, &cf, 1);
        let r = ok(instantiate1_fast(&mut st, F, &fx.big, &fx.cf, 1));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&let_t, &s1, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.let_t, &fx.s1, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&b2, &cf, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.b2, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&b0, &cf, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.b0, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&lit7, &cf, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.lit7, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1(&pj, &fv0, 0);
        let r = ok(instantiate1_fast(&mut st, F, &fx.pj, &fx.fv0, 0));
        assert!(eq_e(&st, &r, &w));
        // the memoized walk without the top-level bracket is the same answer
        let w = core_ops::instantiate1(&big, &cf, 0);
        let r = ok(instantiate1_go(&mut st, &fx.cf, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `instantiateList` (6) ----------------------------------------------

    #[test]
    fn t_instantiate_list() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let cf = den(&st, &fx.cf);
        let s1 = den(&st, &fx.s1);
        let let_t = den(&st, &fx.let_t);
        let fv0 = den(&st, &fx.fv0);
        let b2 = den(&st, &fx.b2);
        let two = vec![expr::dup(&cf), expr::dup(&s1)];
        let hs2 = vec![fx.cf.dup2(), fx.s1.dup2()];

        let w = core_ops::instantiate_list(&big, &two, 0);
        let r = ok(instantiate_list_fast(&mut st, F, &fx.big, &hs2, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_list(&big, &two, 1);
        let r = ok(instantiate_list_fast(&mut st, F, &fx.big, &hs2, 1));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_list(&let_t, &vec![expr::dup(&fv0)], 0);
        let r = ok(instantiate_list_fast(&mut st, F, &fx.let_t, &vec![fx.fv0.dup2()], 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_list(&b2, &vec![expr::dup(&cf)], 0);
        let r = ok(instantiate_list_fast(&mut st, F, &fx.b2, &vec![fx.cf.dup2()], 0));
        assert!(eq_e(&st, &r, &w));
        // the unmemoized walk (the one `instantiate_list_go`'s `bvar` arm calls)
        let w = core_ops::instantiate_list(&big, &two, 0);
        let r = ok(instantiate_list(&mut st, &hs2, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));
        let b0 = den(&st, &fx.b0);
        let w = core_ops::instantiate_list(&b0, &vec![expr::dup(&cf)], 0);
        let r = ok(instantiate_list(&mut st, &vec![fx.cf.dup2()], F, &fx.b0, 0));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `liftLooseBVars` (4) -----------------------------------------------

    #[test]
    fn t_lift_loose_bvars() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let let_t = den(&st, &fx.let_t);

        let w = core_ops::lift_loose_bvars(2, 0, &big);
        let r = ok(lift_loose_bvars_fast(&mut st, F, 2, 0, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lift_loose_bvars(3, 1, &big);
        let r = ok(lift_loose_bvars_fast(&mut st, F, 3, 1, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lift_loose_bvars(1, 0, &let_t);
        let r = ok(lift_loose_bvars_fast(&mut st, F, 1, 0, &fx.let_t));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lift_loose_bvars(2, 0, &big);
        let r = ok(lift_loose_bvars_go(&mut st, 2, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `resetMeta` (4) -----------------------------------------------------

    #[test]
    fn t_reset_meta() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let lam_t = den(&st, &fx.lam_t);
        let fv1 = den(&st, &fx.fv1);

        let w = core_ops::reset_meta(&big);
        let r = ok(reset_meta_fast(&mut st, F, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::reset_meta(&lam_t);
        let r = ok(reset_meta_fast(&mut st, F, &fx.lam_t));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::reset_meta(&fv1);
        let r = ok(reset_meta_fast(&mut st, F, &fx.fv1));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::reset_meta(&big);
        let r = ok(reset_meta_go(&mut st, F, &fx.big));
        assert!(eq_e(&st, &r, &w));
    }

    // --- the measures and the scope predicates (17) -------------------------

    #[test]
    fn t_measures_and_scope() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let fv1 = den(&st, &fx.fv1);
        let all_t = den(&st, &fx.all_t);
        let let_t = den(&st, &fx.let_t);
        let s0 = den(&st, &fx.s0);

        assert_eq!(ok(size_b(&st, F, &fx.big)), core_ops::size_b(&big));
        assert_eq!(ok(size_b(&st, F, &fx.fv1)), core_ops::size_b(&fv1));
        assert_eq!(ok(size_f(&st, F, &fx.big)), core_ops::size_f(&big));
        assert_eq!(ok(size_f(&st, F, &fx.fv1)), core_ops::size_f(&fv1));

        let w = core_ops::abstract_range(&big, 0, 2, 0);
        let r = ok(abstract_range(&mut st, F, &fx.big, 0, 2, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract_range(&big, 1, 1, 0);
        let r = ok(abstract_range(&mut st, F, &fx.big, 1, 1, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract_range(&all_t, 0, 3, 1);
        let r = ok(abstract_range(&mut st, F, &fx.all_t, 0, 3, 1));
        assert!(eq_e(&st, &r, &w));

        let w = core_ops::fvar_leaves(&big);
        let r = ok(fvar_leaves(&st, F, &fx.big));
        assert!(eq_fvl(&st, &r, &w));
        let w = core_ops::fvar_leaves(&fv1);
        let r = ok(fvar_leaves(&st, F, &fx.fv1));
        assert!(eq_fvl(&st, &r, &w));
        let w = core_ops::fvar_leaves(&s0);
        let r = ok(fvar_leaves(&st, F, &fx.s0));
        assert!(eq_fvl(&st, &r, &w));

        assert_eq!(ok(wscoped_b(&st, F, 5, &fx.big)), core_ops::wscoped_b(5, &big));
        assert_eq!(ok(wscoped_b(&st, F, 1, &fx.big)), core_ops::wscoped_b(1, &big));
        assert_eq!(ok(wscoped_b(&st, F, 0, &fx.big)), core_ops::wscoped_b(0, &big));
        assert_eq!(
            ok(wscoped_b(&st, F, 2, &fx.let_t)),
            core_ops::wscoped_b(2, &let_t)
        );

        assert_eq!(
            ok(loose_bvars_bounded(&st, F, 3, &fx.big)),
            core_ops::loose_bvars_bounded(3, &big)
        );
        assert_eq!(
            ok(loose_bvars_bounded(&st, F, 0, &fx.big)),
            core_ops::loose_bvars_bounded(0, &big)
        );
        assert_eq!(
            ok(loose_bvars_bounded(&st, F, 1, &fx.let_t)),
            core_ops::loose_bvars_bounded(1, &let_t)
        );
    }

    // --- the one-node readers (9) -------------------------------------------

    #[test]
    fn t_one_node_readers() {
        let (st, fx) = fixture();
        let big = den(&st, &fx.big);
        let pi_t = den(&st, &fx.pi_t);
        let fv0 = den(&st, &fx.fv0);

        assert_eq!(ok(is_lam(&st, &fx.big)), core_ops::is_lam(&big));
        assert_eq!(ok(is_lam(&st, &fx.pi_t)), core_ops::is_lam(&pi_t));
        assert!(eq_opw(&ok(lam_pw(&st, &fx.big)), &core_ops::lam_pw(&big)));
        assert!(eq_opw(&ok(lam_pw(&st, &fx.pi_t)), &core_ops::lam_pw(&pi_t)));
        assert!(eq_opw(
            &ok(forall_pw(&st, &fx.pi_t)),
            &core_ops::forall_pw(&pi_t)
        ));
        assert!(eq_opw(
            &ok(forall_pw(&st, &fx.big)),
            &core_ops::forall_pw(&big)
        ));
        assert_eq!(ok(has_fvar(&st, F, &fx.big)), core_ops::has_fvar(&big));
        assert_eq!(ok(has_fvar(&st, F, &fx.pi_t)), core_ops::has_fvar(&pi_t));
        assert_eq!(ok(has_fvar(&st, F, &fx.fv0)), core_ops::has_fvar(&fv0));
    }

    // --- application spines (6) ---------------------------------------------

    #[test]
    fn t_spines() {
        let (mut st, fx) = fixture();
        let spine = den(&st, &fx.spine);
        let cf = den(&st, &fx.cf);
        let fv0 = den(&st, &fx.fv0);
        let b0 = den(&st, &fx.b0);

        let w = core_ops::get_app_fn(&spine);
        let r = ok(get_app_fn(&st, F, &fx.spine));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::get_app_fn(&cf);
        let r = ok(get_app_fn(&st, F, &fx.cf));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::get_app_args(&spine);
        let r = ok(get_app_args(&st, F, &fx.spine));
        assert!(eq_le(&st, &r, &w));
        let w = core_ops::get_app_args(&cf);
        let r = ok(get_app_args(&st, F, &fx.cf));
        assert!(eq_le(&st, &r, &w));
        let w = core_ops::mk_app_n(
            expr::dup(&cf),
            &vec![expr::dup(&fv0), expr::dup(&b0)],
        );
        let r = ok(mk_app_n(
            &mut st,
            &fx.cf,
            &vec![fx.fv0.dup2(), fx.b0.dup2()],
        ));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::mk_app_n(expr::dup(&cf), &Vec::new());
        let r = ok(mk_app_n(&mut st, &fx.cf, &Vec::new()));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `renameConsts` (4) --------------------------------------------------
    //
    // The twin's renaming is a map on name HANDLES; the bridge's obligation is
    // that it denotes con-leche's map on names, and here the two are written
    // side by side.

    #[test]
    fn t_rename_consts() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let cf = den(&st, &fx.cf);
        let fv1 = den(&st, &fx.fv1);
        let ren_h = RenH {
            foo: EIdxRenameKey { from: fx.foo.dup2(), to: fx.bar.dup2() },
        };
        let ren_p = RenP { from: den_n(&st, &fx.foo), to: den_n(&st, &fx.bar) };

        let w = core_ops::rename_consts(&ren_p, &big);
        let r = ok(rename_consts_fast(&mut st, F, &ren_h, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::rename_consts(&ren_p, &cf);
        let r = ok(rename_consts_fast(&mut st, F, &ren_h, &fx.cf));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::rename_consts(&ren_p, &fv1);
        let r = ok(rename_consts_fast(&mut st, F, &ren_h, &fx.fv1));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::rename_consts(&ren_p, &big);
        let r = ok(rename_consts_go(&mut st, &ren_h, F, &fx.big));
        assert!(eq_e(&st, &r, &w));
    }

    // --- telescopes, part 1: strip / result / arity / sort (13) --------------

    #[test]
    fn t_telescopes_readers() {
        let (st, fx) = fixture();
        let lam_t2 = den(&st, &fx.lam_t2);
        let pi_t = den(&st, &fx.pi_t);
        let cf = den(&st, &fx.cf);
        let pi_s = den(&st, &fx.pi_s);
        let s1 = den(&st, &fx.s1);

        assert!(eq_binders(
            &st,
            &ok(strip_lams(&st, 2, &fx.lam_t2)),
            &core_ops::strip_lams(2, &lam_t2)
        ));
        assert!(eq_binders(
            &st,
            &ok(strip_lams(&st, 0, &fx.lam_t2)),
            &core_ops::strip_lams(0, &lam_t2)
        ));
        assert!(eq_binders(
            &st,
            &ok(strip_lams(&st, 3, &fx.lam_t2)),
            &core_ops::strip_lams(3, &lam_t2)
        ));
        assert!(eq_binders(
            &st,
            &ok(strip_pis(&st, 2, &fx.pi_t)),
            &core_ops::strip_pis(2, &pi_t)
        ));
        assert!(eq_binders(
            &st,
            &ok(strip_pis(&st, 1, &fx.pi_t)),
            &core_ops::strip_pis(1, &pi_t)
        ));
        assert!(eq_binders(
            &st,
            &ok(strip_pis(&st, 3, &fx.pi_t)),
            &core_ops::strip_pis(3, &pi_t)
        ));

        let w = core_ops::pi_result(&pi_t);
        assert!(eq_e(&st, &ok(pi_result(&st, F, &fx.pi_t)), &w));
        let w = core_ops::pi_result(&cf);
        assert!(eq_e(&st, &ok(pi_result(&st, F, &fx.cf)), &w));
        assert_eq!(ok(pi_arity(&st, F, &fx.pi_t)), core_ops::pi_arity(&pi_t));
        assert_eq!(ok(pi_arity(&st, F, &fx.cf)), core_ops::pi_arity(&cf));
        assert!(eq_ol(
            &st,
            &ok(result_sort(&st, F, &fx.pi_s)),
            &core_ops::result_sort(&pi_s)
        ));
        assert!(eq_ol(
            &st,
            &ok(result_sort(&st, F, &fx.pi_t)),
            &core_ops::result_sort(&pi_t)
        ));
        assert!(eq_ol(
            &st,
            &ok(result_sort(&st, F, &fx.s1)),
            &core_ops::result_sort(&s1)
        ));
    }

    // --- telescopes, part 2: the instantiating entries (17) ------------------

    #[test]
    fn t_telescopes_instantiation() {
        let (mut st, fx) = fixture();
        let pi_t = den(&st, &fx.pi_t);
        let cf = den(&st, &fx.cf);
        let s1 = den(&st, &fx.s1);
        let lam_t2 = den(&st, &fx.lam_t2);
        let fv0 = den(&st, &fx.fv0);
        let two = vec![expr::dup(&cf), expr::dup(&s1)];
        let hs2 = vec![fx.cf.dup2(), fx.s1.dup2()];
        let one_cf = vec![expr::dup(&cf)];
        let hs1 = vec![fx.cf.dup2()];

        let w = core_ops::inst_pis(&pi_t, &two);
        let r = ok(inst_pis(&mut st, F, &fx.pi_t, &hs2));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::inst_pis(&pi_t, &Vec::new());
        let r = ok(inst_pis(&mut st, F, &fx.pi_t, &Vec::new()));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::inst_pis(&cf, &vec![expr::dup(&s1)]);
        let r = ok(inst_pis(&mut st, F, &fx.cf, &vec![fx.s1.dup2()]));
        assert!(eq_ope(&st, &r, &w));

        let w = core_ops::inst_pis_at(&two, &pi_t);
        let r = ok(inst_pis_at(&mut st, F, &hs2, &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_pis_at(&Vec::new(), &pi_t);
        let r = ok(inst_pis_at(&mut st, F, &Vec::new(), &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_pis_at(&one_cf, &lam_t2);
        let r = ok(inst_pis_at(&mut st, F, &hs1, &fx.lam_t2));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_lams_at(&two, &lam_t2);
        let r = ok(inst_lams_at(&mut st, F, &hs2, &fx.lam_t2));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_lams_at(&one_cf, &pi_t);
        let r = ok(inst_lams_at(&mut st, F, &hs1, &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));

        let w = core_ops::inst_pis_at_f_go(&Vec::new(), &two, 0, &pi_t, Vec::new());
        let r = ok(inst_pis_at_f_go(&mut st, F, &Vec::new(), &hs2, 0, &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_pis_at_f_go(
            &vec![expr::dup(&fv0)],
            &one_cf,
            0,
            &pi_t,
            Vec::new(),
        );
        let r = ok(inst_pis_at_f_go(
            &mut st,
            F,
            &vec![fx.fv0.dup2()],
            &hs1,
            0,
            &fx.pi_t,
        ));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_pis_at_f(&two, &pi_t);
        let r = ok(inst_pis_at_f(&mut st, F, &hs2, &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_pis_at_f(&one_cf, &lam_t2);
        let r = ok(inst_pis_at_f(&mut st, F, &hs1, &fx.lam_t2));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_lams_at_f_go(&Vec::new(), &two, 0, &lam_t2, Vec::new());
        let r = ok(inst_lams_at_f_go(
            &mut st,
            F,
            &Vec::new(),
            &hs2,
            0,
            &fx.lam_t2,
        ));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_lams_at_f(&two, &lam_t2);
        let r = ok(inst_lams_at_f(&mut st, F, &hs2, &fx.lam_t2));
        assert!(eq_pair(&st, &r, &w));
        let w = core_ops::inst_lams_at_f(&one_cf, &pi_t);
        let r = ok(inst_lams_at_f(&mut st, F, &hs1, &fx.pi_t));
        assert!(eq_pair(&st, &r, &w));

        let fv1 = den(&st, &fx.fv1);
        let w = core_ops::fvar_type_d(&fv1);
        assert!(eq_e(&st, &ok(fvar_type_d(&st, &fx.fv1)), &w));
        let w = core_ops::fvar_type_d(&cf);
        assert!(eq_e(&st, &ok(fvar_type_d(&st, &fx.cf)), &w));
    }

    // --- telescopes, part 3: spine, recursor rules, rebuilding (12) ----------

    #[test]
    fn t_telescopes_rebuilding() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let pi_t = den(&st, &fx.pi_t);
        let cf = den(&st, &fx.cf);
        let s1 = den(&st, &fx.s1);
        let two = vec![expr::dup(&cf), expr::dup(&s1)];
        let hs2 = vec![fx.cf.dup2(), fx.s1.dup2()];

        let w = core_ops::inst_spine(&two, 1, &big);
        let r = ok(inst_spine(&mut st, F, &hs2, 1, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::inst_spine(&Vec::new(), 0, &big);
        let r = ok(inst_spine(&mut st, F, &Vec::new(), 0, &fx.big));
        assert!(eq_e(&st, &r, &w));

        assert_eq!(
            ok(rec_rule_plain(&mut st, F, &fx.pi_t, 2, 2, 1)),
            core_ops::rec_rule_plain(&pi_t, 2, 2, 1)
        );
        assert_eq!(
            ok(rec_rule_plain(&mut st, F, &fx.pi_t, 1, 1, 1)),
            core_ops::rec_rule_plain(&pi_t, 1, 1, 1)
        );
        assert_eq!(
            ok(rec_rule_plain(&mut st, F, &fx.pi_t, 2, 1, 2)),
            core_ops::rec_rule_plain(&pi_t, 2, 1, 2)
        );
        assert_eq!(
            ok(rec_rule_plain(&mut st, F, &fx.big, 2, 2, 1)),
            core_ops::rec_rule_plain(&big, 2, 2, 1)
        );

        let w = core_ops::pis_to_lams(2, &pi_t, &cf);
        let r = ok(pis_to_lams(&mut st, 2, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::pis_to_lams(0, &pi_t, &cf);
        let r = ok(pis_to_lams(&mut st, 0, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::pis_to_lams(3, &pi_t, &cf);
        let r = ok(pis_to_lams(&mut st, 3, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::replace_pi_body(2, &pi_t, &cf);
        let r = ok(replace_pi_body(&mut st, 2, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::replace_pi_body(1, &pi_t, &cf);
        let r = ok(replace_pi_body(&mut st, 1, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::replace_pi_body(3, &pi_t, &cf);
        let r = ok(replace_pi_body(&mut st, 3, &fx.pi_t, &fx.cf));
        assert!(eq_ope(&st, &r, &w));
    }

    // --- the packed range fields (19) ---------------------------------------

    #[test]
    fn t_packed_range_fields() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let let_t = den(&st, &fx.let_t);
        let b2 = den(&st, &fx.b2);
        let fv1 = den(&st, &fx.fv1);
        let pi_t = den(&st, &fx.pi_t);

        assert_eq!(
            ok(bvar_bound_memo(&mut st, F, &fx.big)),
            core_ops::bvar_bound(&big)
        );
        assert_eq!(
            ok(bvar_bound_memo(&mut st, F, &fx.let_t)),
            core_ops::bvar_bound(&let_t)
        );
        assert_eq!(
            ok(bvar_bound_memo(&mut st, F, &fx.b2)),
            core_ops::bvar_bound(&b2)
        );
        assert_eq!(
            ok(bvar_bound_go(&mut st, F, &fx.big)),
            core_ops::bvar_bound(&big)
        );
        assert_eq!(
            ok(fvar_range_memo(&mut st, F, &fx.big)),
            core_ops::fvar_range(&big)
        );
        assert_eq!(
            ok(fvar_range_memo(&mut st, F, &fx.fv1)),
            core_ops::fvar_range(&fv1)
        );
        assert_eq!(
            ok(fvar_range_go(&mut st, F, &fx.big)),
            core_ops::fvar_range(&big)
        );
        assert_eq!(ok(bvar_b(&mut st, F, &fx.big)), core_ops::bvar_b(&big));
        assert_eq!(ok(bvar_b(&mut st, F, &fx.b2)), core_ops::bvar_b(&b2));
        assert_eq!(ok(fvar_b(&mut st, F, &fx.big)), core_ops::fvar_b(&big));
        assert_eq!(ok(fvar_b(&mut st, F, &fx.fv1)), core_ops::fvar_b(&fv1));
        // `Expr.hasFvarFast` and `Expr.looseBVarsBoundedFast` are the field
        // reads themselves; con-ron-core spells them at the call site, so the
        // comparison partner is the definition.
        assert_eq!(
            ok(has_fvar_fast(&mut st, F, &fx.big)),
            core_ops::fvar_b(&big) != 0
        );
        assert_eq!(
            ok(has_fvar_fast(&mut st, F, &fx.pi_t)),
            core_ops::fvar_b(&pi_t) != 0
        );
        assert_eq!(
            ok(loose_bvars_bounded_fast(&mut st, F, 3, &fx.big)),
            core_ops::bvar_b(&big) <= 3
        );
        assert_eq!(
            ok(loose_bvars_bounded_fast(&mut st, F, 0, &fx.big)),
            core_ops::bvar_b(&big) <= 0
        );
        // the field read and the walk agree, which is con-leche's `bvarB_eq` /
        // `fvarB_eq` / `hasFvar_eq` at the fixture
        assert_eq!(ok(bvar_b(&mut st, F, &fx.big)), core_ops::bvar_bound(&big));
        assert_eq!(ok(fvar_b(&mut st, F, &fx.big)), core_ops::fvar_range(&big));
        assert_eq!(
            ok(has_fvar_fast(&mut st, F, &fx.big)),
            core_ops::has_fvar(&big)
        );
        assert_eq!(
            ok(loose_bvars_bounded_fast(&mut st, F, 3, &fx.big)),
            core_ops::loose_bvars_bounded(3, &big)
        );
    }

    // --- `abstract1` (6) -----------------------------------------------------

    #[test]
    fn t_abstract1() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let fv0 = den(&st, &fx.fv0);

        let w = core_ops::abstract1(&big, 0, 0);
        let r = ok(abstract1_fast(&mut st, F, &fx.big, 0, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract1(&big, 1, 0);
        let r = ok(abstract1_fast(&mut st, F, &fx.big, 1, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract1(&big, 2, 0);
        let r = ok(abstract1_fast(&mut st, F, &fx.big, 2, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract1(&big, 1, 3);
        let r = ok(abstract1_fast(&mut st, F, &fx.big, 1, 3));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract1(&fv0, 0, 0);
        let r = ok(abstract1_fast(&mut st, F, &fx.fv0, 0, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::abstract1(&big, 1, 0);
        let r = ok(abstract1_go(&mut st, 1, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `lowerBVars` (5) ----------------------------------------------------

    #[test]
    fn t_lower_bvars() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);

        let w = core_ops::lower_bvars(1, 0, &big);
        let r = ok(lower_bvars_fast(&mut st, F, 1, 0, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lower_bvars(2, 0, &big);
        let r = ok(lower_bvars_fast(&mut st, F, 2, 0, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lower_bvars(1, 1, &big);
        let r = ok(lower_bvars_fast(&mut st, F, 1, 1, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lower_bvars(5, 0, &big);
        let r = ok(lower_bvars_fast(&mut st, F, 5, 0, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::lower_bvars(1, 0, &big);
        let r = ok(lower_bvars_go(&mut st, 1, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));
    }

    // --- `instantiate1Lift` and `instPisAtLift` (8) --------------------------

    #[test]
    fn t_instantiate1_lift() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let cf = den(&st, &fx.cf);
        let b1 = den(&st, &fx.b1);
        let let_t = den(&st, &fx.let_t);
        let b0 = den(&st, &fx.b0);
        let pi_t = den(&st, &fx.pi_t);
        let lam_t2 = den(&st, &fx.lam_t2);

        let w = core_ops::instantiate1_lift(&big, &cf, 0);
        let r = ok(instantiate1_lift_fast(&mut st, F, &fx.big, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1_lift(&big, &b1, 0);
        let r = ok(instantiate1_lift_fast(&mut st, F, &fx.big, &fx.b1, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1_lift(&big, &let_t, 1);
        let r = ok(instantiate1_lift_fast(&mut st, F, &fx.big, &fx.let_t, 1));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1_lift(&let_t, &b0, 0);
        let r = ok(instantiate1_lift_fast(&mut st, F, &fx.let_t, &fx.b0, 0));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate1_lift(&big, &cf, 0);
        let r = ok(instantiate1_lift_go(&mut st, &fx.cf, F, &fx.big, 0));
        assert!(eq_e(&st, &r, &w));

        let w = core_ops::inst_pis_at_lift(&vec![expr::dup(&cf), expr::dup(&b0)], &pi_t);
        let r = ok(inst_pis_at_lift(
            &mut st,
            F,
            &vec![fx.cf.dup2(), fx.b0.dup2()],
            &fx.pi_t,
        ));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::inst_pis_at_lift(&Vec::new(), &pi_t);
        let r = ok(inst_pis_at_lift(&mut st, F, &Vec::new(), &fx.pi_t));
        assert!(eq_ope(&st, &r, &w));
        let w = core_ops::inst_pis_at_lift(&vec![expr::dup(&cf)], &lam_t2);
        let r = ok(inst_pis_at_lift(&mut st, F, &vec![fx.cf.dup2()], &fx.lam_t2));
        assert!(eq_ope(&st, &r, &w));
    }

    // --- equality, and the two derived bits (11) ----------------------------

    #[test]
    fn t_equality_and_bits() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let let_t = den(&st, &fx.let_t);
        let s0 = den(&st, &fx.s0);
        let s1 = den(&st, &fx.s1);
        let pi_t = den(&st, &fx.pi_t);
        let su = den(&st, &fx.su);
        let cb = den(&st, &fx.cb);

        assert_eq!(
            expr_ptr_beq(&fx.big, &fx.big),
            core_ops::expr_ptr_beq(&big, &big)
        );
        assert_eq!(
            expr_ptr_beq(&fx.big, &fx.let_t),
            core_ops::expr_ptr_beq(&big, &let_t)
        );
        assert_eq!(
            expr_ptr_beq(&fx.s0, &fx.s1),
            core_ops::expr_ptr_beq(&s0, &s1)
        );
        // interning is hash-consing, so a rebuilt node is the SAME handle and
        // the index test is the structural test (`denoteE_inj`, task #97a)
        let r = ok(intern_e(
            &mut st,
            ENodeView::App(fx.cf.dup2(), fx.b0.dup2()),
        ));
        assert!(expr_ptr_beq(&r, &fx.ap1));

        assert_eq!(
            lidx_has_param(&st, &fx.pu),
            core_level::level_has_param(&den_l(&st, &fx.pu))
        );
        assert_eq!(
            lidx_has_param(&st, &fx.z),
            core_level::level_has_param(&den_l(&st, &fx.z))
        );
        assert_eq!(
            lidx_has_param(&st, &fx.one),
            core_level::level_has_param(&den_l(&st, &fx.one))
        );
        assert_eq!(
            eidx_has_level_param(&st, &fx.big),
            core_ops::has_level_param(&big)
        );
        assert_eq!(
            eidx_has_level_param(&st, &fx.pi_t),
            core_ops::has_level_param(&pi_t)
        );
        assert_eq!(
            eidx_has_level_param(&st, &fx.su),
            core_ops::has_level_param(&su)
        );
        assert_eq!(
            eidx_has_level_param(&st, &fx.cb),
            core_ops::has_level_param(&cb)
        );
    }

    // --- `instantiateLevelParams` (6) ---------------------------------------

    #[test]
    fn t_instantiate_level_params() {
        let (mut st, fx) = fixture();
        let big = den(&st, &fx.big);
        let su = den(&st, &fx.su);
        let cb = den(&st, &fx.cb);
        let pi_t = den(&st, &fx.pi_t);
        let ks = vec![den_n(&st, &fx.u_n)];
        let zs = vec![den_l(&st, &fx.z)];
        let ps = vec![den_l(&st, &fx.pu)];
        let hks = vec![fx.u_n.dup2()];

        let w = core_ops::instantiate_level_params(&ks, &zs, &big);
        let r = ok(inst_lp_fast(&mut st, F, &hks, &fx.us_z, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_level_params(&ks, &ps, &big);
        let r = ok(inst_lp_fast(&mut st, F, &hks, &fx.us_u, &fx.big));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_level_params(&ks, &zs, &su);
        let r = ok(inst_lp_fast(&mut st, F, &hks, &fx.us_z, &fx.su));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_level_params(&ks, &zs, &cb);
        let r = ok(inst_lp_fast(&mut st, F, &hks, &fx.us_z, &fx.cb));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_level_params(&ks, &zs, &pi_t);
        let r = ok(inst_lp_fast(&mut st, F, &hks, &fx.us_z, &fx.pi_t));
        assert!(eq_e(&st, &r, &w));
        let w = core_ops::instantiate_level_params(&ks, &zs, &big);
        let r = ok(inst_lp_go(&mut st, &ks, &zs, F, &fx.big));
        assert!(eq_e(&st, &r, &w));
    }

    // --- the store primitives of `Monad.lean` (6) ---------------------------

    #[test]
    fn t_monad_primitives() {
        let (mut st, fx) = fixture();

        match ok(view(&st, &fx.big)) {
            ENodeView::Lam(ty, body, _) => {
                assert!(ty.eq2(&fx.s0));
                assert!(!body.eq2(&fx.s0));
            }
            _ => panic!("`big` is a λ"),
        }
        let u = ok(crate::arena::monad::read_level(&st, &fx.pu));
        assert!(core_level::beq(
            &u,
            &core_level::param(name::mk_str(name::anonymous(), cp("u")))
        ));
        let n = ok(crate::arena::monad::read_name(&st, &fx.foo));
        assert!(name::beq(&n, &name::mk_str(name::anonymous(), cp("foo"))));

        let l = core_level::succ(core_level::succ(core_level::zero()));
        let hl = ok(crate::arena::monad::intern_level(&mut st, &l));
        assert!(core_level::beq(&den_l(&st, &hl), &l));

        let nm = name::mk_str(name::mk_str(name::anonymous(), cp("a")), cp("b"));
        let hn = ok(crate::arena::monad::intern_name(&mut st, &nm));
        assert!(name::beq(&den_n(&st, &hn), &nm));

        let us = vec![
            core_level::zero(),
            core_level::param(name::mk_str(name::anonymous(), cp("u"))),
        ];
        let hus = ok(crate::arena::monad::intern_levels(&mut st, &us));
        let back = ok(crate::arena::monad::read_levels(&st, &hus));
        assert!(back.len() == 2);
        assert!(core_level::beq(&back[0], &us[0]));
        assert!(core_level::beq(&back[1], &us[1]));
    }

    // --- fuel exhaustion fails rather than answering wrongly (3) ------------

    #[test]
    fn t_fuel_exhaustion() {
        let (mut st, fx) = fixture();
        // `big`'s loose-bvar bound is 0, so the derived-word cutoff answers it
        // at any fuel; `let_t`'s is 1, so the walk really descends and fuel 1
        // runs out.
        let w = core_ops::instantiate1(&den(&st, &fx.big), &den(&st, &fx.cf), 0);
        let r = ok(instantiate1_fast(&mut st, 1, &fx.big, &fx.cf, 0));
        assert!(eq_e(&st, &r, &w));
        assert!(instantiate1_fast(&mut st, 1, &fx.let_t, &fx.cf, 0).is_err());
        assert!(size_b(&st, 0, &fx.big).is_err());
    }
}
