//! **The pure checker core's syntactic layer** —
//! `ConLeche/Kernel/Core.lean`'s readers, pinned tables, install-time rule
//! bits and small helpers, plus the three fuel constants of the knot's loops
//! and `checkFuel` (`:2903`).  The head of the file (`CheckError`, `CheckM`)
//! is `core_types.rs` (task #14).
//!
//! The module is `core_k`, not `core`: `core` is a Rust prelude crate name,
//! and `crate::kernel::core` would shadow it for every `use` inside this
//! crate.  The `k` is for *kernel* — con-leche's `ConLeche.Kernel.Core`.
//!
//! ## What is here and what moved (task #23)
//!
//! Task #18 ported `Kernel/Core.lean`'s *bodies* here and tied them with
//! `Cached/CoreC.lean`'s wrappers.  `CoreC.lean` has its own twin of almost
//! every one of those bodies, and it is the twins the executed checker runs:
//! they read the level operations through `lsimpC`/`lnzC`/`eqvC`, the stored
//! constants through `ienv`/`constTyAt`/`constValAt`/`ruleRhsAt`, and the
//! bulk instantiations through `instC`, and five of them are a different
//! *algorithm* (bulk beta, the head-normalization loop, bulk telescope
//! consumption, the binder-telescope loops).  Task #23 ported them and
//! re-pointed the knot, so **the bodies are now
//! `crate::cached::core_c`** and the ones here are gone: a superseded body
//! threads the same knot, so keeping it would have doubled the mutual block
//! of the generated Lean for functions nothing executes (DESIGN.md §3.1).
//! Their `Core.lean` citations are the second `con-leche:` line on the twin
//! in `core_c`.
//!
//! What stays here is everything the cached bodies *call*:
//!
//! * the syntactic readers and guards — `unfoldable_head`, `head_hint`,
//!   `same_const_heads`, `raw_nat_lit`, `is_ctor_app`,
//!   `eta_ctor_shape`, `is_bool_true`, `quick_pair`, `succ_of`,
//!   `str_expansion_fires`, `pw_written`, `lift_fueled`.  **Six of these
//!   carry a second citation to `Cached/StateC.lean`'s `*C` index guards**
//!   (`isCtorAppC`, `headHintC`, `unfoldableHeadC`,
//!   `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`): those are the same
//!   function, since the port reads the environment through `FEnv` anyway
//!   (deviation 3 below).  So are `litToCtorIfNatI` and `annotBinderMetaI`,
//!   whose twins are the spec's under a `pure`;
//! * the pinned name tables and the `Nat`-operation pin sets;
//! * the install-time rule bits (`rec_rule_bits`,
//!   `rec_rule_k`) and the shape conjunctions the cached certificates read
//!   (`struct_eta_shape_ok`, `unit_shape_ok`, `proj_fire_shape_ok`,
//!   `fab_scope_ok`, `proj_entry_fire_ok`, `and_rescue_slots`);
//! * the pure pieces of the inference clauses (`infer_fvar`,
//!   `infer_lit_nat`, `infer_lit_str`, `infer_proj_at`,
//!   `proj_type_at_checked`, `proj_entry_type_at`);
//! * the four loop budgets (`whnf_core_loop_fuel`, `whnf_loop_fuel`,
//!   `defeq_loop_fuel`, `check_fuel`);
//! * the `Vec` helpers and the owning environment probes.
//!
//! Four functions here are **dead and deliberately kept**, as task #18's
//! eleven were, so the provenance ledger stays in step with its source:
//! `beta_gate_fires` (the pure β gate; the cached sites read
//! `mode.betaSkip`), `eta_projs`/`eta_projs_from` (superseded by
//! `core_c::proj_apps_i`, but `eta_fab_args_e` is written
//! against them, and all three are dead in the Lean too), and `consts_resolve` (whose
//! memoized `ExprC` twin is `state_c::consts_resolve_fc`).
//!
//! ## The knot is closed by name, not by a record (DESIGN.md §3.1)
//!
//! `Kernel/Core.lean`'s bodies are non-recursive, written against a record
//! `r : CoreFns m` of the six mutually recursive entry points.  The port
//! drops the record: where a body writes `r.whnf d x` the Rust writes
//! `core_c::whnf(mode, fuel, st, fe, d, &x)` — the *wrapper*, by name — and
//! the record's parameter is replaced by the `fuel: u64` the wrapper
//! decrements.  The whole set (the bodies in `core_c` and its six wrappers)
//! is one block of plain mutually recursive functions; no trait is in the
//! recursion and there are no closures.
//!
//! Four consequences, each a deviation from the cited text that applies
//! *everywhere* and is therefore recorded once rather than on every item:
//!
//! 1. **`mode` is threaded explicitly.**  In the Lean the knot closes over
//!    the mode, so a body that reads no mode itself takes none.
//! 2. **The state is `&mut CState`** — `CheckCM`'s `StateT CState`.  No
//!    function *in this module* takes it any more; that is the measure of
//!    what moved.
//! 3. **The environment is the index `FEnv`.**  `Kernel/Core.lean`'s bodies
//!    take `env : Env` and call `env.find?`/`env.findProj?`; the executed
//!    checker reads through the index, and con-leche writes the `F`-mirror
//!    twins (`FEnv.lean:98-153`) and the `*C` guards (`StateC.lean:48-112`)
//!    for exactly that.  The port has one spelling, `fe: &FEnv` with
//!    `fenv::find`/`fenv::find_proj`, so those twins are *one* Rust function
//!    with two or three citations.
//! 4. **Depths, indices and arities are `u64`** (DESIGN.md §3.3); only
//!    `Literal.natVal` and the `Nat`-operation fast path use `ron::Nat`.
//!
//! ## The other standing deviations
//!
//! * **`List` becomes `Vec` with `*_from` index helpers** (task #3's
//!   pattern): `pi_residual`, `nat_op_deps`, `and_rescue_slots` and friends.
//!   `List.take`/`.drop`/`++` copy a `Vec` spine (`take_exprs`,
//!   `drop_exprs`, `append_exprs`) where Lean's sharing is free.
//! * **`&&`/`∧` cascades become `if` nests** (task #3's pattern 9), so the
//!   generated Lean keeps the cited short-circuit order.
//! * **Lean string literals are `const […]: [u32; N]` code points**
//!   (DESIGN.md §3.3, task #14): every throw site carries its message as a
//!   `const` in its own body and builds it with `core_types::code_points`.
//!   Interpolated messages (`s!"unknown constant {n}"`) drop the
//!   interpolation — DESIGN.md §3.1: message strings need not match, the
//!   theorem never reads them.
//! * **A pattern's fields are copied into owned locals** (`expr::dup`, an
//!   `P` bump) wherever they outlive the `match`; this is what Lean's value
//!   semantics gives for free, and it is task #14's rule against holding a
//!   borrow across a state-touching branch.

use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::env;
use crate::kernel::env::{
    ConstantInfo, ProjEntry, RecRule,
};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprView, Literal};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::ron::nat;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `Vec` helpers for the `List` operations the Lean uses for free
// ---------------------------------------------------------------------------



/// con-leche: none — the index recursion behind `drop_exprs`
/// The accumulator is passed by value and returned (task #6's rule).
pub fn drop_exprs_from(xs: &Vec<Expr>, k: usize, out: Vec<Expr>) -> Vec<Expr> {
    if k >= xs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&xs[k]));
        drop_exprs_from(xs, k + 1, out)
    }
}


/// con-leche: none — the index recursion behind `drop_exprs_n`
pub fn drop_exprs_n_from(xs: &Vec<Expr>, n: u64, i: usize) -> Vec<Expr> {
    if n == 0 {
        drop_exprs_from(xs, i, Vec::new())
    } else if i >= xs.len() {
        Vec::new()
    } else {
        drop_exprs_n_from(xs, n - 1, i + 1)
    }
}


/// con-leche: none — the index recursion behind `take_exprs_n`
/// The accumulator is passed by value and returned (task #6's rule).
pub fn take_exprs_n_from(xs: &Vec<Expr>, n: u64, i: usize, out: Vec<Expr>) -> Vec<Expr> {
    if n == 0 || i >= xs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&xs[i]));
        take_exprs_n_from(xs, n - 1, i + 1, out)
    }
}

/// con-leche: none — `List.append` on a `Vec`; Lean's `++` shares the tail
/// `xs ++ ys`, consuming `xs` and copying `ys`' spine.
pub fn append_exprs(xs: Vec<Expr>, ys: &Vec<Expr>) -> Vec<Expr> {
    append_exprs_from(xs, ys, 0)
}

/// con-leche: none — the index recursion behind `append_exprs`
pub fn append_exprs_from(xs: Vec<Expr>, ys: &Vec<Expr>, i: usize) -> Vec<Expr> {
    if i >= ys.len() {
        xs
    } else {
        let mut xs = xs;
        xs.push(expr::dup(&ys[i]));
        append_exprs_from(xs, ys, i + 1)
    }
}

/// con-leche: none — `Expr` list equality; Lean's `List.contains` on `fvarLeaves`
/// Is the pair `(i, ty)` one of `ys`?  The `BEq (Nat × Expr)` the cited
/// `major.fvarLeaves.contains l` uses is `Nat` equality and `Expr.beq`.
pub fn leaf_contains(ys: &Vec<(u64, Expr)>, i: u64, ty: &Expr) -> bool {
    leaf_contains_from(ys, i, ty, 0)
}

/// con-leche: none — the index recursion behind `leaf_contains`
pub fn leaf_contains_from(ys: &Vec<(u64, Expr)>, i: u64, ty: &Expr, j: usize) -> bool {
    if j >= ys.len() {
        false
    } else if ys[j].0 == i && expr::beq(&ys[j].1, ty) {
        true
    } else {
        leaf_contains_from(ys, i, ty, j + 1)
    }
}


/// con-leche: ConLeche/Kernel/Core.lean:577-749 majorToCtor
/// The index recursion behind `fvar_leaves_subset`.
pub fn fvar_leaves_subset_from(
    xs: &Vec<(u64, Expr)>,
    ys: &Vec<(u64, Expr)>,
    i: usize,
) -> bool {
    if i >= xs.len() {
        true
    } else if leaf_contains(ys, xs[i].0, &xs[i].1) {
        fvar_leaves_subset_from(xs, ys, i + 1)
    } else {
        false
    }
}

/// con-leche: none — Lean's `toString` on a `Nat` (the runtime's `Nat.repr`)
/// `toString i` for a `Nat` index: the decimal code points, most significant
/// digit first, `0` for zero.  Lean's `Nat.toString` is the runtime's; on the
/// `u64` of DESIGN.md §3.3 this is the recursion that produces it.
pub fn nat_to_dec(i: u64) -> Vec<u32> {
    nat_to_dec_go(i, Vec::new())
}

/// con-leche: none — Lean's `toString` on a `Nat` (the runtime's `Nat.repr`)
/// The digit recursion behind `nat_to_dec`: the quotient's digits are pushed
/// before the last one, so the result is most-significant first.
pub fn nat_to_dec_go(i: u64, out: Vec<u32>) -> Vec<u32> {
    if i < 10 {
        let mut out = out;
        out.push(48 + (i as u32));
        out
    } else {
        let mut out = nat_to_dec_go(i / 10, out);
        out.push(48 + ((i % 10) as u32));
        out
    }
}

// ---------------------------------------------------------------------------
// Environment probes (task #14's rule: never hold a container's borrow
// across a branch that touches the state)
// ---------------------------------------------------------------------------






// ---------------------------------------------------------------------------
// `liftFueled` and the small readers (`Core.lean:109-206`)
// ---------------------------------------------------------------------------




// ---------------------------------------------------------------------------
// Delta (`Core.lean:217-266`)
// ---------------------------------------------------------------------------




// ---------------------------------------------------------------------------
// `Nat` literals (`Core.lean:269-346`)
// ---------------------------------------------------------------------------






/// con-leche: ConLeche/Kernel/CoreDefs.lean:161-186 Expr.constsResolve
/// Do all constants referenced in `e` (including inside `fvar` type
/// annotations) resolve in the environment?  A `Nat` literal implicitly
/// references the `Nat` basis constants, a `String` literal additionally the
/// string-support ones.  Checked once per declaration by the install; the
/// core never calls it.
pub fn consts_resolve(fe: &FEnv, e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Bvar(_) => true,
        ExprView::Sort(_) => true,
        ExprView::Lit(Literal::NatVal(_)) => nat_trio_stored(fe),
        ExprView::Lit(Literal::StrVal(_)) => {
            if nat_trio_stored(fe) {
                str_support_stored(fe)
            } else {
                false
            }
        }
        ExprView::Const(n, _) => fenv::find(fe, n).is_some(),
        ExprView::Fvar(_, ty) => consts_resolve(fe, ty),
        ExprView::App(f, a) => {
            if consts_resolve(fe, f) {
                consts_resolve(fe, a)
            } else {
                false
            }
        }
        ExprView::Lam(ty, body, _) => {
            if consts_resolve(fe, ty) {
                consts_resolve(fe, body)
            } else {
                false
            }
        }
        ExprView::ForallE(ty, body, _) => {
            if consts_resolve(fe, ty) {
                consts_resolve(fe, body)
            } else {
                false
            }
        }
        ExprView::LetE(ty, val, body) => {
            if consts_resolve(fe, ty) {
                if consts_resolve(fe, val) {
                    consts_resolve(fe, body)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprView::Proj(s, _, pe) => {
            if fenv::find(fe, s).is_some() {
                consts_resolve(fe, pe)
            } else {
                false
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:161-186 Expr.constsResolve
/// The `.lit (.natVal _)` arm's three `isSome` tests, factored out (the
/// `.strVal` arm opens with the same three).
pub fn nat_trio_stored(fe: &FEnv) -> bool {
    if fenv::find(fe, &basis_names::nat_name()).is_some() {
        if fenv::find(fe, &basis_names::nat_zero_name()).is_some() {
            fenv::find(fe, &basis_names::nat_succ_name()).is_some()
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:161-186 Expr.constsResolve
/// The `.lit (.strVal _)` arm's seven further `isSome` tests.
pub fn str_support_stored(fe: &FEnv) -> bool {
    if fenv::find(fe, &basis_names::string_name()).is_some() {
        if fenv::find(fe, &basis_names::string_of_list_name()).is_some() {
            if fenv::find(fe, &basis_names::list_name()).is_some() {
                if fenv::find(fe, &basis_names::list_nil_name()).is_some() {
                    if fenv::find(fe, &basis_names::list_cons_name()).is_some() {
                        if fenv::find(fe, &basis_names::char_name()).is_some() {
                            fenv::find(fe, &basis_names::char_of_nat_name()).is_some()
                        } else {
                            false
                        }
                    } else {
                        false
                    }
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}



// ---------------------------------------------------------------------------
// String literals (`Core.lean:365-475`)
// ---------------------------------------------------------------------------


/// con-leche: ConLeche/Kernel/CoreDefs.lean:214-225 strLitToConstructor
/// The `foldr` of `str_lit_to_constructor`, downwards from the end: `acc` is
/// the list built from `s[i..]`, so `i = s.len()` is the `init` and each step
/// conses `s[i - 1]`.
pub fn str_lit_cons_from(s: &Vec<u32>, i: usize, acc: Expr) -> Expr {
    if i == 0 {
        acc
    } else {
        let c: u32 = s[i - 1];
        let ch = expr::app(
            expr::mk_const(basis_names::char_of_nat_name(), Vec::new()),
            expr::lit(expr::literal_nat(nat::from_u64(c as u64))),
        );
        let cell = expr::app(
            expr::app(
                expr::app(
                    expr::mk_const(
                        basis_names::list_cons_name(),
                        level::singleton(level::zero()),
                    ),
                    expr::mk_const(basis_names::char_name(), Vec::new()),
                ),
                ch,
            ),
            acc,
        );
        str_lit_cons_from(s, i - 1, cell)
    }
}










// ---------------------------------------------------------------------------
// The certified structural-`Nat` operations (`Core.lean:505-775`)
// ---------------------------------------------------------------------------


/// con-leche: ConLeche/Kernel/CoreDefs.lean:359 natPredName
/// `Nat.pred`.
pub fn nat_pred_name() -> Name {
    const S: [u32; 4] = [112, 114, 101, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:360 natAddName
/// `Nat.add`.
pub fn nat_add_name() -> Name {
    const S: [u32; 3] = [97, 100, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:361 natSubName
/// `Nat.sub`.
pub fn nat_sub_name() -> Name {
    const S: [u32; 3] = [115, 117, 98];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:362 natMulName
/// `Nat.mul`.
pub fn nat_mul_name() -> Name {
    const S: [u32; 3] = [109, 117, 108];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:363 natPowName
/// `Nat.pow`.
pub fn nat_pow_name() -> Name {
    const S: [u32; 3] = [112, 111, 119];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:364 natBeqName
/// `Nat.beq`.
pub fn nat_beq_name() -> Name {
    const S: [u32; 3] = [98, 101, 113];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:365 natBleName
/// `Nat.ble`.
pub fn nat_ble_name() -> Name {
    const S: [u32; 3] = [98, 108, 101];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:366 natDivName
/// `Nat.div`.
pub fn nat_div_name() -> Name {
    const S: [u32; 3] = [100, 105, 118];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:367 natModName
/// `Nat.mod`.
pub fn nat_mod_name() -> Name {
    const S: [u32; 3] = [109, 111, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:368 natGcdName
/// `Nat.gcd`.
pub fn nat_gcd_name() -> Name {
    const S: [u32; 3] = [103, 99, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:369 natLandName
/// `Nat.land`.
pub fn nat_land_name() -> Name {
    const S: [u32; 4] = [108, 97, 110, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:370 natLorName
/// `Nat.lor`.
pub fn nat_lor_name() -> Name {
    const S: [u32; 3] = [108, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:371 natXorName
/// `Nat.xor`.
pub fn nat_xor_name() -> Name {
    const S: [u32; 3] = [120, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:372 natShiftLeftName
/// `Nat.shiftLeft`.
pub fn nat_shift_left_name() -> Name {
    const S: [u32; 9] = [115, 104, 105, 102, 116, 76, 101, 102, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:373 natShiftRightName
/// `Nat.shiftRight`.
pub fn nat_shift_right_name() -> Name {
    const S: [u32; 10] = [115, 104, 105, 102, 116, 82, 105, 103, 104, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:374 boolName
/// `Bool`.
pub fn bool_name() -> Name {
    const S: [u32; 4] = [66, 111, 111, 108];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:375 boolTrueName
/// `Bool.true`.
pub fn bool_true_name() -> Name {
    const S: [u32; 4] = [116, 114, 117, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:376 boolFalseName
/// `Bool.false`.
pub fn bool_false_name() -> Name {
    const S: [u32; 5] = [102, 97, 108, 115, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}















/// con-leche: ConLeche/Kernel/CoreDefs.lean:552-568 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:129-142 natOpGuardF
/// The cited `(natOpDeps c).all (fun n => match env.find? n with | some
/// (.defnInfo cv _ _) => cv.levelParams.isEmpty | _ => false)` predicate, at
/// one dependency (task #14's per-element rule).
pub fn defn_lp_empty(fe: &FEnv, n: &Name) -> bool {
    match fenv::find(fe, n) {
        Some(ConstantInfo::DefnInfo(cv, _, _)) => cv.level_params.len() == 0,
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:552-568 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:129-142 natOpGuardF
/// The `List.all` of `nat_op_guard`, as an index recursion.
pub fn deps_all_stored(fe: &FEnv, deps: &Vec<Name>, i: usize) -> bool {
    if i >= deps.len() {
        true
    } else if defn_lp_empty(fe, &deps[i]) {
        deps_all_stored(fe, deps, i + 1)
    } else {
        false
    }
}



/// con-leche: ConLeche/Kernel/CoreDefs.lean:582-588 Expr.substConst0
/// Substitute the level-monomorphic constant `n` by `r` through an
/// application spine (the certification equations' self-references; the
/// equation sides are binder-free, so only `app` recurses).
pub fn subst_const0(n: &Name, r: &Expr, e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::Const(c, us) => {
            if us.len() == 0 && name::beq(c, n) {
                expr::dup(r)
            } else {
                expr::dup(e)
            }
        }
        ExprView::App(f, a) => expr::app(subst_const0(n, r, f), subst_const0(n, r, a)),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:590-606 Expr.substConstAll
/// Substitute the level-monomorphic constant `n` by the *closed* term `r`
/// everywhere, including under binders.  `fvar` annotations are not entered:
/// the substitution runs on closed input terms only.
pub fn subst_const_all(n: &Name, r: &Expr, e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::Const(c, us) => {
            if us.len() == 0 && name::beq(c, n) {
                expr::dup(r)
            } else {
                expr::dup(e)
            }
        }
        ExprView::App(f, a) => expr::app(subst_const_all(n, r, f), subst_const_all(n, r, a)),
        ExprView::Lam(ty, b, mb) => expr::lam(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, b),
            expr::binder_meta_dup(mb),
        ),
        ExprView::ForallE(ty, b, mb) => expr::forall_e(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, b),
            expr::binder_meta_dup(mb),
        ),
        ExprView::LetE(ty, v, b) => expr::let_e(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, v),
            subst_const_all(n, r, b),
        ),
        ExprView::Proj(s, i, pe) => expr::proj(name::dup(s), *i, subst_const_all(n, r, pe)),
        _ => expr::dup(e),
    }
}







// ---------------------------------------------------------------------------
// Telescope certificates and proof irrelevance (`Core.lean:848-981`)
// ---------------------------------------------------------------------------


/// con-leche: ConLeche/Kernel/CoreDefs.lean:670-675 piResidual
/// The index recursion behind `pi_residual`.
pub fn pi_residual_from(e: &Expr, args: &Vec<Expr>, i: usize) -> Option<Expr> {
    if i >= args.len() {
        Some(expr::dup(e))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(_, b, _) => {
                let next = expr_ops::instantiate1(b, &args[i], 0);
                pi_residual_from(&next, args, i + 1)
            }
            _ => None,
        }
    }
}

// ---------------------------------------------------------------------------
// Structure eta (`Core.lean:983-1213`)
// ---------------------------------------------------------------------------

/// con-leche: none — the `[e]` singleton list of `targs ++ [b]`, as a `Vec`
/// A one-element `Vec<Expr>` (`level::singleton` is its `Level` twin).
pub fn expr_singleton(e: &Expr) -> Vec<Expr> {
    let mut v: Vec<Expr> = Vec::new();
    v.push(expr::dup(e));
    v
}


/// con-leche: ConLeche/Kernel/CoreDefs.lean:694-704 etaProjs
/// The index recursion behind `eta_projs` (the cited
/// `(List.range nF).map`), with the slot kind decided once by the caller.
pub fn eta_projs_from(
    tower: bool,
    t: &Name,
    us: &Vec<Level>,
    targs: &Vec<Expr>,
    b: &Expr,
    n_f: u64,
    j: u64,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if j >= n_f {
        out
    } else {
        let mut out = out;
        if tower {
            out.push(expr::proj(name::dup(t), j, expr::dup(b)));
        } else {
            let spine = append_exprs(env::exprs_copy(targs), &expr_singleton(b));
            out.push(expr_ops::mk_app_n(
                expr::mk_const(env::proj_fn_name(t, j), env::levels_copy(us)),
                &spine,
            ));
        }
        eta_projs_from(tower, t, us, targs, b, n_f, j + 1, out)
    }
}





/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-751 ProjEntry.fireOk
/// **The tower-fire guard**: at a `Prop`-declared structure the field's guard
/// level must be a proposition at this instantiation; at every other family
/// the rule fires unconditionally.
pub fn proj_entry_fire_ok(entry: &ProjEntry, us: &Vec<Level>) -> bool {
    let struct_prop = match level::is_equiv(&entry.struct_sort, &level::zero()) {
        Some(true) => true,
        Some(false) => false,
        None => false,
    };
    if !struct_prop {
        true
    } else {
        let fs = level::subst(&entry.level_params, us, &entry.field_sort);
        match level::is_equiv(&fs, &level::zero()) {
            Some(true) => true,
            Some(false) => false,
            None => false,
        }
    }
}


/// con-leche: ConLeche/Kernel/CoreDefs.lean:753-766 andRescueSlotsOf
/// The `(List.range 2).all` of `and_rescue_slots`, as an index recursion.
pub fn and_rescue_slots_from(
    fe: &FEnv,
    ctor: &Name,
    n_p: u64,
    ust: &Vec<Level>,
    j: u64,
) -> bool {
    if j >= 2 {
        true
    } else if and_rescue_slot_ok(fe, ctor, n_p, ust, j) {
        and_rescue_slots_from(fe, ctor, n_p, ust, j + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:753-766 andRescueSlotsOf
/// The per-slot test (task #14's per-element rule), so the entry's borrow
/// dies inside the callee.
pub fn and_rescue_slot_ok(
    fe: &FEnv,
    ctor: &Name,
    n_p: u64,
    ust: &Vec<Level>,
    j: u64,
) -> bool {
    match fenv::find_proj(fe, &basis_names::and_name(), j) {
        Some(e) => {
            if !name::beq(&e.ctor, ctor) {
                false
            } else if e.num_params != n_p {
                false
            } else if e.num_fields != 2 {
                false
            } else {
                proj_entry_fire_ok(&e, ust)
            }
        }
        None => false,
    }
}

// ---------------------------------------------------------------------------
// The stuck-major rescue (`Core.lean:1287-1487`)
// ---------------------------------------------------------------------------


// ---------------------------------------------------------------------------
// The install-time rule bits (`Core.lean:1494-1621`)
// ---------------------------------------------------------------------------





// ---------------------------------------------------------------------------
// Iota (`Core.lean:1695-1800`)
// ---------------------------------------------------------------------------


/// con-leche: ConLeche/Kernel/Core.lean:820-932 iotaRec
/// `rules.find? (fun r' => r'.ctor == cj)`, as an index recursion returning
/// the position (§3.4 forbids closures; an index keeps the rule list's borrow
/// out of the state-touching cascade below).
pub fn rules_find(rules: &Vec<RecRule>, cj: &Name, i: usize) -> Option<usize> {
    if i >= rules.len() {
        None
    } else if name::beq(&rules[i].ctor, cj) {
        Some(i)
    } else {
        rules_find(rules, cj, i + 1)
    }
}


// ---------------------------------------------------------------------------
// Projections (`Core.lean:1803-1888`)
// ---------------------------------------------------------------------------


/// con-leche: ConLeche/Kernel/CoreDefs.lean:896-905 ProjEntry.typeAt
/// `out ++ targs.reverse`, as the downward index recursion `targs[k - 1]`,
/// `targs[k - 2]`, ….
pub fn rev_append_exprs(out: Vec<Expr>, targs: &Vec<Expr>, k: usize) -> Vec<Expr> {
    if k == 0 || k > targs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&targs[k - 1]));
        rev_append_exprs(out, targs, k - 1)
    }
}


// ---------------------------------------------------------------------------
// `whnfCore` (`Core.lean:1898-1990`)
// ---------------------------------------------------------------------------




// ---------------------------------------------------------------------------
// Inference (`Core.lean:2042-2337`)
// ---------------------------------------------------------------------------






// ---------------------------------------------------------------------------
// Definitional equality (`Core.lean:2346-2660`)
// ---------------------------------------------------------------------------




// ---------------------------------------------------------------------------
// The annotation pass (`Core.lean:2677-2858`)
// ---------------------------------------------------------------------------




/* Not ported from `Kernel/Core.lean` (DESIGN.md §3.1), and why:

   * `instance : ToString CheckError` (`:53-57`) — rendering only; §3.1 says
     message strings need not match, and the CLI (outside the verified core)
     renders errors.  Already recorded by task #14, which ported the
     `CheckError` half of the file.
   * the eight `@[simp] theorem`s about `recRuleBits` (`:1545-1586`) and the
     four about `projFnRule` (`:1596-1613`) — field-projection equations,
     i.e. the *spec* this port will be proved against, not part of it.

   Everything else in the file is either here or in `crate::cached::core_c`,
   whose twin of it is what the knot executes (the module note's "What is
   here and what moved").  `structure CoreFns` (`:66-92`) and
   `CoreFns.ioView` (`:89-95`) are cited on `core_c::infer_at_i`, the `io`
   flag that *is* the record's slot dispatch; `coreKnot` (`:2866-2900`) is
   cited on `core_c`'s six wrappers, which are `coreKnotI`'s.

   The `FEnv.lean` guards that read the same bodies through the index
   (`natLitSupportedF`, `strLitSupportedF`, `natOpGuardF`, `natOpStoredF`,
   `andRescueSlotsF`, `towerSlotsAllF`, `recSlotsAllF`) and the seven
   `StateC.lean` `*C` index guards are covered by the corresponding function
   here, with a second citation, per the module note's deviation 3. */
#[cfg(test)]
mod tests {
    // Task #97-SWAP: this module's tests ran the `Expr`-tree checker
    // (`cached::core_c`, `cached::state_c`) over the items above, and that
    // checker is gone — the arena's is the checker now.  What the items are
    // still FOR is the pinned DATA (`lib.rs`'s "Why `Expr` survives"), which
    // `arena::intern` reads and `crates/con-ron-core/src/arena/*`'s own tests
    // and `scripts/diff-e2e.sh` exercise end to end.
}
