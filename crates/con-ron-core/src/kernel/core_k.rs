//! The checker core's **bodies** — `ConLeche/Kernel/Core.lean` from the
//! `Bodies` section on (`:97-2858`), plus the knot's fuel constant
//! (`:2903`).  The head of the file (`CheckError`, `CheckM`) is
//! `core_types.rs` (task #14); the six memoizing wrappers that *tie* these
//! bodies are `crate::cached::core_c` (`Cached/CoreC.lean`).
//!
//! The module is `core_k`, not `core`: `core` is a Rust prelude crate name,
//! and `crate::kernel::core` would shadow it for every `use` inside this
//! crate.  The `k` is for *kernel* — the pure checker core, con-leche's
//! `ConLeche.Kernel.Core`.
//!
//! ## The knot is closed by name, not by a record (DESIGN.md §3.1)
//!
//! Every function here is a Lean *body*: non-recursive, written against the
//! record `r : CoreFns m` of the six mutually recursive entry points.  The
//! port drops the record: where the Lean body writes `r.whnf d x` the Rust
//! writes `core_c::whnf(mode, fuel, st, fe, d, &x)` — the *wrapper*, by name
//! — and the record's parameter is replaced by the `fuel: u64` the wrapper
//! decrements.  So a body at `fuel` is the Lean body applied to `coreKnot …
//! fuel`, and `core_c`'s wrapper at `fuel + 1` calls the body at `fuel`,
//! exactly as `coreKnot`'s `fuel + 1` arm does.  The whole set — these
//! bodies and those six wrappers — is one block of plain mutually recursive
//! functions; no trait is in the recursion and there are no closures
//! (DESIGN.md §3.1: Aeneas rejects a function mutually recursive with a
//! trait implementation, and §3.4 forbids closures).
//!
//! Four consequences, each a deviation from the cited text that applies
//! *everywhere* and is therefore recorded once, here, rather than on every
//! item:
//!
//! 1. **`mode` is threaded explicitly.**  In the Lean the knot closes over
//!    the mode, so a body that reads no mode itself takes none.  The Rust
//!    wrappers are plain functions, so `mode: &CheckMode` is a parameter of
//!    every function that (transitively) calls one — `reduce_nat`,
//!    `iota_certs`, `def_eq_list` and the rest included.
//! 2. **The state is `&mut CState`.**  The bodies themselves touch no memo
//!    — the maps are the wrappers' business (`memoEI`/`memoBI`) — but each
//!    must thread `st` to the wrappers it calls.  Aeneas turns a `&mut`
//!    parameter into a threaded return, so the generated Lean carries
//!    con-leche's own `StateT CState` shape.
//! 3. **The environment is the index `FEnv`.**  `Kernel/Core.lean`'s bodies
//!    take `env : Env` and call `env.find?`/`env.findProj?`; the executed
//!    checker reads the environment through the index (`FEnv`, task #14) and
//!    con-leche writes the `F`-mirror twins for exactly that
//!    (`FEnv.lean:98-153`).  The port has one spelling: `fe: &FEnv` with
//!    `fenv::find`/`fenv::find_proj`, whose agreement with `Env.find?` is
//!    con-leche's own `ConLeche/Verify/EnvBound.lean`.  The five guards the
//!    Lean writes twice (`natLitSupported`/`natLitSupportedF`, …) are
//!    therefore *one* Rust function with two citations.
//! 4. **Depths, indices and arities are `u64`** (DESIGN.md §3.3); only
//!    `Literal.natVal` and the `Nat`-operation fast path use `ron::Nat`.
//!
//! ## The other standing deviations
//!
//! * **`List` becomes `Vec` with `*_from` index helpers** (task #3's
//!   pattern): `iota_certs`, `def_eq_list`, `pi_residual`,
//!   `struct_eta_proj_certs`, `eta_projs`, `nat_op_deps` and friends.
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
//!   `Rc` bump) wherever they outlive the `match` or cross a wrapper call;
//!   this is what Lean's value semantics gives for free, and it is task
//!   #14's rule against holding a borrow across a state-touching branch.

use crate::cached::core_c;
use crate::cached::state_c;
use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{
    CheckMode, ConstantInfo, ConstantVal, IndCaps, ProjEntry, RecRule, RecRuleFire,
    ReducibilityHint,
};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprKind, Literal};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_read;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::nat;
use crate::ron::nat::Nat;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `Vec` helpers for the `List` operations the Lean uses for free
// ---------------------------------------------------------------------------

/// con-leche: none — `List.drop` on a `Vec`; Lean's list tail is shared
/// `xs.drop k`, as a fresh `Vec` of `Rc` bumps.
pub fn drop_exprs(xs: &Vec<Expr>, k: usize) -> Vec<Expr> {
    drop_exprs_from(xs, k, Vec::new())
}

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

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The scope guard's third conjunct,
/// `fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)` — a closure
/// over a `List.all`, so it becomes the index recursion below.  All three of
/// `majorToCtor`'s branches run it.
pub fn fvar_leaves_subset(xs: &Vec<(u64, Expr)>, ys: &Vec<(u64, Expr)>) -> bool {
    fvar_leaves_subset_from(xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
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

/// con-leche: ConLeche/Kernel/Core.lean:113-116 projModelName
/// `toString i` for a `Nat` index: the decimal code points, most significant
/// digit first, `0` for zero.  Lean's `Nat.toString` is the runtime's; on the
/// `u64` of DESIGN.md §3.3 this is the recursion that produces it.
pub fn nat_to_dec(i: u64) -> Vec<u32> {
    nat_to_dec_go(i, Vec::new())
}

/// con-leche: ConLeche/Kernel/Core.lean:113-116 projModelName
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

/// con-leche: ConLeche/Kernel/Core.lean:208-227 unfoldDefinition
/// con-leche: ConLeche/Kernel/Core.lean:244-253 headHint
/// The `some (.defnInfo cv value hint)` destructuring, as an owning probe:
/// the borrow of the index dies at the call boundary and the caller works on
/// copies, which is what Lean's value semantics hands its pattern variables.
pub fn defn_probe(fe: &FEnv, n: &Name) -> Option<(ConstantVal, Expr, ReducibilityHint)> {
    match fenv::find(fe, n) {
        Some(ConstantInfo::DefnInfo(cv, v, h)) => Some((
            env::constant_val_dup(cv),
            expr::dup(v),
            env::reducibility_hint_dup(h),
        )),
        Some(_) => None,
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The `some (.ctorInfo cv cnP cnF)` destructuring, as an owning probe (see
/// `defn_probe`).
pub fn ctor_probe(fe: &FEnv, n: &Name) -> Option<(ConstantVal, u64, u64)> {
    match fenv::find(fe, n) {
        Some(ConstantInfo::CtorInfo(cv, n_p, n_f)) => {
            Some((env::constant_val_dup(cv), *n_p, *n_f))
        }
        Some(_) => None,
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The `some (.indInfo cvT caps)` destructuring, as an owning probe (see
/// `defn_probe`).
pub fn ind_probe(fe: &FEnv, n: &Name) -> Option<(ConstantVal, IndCaps)> {
    match fenv::find(fe, n) {
        Some(ConstantInfo::IndInfo(cv, caps)) => {
            Some((env::constant_val_dup(cv), env::ind_caps_dup(caps)))
        }
        Some(_) => None,
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// con-leche: ConLeche/Kernel/Core.lean:975-998 structEtaProjCerts
/// The `some (.recInfo cv mI rP rules)` destructuring, as an owning probe
/// (see `defn_probe`).  The rule list is copied spine-wise —
/// `iotaRec` reads it after several state-touching calls.
pub fn rec_probe(fe: &FEnv, n: &Name) -> Option<(ConstantVal, u64, u64, Vec<RecRule>)> {
    match fenv::find(fe, n) {
        Some(ConstantInfo::RecInfo(cv, m_i, r_p, rules)) => Some((
            env::constant_val_dup(cv),
            *m_i,
            *r_p,
            env::rec_rules_copy(rules),
        )),
        Some(_) => None,
        None => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:656-672 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
/// `match env.find? n with | some ci => ci.toConstantVal.levelParams.isEmpty
/// | none => false` — the level-monomorphism test `natOpGuard` runs on the
/// `Bool` constructors, as its own function so the index's borrow ends here.
pub fn lp_empty(fe: &FEnv, n: &Name) -> bool {
    match fenv::find(fe, n) {
        Some(ci) => env::to_constant_val(ci).level_params.len() == 0,
        None => false,
    }
}

// ---------------------------------------------------------------------------
// `liftFueled` and the small readers (`Core.lean:109-206`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:108-111 liftFueled
/// Lift a fuel-style partial result; `none` is an internal error.
///
/// Deviations: monomorphic at `Option Bool`, because every call site in
/// `Core.lean` lifts a `Level.isEquiv`/`Level.isEquivList` (§3.4 keeps
/// generics out where one instance is all there is), and the `what`
/// parameter is baked in for the same reason — every site passes
/// `"level comparison"`.
pub fn lift_fueled(o: Option<bool>) -> CheckM<bool> {
    const M: [u32; 32] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 108, 101,
        118, 101, 108, 32, 99, 111, 109, 112, 97, 114, 105, 115, 111, 110,
    ];
    match o {
        Some(a) => Ok(a),
        None => Err(core_types::internal(core_types::code_points(&M))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:113-116 projModelName
/// The model-side name of field `i`'s projection for `T`:
/// `(T.str "_model").str ("proj_" ++ toString i)`.
pub fn proj_model_name(t: &Name, i: u64) -> Name {
    const MODEL: [u32; 6] = [95, 109, 111, 100, 101, 108];
    const PROJ_: [u32; 5] = [112, 114, 111, 106, 95];
    let head = name::mk_str(name::dup(t), core_types::code_points(&MODEL));
    let mut s: Vec<u32> = core_types::code_points(&PROJ_);
    let digits: Vec<u32> = nat_to_dec(i);
    s = core_types::code_points_from(&digits, 0, s);
    name::mk_str(head, s)
}

/// con-leche: ConLeche/Kernel/Core.lean:118-125 isCtorApp
/// Is the expression headed by a stored constructor?
pub fn is_ctor_app(fe: &FEnv, e: &Expr) -> bool {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(c, _) => match fenv::find(fe, c) {
            Some(ci) => is_ctor_info(ci),
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:127-134 piResultIsProp
/// Does the syntactic pi telescope end in a (normalized) `Prop`?
pub fn pi_result_is_prop(e: &Expr) -> bool {
    let r = expr_ops::pi_result(e);
    match &r.0.kind {
        ExprKind::Sort(u) => match level::is_equiv(u, &level::zero()) {
            Some(true) => true,
            Some(false) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:136-144 piResultZ
/// The result-sort zero-ness datum of an inductive's type (`IndCaps.sortZ`,
/// computed at the block's install).  A telescope that does not end in a
/// sort gets `ifAllZero []` — "zero at every valuation".
pub fn pi_result_z(e: &Expr) -> PropWhen {
    let r = expr_ops::pi_result(e);
    match &r.0.kind {
        ExprKind::Sort(u) => level::zeroness_of(u),
        _ => prop_when::if_all_zero(Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:146-154 piResultNeverZero
/// The *specification* of `caps_never_zero`: the walk down the family's type
/// that the stored datum replaces.  Nothing executable calls it; ported so
/// the provenance gate stays in step with its source (task #11's
/// `beqRecursive` rule).
pub fn pi_result_never_zero(lps: &Vec<Name>, us: &Vec<Level>, e: &Expr) -> bool {
    let r = expr_ops::pi_result(e);
    match &r.0.kind {
        ExprKind::Sort(u) => level::is_never_zero(&level::subst(lps, us, u)),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:156-167 capsNeverZero
/// Is a stored inductive's result sort, at the given level instantiation,
/// provably nonzero?  Read off the stored datum.
pub fn caps_never_zero(lps: &Vec<Name>, us: &Vec<Level>, caps: &IndCaps) -> bool {
    prop_when::is_never(&level::subst_pw(lps, us, &caps.sort_z))
}

/// con-leche: ConLeche/Kernel/Core.lean:169-206 isUnitLikeTy
/// Is this (whnf'd) type expression a unit-like inductive type?  The
/// head-name comparison against the single pin that can pass (`PUnit`) comes
/// first, then the two stored-shape checks specialised to it — con-leche's
/// task #161 item C1 computation downgrade, licensed by `unitLike_eq_punit`.
/// The `&&` cascade is an `if` nest, and `[r]` is `rules.len() == 1`.
pub fn is_unit_like_ty(fe: &FEnv, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Const(c, _) => {
            if name::beq(c, &basis_names::punit_name()) {
                if is_punit_ind(fe) {
                    is_punit_rec_shape(fe)
                } else {
                    false
                }
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:169-206 isUnitLikeTy
/// The cited `match env.find? punitName with | some (.indInfo _ _) => true |
/// _ => false`, factored out (task #14's probe rule).
pub fn is_punit_ind(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::punit_name()) {
        Some(ConstantInfo::IndInfo(_, _)) => true,
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:169-206 isUnitLikeTy
/// The cited `match env.find? punitRecName with | some (.recInfo _ mI rP [r])
/// => mI == rP && r.nfields == 0 | _ => false`, factored out.
pub fn is_punit_rec_shape(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::punit_rec_name()) {
        Some(ConstantInfo::RecInfo(_, m_i, r_p, rules)) => {
            if rules.len() == 1 {
                *m_i == *r_p && rules[0].nfields == 0
            } else {
                false
            }
        }
        Some(_) => false,
        None => false,
    }
}

// ---------------------------------------------------------------------------
// Delta (`Core.lean:217-266`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:208-227 unfoldDefinition
/// Unfold the (application of a) definition at the head, one step; `None`
/// when the head is not an unfoldable constant.  **Theorems are opaque to
/// reduction** — a stored `thmInfo` never unfolds.
pub fn unfold_definition(fe: &FEnv, e: &Expr) -> Option<Expr> {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(n, us) => match defn_probe(fe, n) {
            Some((cv, value, _)) => {
                if us.len() == cv.level_params.len() {
                    let v = expr_ops::instantiate_level_params(&cv.level_params, us, &value);
                    Some(expr_ops::mk_app_n(v, &expr_ops::get_app_args(e)))
                } else {
                    None
                }
            }
            None => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:229-242 unfoldableHead
/// May the delta step unfold `e`'s head?  The *decision* the lazy delta step
/// takes; the unfolding itself is materialized only inside the branch that
/// consumes it.  By construction
/// `unfoldable_head(fe, e) = unfold_definition(fe, e).is_some()`.
pub fn unfoldable_head(fe: &FEnv, e: &Expr) -> bool {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(n, us) => match fenv::find(fe, n) {
            Some(ConstantInfo::DefnInfo(cv, _, _)) => us.len() == cv.level_params.len(),
            Some(_) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:244-253 headHint
/// The reducibility hint of the constant at the head of `e` (`opaque` when
/// the head is not a stored definition — a theorem included).
pub fn head_hint(fe: &FEnv, e: &Expr) -> ReducibilityHint {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(n, _) => match defn_probe(fe, n) {
            Some((_, _, hint)) => hint,
            None => ReducibilityHint::Opaque,
        },
        _ => ReducibilityHint::Opaque,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:255-264 sameConstHeads
/// Are `a` and `b` applications of the *same* constant (the lazy delta
/// same-head short-circuit)?  Both sides must actually be applications.
pub fn same_const_heads(a: &Expr, b: &Expr) -> bool {
    match &a.0.kind {
        ExprKind::App(f1, _) => match &b.0.kind {
            ExprKind::App(f2, _) => {
                let g1 = expr_ops::get_app_fn(f1);
                let g2 = expr_ops::get_app_fn(f2);
                match &g1.0.kind {
                    ExprKind::Const(n1, _) => match &g2.0.kind {
                        ExprKind::Const(n2, _) => name::beq(n1, n2),
                        _ => false,
                    },
                    _ => false,
                }
            }
            _ => false,
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// `Nat` literals (`Core.lean:269-346`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:266-272 natLitToConstructor
/// The constructor form of a `Nat` literal, one layer: `n + 1` becomes
/// `Nat.succ (lit n)`, `0` becomes `Nat.zero`.  The cited `match n with | 0 |
/// k + 1` is `nat::is_zero` plus `nat::pred` on the bignum (§3.3).
pub fn nat_lit_to_constructor(n: &Nat) -> Expr {
    if nat::is_zero(n) {
        expr::mk_const(basis_names::nat_zero_name(), Vec::new())
    } else {
        expr::app(
            expr::mk_const(basis_names::nat_succ_name(), Vec::new()),
            expr::lit(Literal::NatVal(nat::pred(n))),
        )
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:274-278 natIndOk
/// The stored `Nat` declaration has the expected shape.
pub fn nat_ind_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(ConstantInfo::IndInfo(cv, _)) => {
            if cv.level_params.len() == 0 {
                expr::beq(&cv.ty, &expr::sort(level::succ(level::zero())))
            } else {
                false
            }
        }
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:280-284 natZeroOk
/// The stored `Nat.zero` declaration has the expected shape.
pub fn nat_zero_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(ConstantInfo::CtorInfo(cv, _, _)) => {
            if cv.level_params.len() == 0 {
                expr::beq(
                    &cv.ty,
                    &expr::mk_const(basis_names::nat_name(), Vec::new()),
                )
            } else {
                false
            }
        }
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:286-295 natSuccOk
/// The stored `Nat.succ` declaration has the expected (annotated) shape.
pub fn nat_succ_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(ConstantInfo::CtorInfo(cv, _, _)) => {
            if cv.level_params.len() == 0 {
                match &cv.ty.0.kind {
                    ExprKind::ForallE(dom, body, _) => match &dom.0.kind {
                        ExprKind::Const(c1, us1) => match &body.0.kind {
                            ExprKind::Const(c2, us2) => {
                                if us1.len() == 0 && us2.len() == 0 {
                                    name::beq(c1, &basis_names::nat_name())
                                        && name::beq(c2, &basis_names::nat_name())
                                } else {
                                    false
                                }
                            }
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:297-305 natLitSupported
/// con-leche: ConLeche/Kernel/FEnv.lean:116-119 natLitSupportedF
/// Whether the environment supports `Nat` literals: `Nat`, `Nat.zero` and
/// `Nat.succ` are stored with exactly the expected kinds, level parameters
/// and (annotated) types.  Every literal code path is guarded on this.
pub fn nat_lit_supported(fe: &FEnv) -> bool {
    if nat_ind_ok(fenv::find(fe, &basis_names::nat_name())) {
        if nat_zero_ok(fenv::find(fe, &basis_names::nat_zero_name())) {
            nat_succ_ok(fenv::find(fe, &basis_names::nat_succ_name()))
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:307-332 Expr.constsResolve
/// Do all constants referenced in `e` (including inside `fvar` type
/// annotations) resolve in the environment?  A `Nat` literal implicitly
/// references the `Nat` basis constants, a `String` literal additionally the
/// string-support ones.  Checked once per declaration by the install; the
/// core never calls it.
pub fn consts_resolve(fe: &FEnv, e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Bvar(_) => true,
        ExprKind::Sort(_) => true,
        ExprKind::Lit(Literal::NatVal(_)) => nat_trio_stored(fe),
        ExprKind::Lit(Literal::StrVal(_)) => {
            if nat_trio_stored(fe) {
                str_support_stored(fe)
            } else {
                false
            }
        }
        ExprKind::Const(n, _) => fenv::find(fe, n).is_some(),
        ExprKind::Fvar(_, ty) => consts_resolve(fe, ty),
        ExprKind::App(f, a) => {
            if consts_resolve(fe, f) {
                consts_resolve(fe, a)
            } else {
                false
            }
        }
        ExprKind::Lam(ty, body, _) => {
            if consts_resolve(fe, ty) {
                consts_resolve(fe, body)
            } else {
                false
            }
        }
        ExprKind::ForallE(ty, body, _) => {
            if consts_resolve(fe, ty) {
                consts_resolve(fe, body)
            } else {
                false
            }
        }
        ExprKind::LetE(ty, val, body) => {
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
        ExprKind::Proj(s, _, pe) => {
            if fenv::find(fe, s).is_some() {
                consts_resolve(fe, pe)
            } else {
                false
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:307-332 Expr.constsResolve
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

/// con-leche: ConLeche/Kernel/Core.lean:307-332 Expr.constsResolve
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

/// con-leche: ConLeche/Kernel/Core.lean:334-339 litToCtorIfNat
/// Convert a `Nat`-literal major premise to constructor form, one layer;
/// anything else passes through.
pub fn lit_to_ctor_if_nat(fe: &FEnv, e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Lit(Literal::NatVal(n)) => {
            if nat_lit_supported(fe) {
                nat_lit_to_constructor(n)
            } else {
                expr::dup(e)
            }
        }
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:341-346 rawNatLit?
/// A `Nat` literal reading of a whnf'd expression: literals and the
/// `Nat.zero` constant (the official kernel's `rawNatLitExt?`).
pub fn raw_nat_lit(e: &Expr) -> Option<Nat> {
    match &e.0.kind {
        ExprKind::Lit(Literal::NatVal(n)) => Some(nat::clone(n)),
        ExprKind::Const(c, us) => {
            if us.len() == 0 && name::beq(c, &basis_names::nat_zero_name()) {
                Some(nat::zero())
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// String literals (`Core.lean:365-475`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:360-371 strLitToConstructor
/// The constructor form of a `String` literal:
/// `String.ofList (List.cons.{0} Char (Char.ofNat (lit c₁)) (… (List.nil.{0}
/// Char)))`.  The cited `s.toList.foldr` becomes the downward index
/// recursion below; a code point *is* `c.toNat` (DESIGN.md §3.3).
pub fn str_lit_to_constructor(s: &Vec<u32>) -> Expr {
    let init = expr::app(
        expr::mk_const(basis_names::list_nil_name(), level::singleton(level::zero())),
        expr::mk_const(basis_names::char_name(), Vec::new()),
    );
    expr::app(
        expr::mk_const(basis_names::string_of_list_name(), Vec::new()),
        str_lit_cons_from(s, s.len(), init),
    )
}

/// con-leche: ConLeche/Kernel/Core.lean:360-371 strLitToConstructor
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
            expr::lit(Literal::NatVal(nat::from_u64(c as u64))),
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

/// con-leche: ConLeche/Kernel/Core.lean:373-379 stringTyOk
/// The stored `String` declaration has the expected shape (`String : Type`,
/// no level parameters; any constant kind).
pub fn string_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                expr::beq(&cv.ty, &expr::sort(level::succ(level::zero())))
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:381-387 charTyOk
/// The stored `Char` declaration has the expected shape (`Char : Type`).
pub fn char_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                expr::beq(&cv.ty, &expr::sort(level::succ(level::zero())))
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:389-400 listTyOk
/// The stored `List` declaration has the expected (annotated) shape
/// `List.{p} : Type p → Type p`.
pub fn list_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 1 {
                let p: &Name = &cv.level_params[0];
                match &cv.ty.0.kind {
                    ExprKind::ForallE(dom, body, _) => match &dom.0.kind {
                        ExprKind::Sort(u1) => match &body.0.kind {
                            ExprKind::Sort(u2) => {
                                let want = level::succ(level::param(name::dup(p)));
                                level::beq(u1, &want) && level::beq(u2, &want)
                            }
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:402-413 listNilTyOk
/// The stored `List.nil` declaration has the expected (annotated) shape
/// `List.nil.{p} : ∀ (α : Type p), List.{p} α`.
pub fn list_nil_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 1 {
                let p: &Name = &cv.level_params[0];
                match &cv.ty.0.kind {
                    ExprKind::ForallE(dom, body, _) => match &dom.0.kind {
                        ExprKind::Sort(u1) => match &body.0.kind {
                            ExprKind::App(hd, arg) => match &arg.0.kind {
                                ExprKind::Bvar(0) => match &hd.0.kind {
                                    ExprKind::Const(l1, us1) => {
                                        if level::beq(
                                            u1,
                                            &level::succ(level::param(name::dup(p))),
                                        ) {
                                            if name::beq(l1, &basis_names::list_name()) {
                                                expr::levels_beq(
                                                    us1,
                                                    &level::singleton(level::param(
                                                        name::dup(p),
                                                    )),
                                                )
                                            } else {
                                                false
                                            }
                                        } else {
                                            false
                                        }
                                    }
                                    _ => false,
                                },
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:415-432 listConsTyOk
/// The stored `List.cons` declaration has the expected (annotated) shape
/// `List.cons.{p} : ∀ (α : Type p) (head : α) (tail : List.{p} α), List.{p} α`.
/// The cited four-deep binder pattern is spelled as a nested `match`; the
/// `.bvar` indices are the cited `0`, `1`, `2`.
pub fn list_cons_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 1 {
                let p: &Name = &cv.level_params[0];
                match &cv.ty.0.kind {
                    ExprKind::ForallE(d1, b1, _) => match &d1.0.kind {
                        ExprKind::Sort(u1) => match &b1.0.kind {
                            ExprKind::ForallE(d2, b2, _) => match &d2.0.kind {
                                ExprKind::Bvar(0) => match &b2.0.kind {
                                    ExprKind::ForallE(d3, b3, _) => {
                                        list_cons_tail_ok(u1, d3, b3, p)
                                    }
                                    _ => false,
                                },
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:415-432 listConsTyOk
/// The innermost two slots of `list_cons_ty_ok`'s pattern —
/// `.forallE (.app (.const l1 us1) (.bvar 1)) (.app (.const l2 us2) (.bvar 2))`
/// and the four comparisons — as their own function, so the nesting stays
/// readable.
pub fn list_cons_tail_ok(u1: &Level, d3: &Expr, b3: &Expr, p: &Name) -> bool {
    match &d3.0.kind {
        ExprKind::App(h1, a1) => match &b3.0.kind {
            ExprKind::App(h2, a2) => match &a1.0.kind {
                ExprKind::Bvar(1) => match &a2.0.kind {
                    ExprKind::Bvar(2) => match &h1.0.kind {
                        ExprKind::Const(l1, us1) => match &h2.0.kind {
                            ExprKind::Const(l2, us2) => {
                                let want = level::singleton(level::param(name::dup(p)));
                                if level::beq(u1, &level::succ(level::param(name::dup(p)))) {
                                    if name::beq(l1, &basis_names::list_name())
                                        && name::beq(l2, &basis_names::list_name())
                                    {
                                        expr::levels_beq(us1, &want)
                                            && expr::levels_beq(us2, &want)
                                    } else {
                                        false
                                    }
                                } else {
                                    false
                                }
                            }
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                },
                _ => false,
            },
            _ => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:434-443 charOfNatTyOk
/// The stored `Char.ofNat` declaration has the expected (annotated) shape
/// `Char.ofNat : Nat → Char`.
pub fn char_of_nat_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                match &cv.ty.0.kind {
                    ExprKind::ForallE(dom, body, _) => match &dom.0.kind {
                        ExprKind::Const(c1, us1) => match &body.0.kind {
                            ExprKind::Const(c2, us2) => {
                                if us1.len() == 0 && us2.len() == 0 {
                                    name::beq(c1, &basis_names::nat_name())
                                        && name::beq(c2, &basis_names::char_name())
                                } else {
                                    false
                                }
                            }
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:445-455 stringOfListTyOk
/// The stored `String.ofList` declaration has the expected (annotated) shape
/// `String.ofList : List.{0} Char → String`.
pub fn string_of_list_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                match &cv.ty.0.kind {
                    ExprKind::ForallE(dom, body, _) => match &dom.0.kind {
                        ExprKind::App(hd, arg) => match &body.0.kind {
                            ExprKind::Const(c2, us2) => match &hd.0.kind {
                                ExprKind::Const(l1, us1) => match &arg.0.kind {
                                    ExprKind::Const(c1, us_c) => {
                                        if us2.len() == 0 && us_c.len() == 0 {
                                            if name::beq(l1, &basis_names::list_name()) {
                                                if expr::levels_beq(
                                                    us1,
                                                    &level::singleton(level::zero()),
                                                ) {
                                                    name::beq(c1, &basis_names::char_name())
                                                        && name::beq(
                                                            c2,
                                                            &basis_names::string_name(),
                                                        )
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
                                    _ => false,
                                },
                                _ => false,
                            },
                            _ => false,
                        },
                        _ => false,
                    },
                    _ => false,
                }
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:457-475 strLitSupported
/// con-leche: ConLeche/Kernel/FEnv.lean:121-130 strLitSupportedF
/// Whether the environment supports `String` literals: the `Nat` literal
/// guard plus the seven string-support declarations at exactly the expected
/// level parameters and (annotated) types.
pub fn str_lit_supported(fe: &FEnv) -> bool {
    if nat_lit_supported(fe) {
        if string_ty_ok(fenv::find(fe, &basis_names::string_name())) {
            if string_of_list_ty_ok(fenv::find(fe, &basis_names::string_of_list_name())) {
                if list_ty_ok(fenv::find(fe, &basis_names::list_name())) {
                    if list_nil_ty_ok(fenv::find(fe, &basis_names::list_nil_name())) {
                        if list_cons_ty_ok(fenv::find(fe, &basis_names::list_cons_name())) {
                            if char_ty_ok(fenv::find(fe, &basis_names::char_name())) {
                                char_of_nat_ty_ok(fenv::find(
                                    fe,
                                    &basis_names::char_of_nat_name(),
                                ))
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
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The certified structural-`Nat` operations (`Core.lean:505-775`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:118-125 isCtorApp
/// The cited `match env.find? c with | some (.ctorInfo _ _ _) => true | _ =>
/// false`.  `env::is_rec_info` is `env.rs`'s twin of this (task #14); the
/// constructor test has no other consumer, so it lives here.
pub fn is_ctor_info(ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::CtorInfo(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:505-505 natPredName
/// `Nat.pred`.
pub fn nat_pred_name() -> Name {
    const S: [u32; 4] = [112, 114, 101, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:506-506 natAddName
/// `Nat.add`.
pub fn nat_add_name() -> Name {
    const S: [u32; 3] = [97, 100, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:507-507 natSubName
/// `Nat.sub`.
pub fn nat_sub_name() -> Name {
    const S: [u32; 3] = [115, 117, 98];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:508-508 natMulName
/// `Nat.mul`.
pub fn nat_mul_name() -> Name {
    const S: [u32; 3] = [109, 117, 108];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:509-509 natPowName
/// `Nat.pow`.
pub fn nat_pow_name() -> Name {
    const S: [u32; 3] = [112, 111, 119];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:510-510 natBeqName
/// `Nat.beq`.
pub fn nat_beq_name() -> Name {
    const S: [u32; 3] = [98, 101, 113];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:511-511 natBleName
/// `Nat.ble`.
pub fn nat_ble_name() -> Name {
    const S: [u32; 3] = [98, 108, 101];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:512-512 natDivName
/// `Nat.div`.
pub fn nat_div_name() -> Name {
    const S: [u32; 3] = [100, 105, 118];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:513-513 natModName
/// `Nat.mod`.
pub fn nat_mod_name() -> Name {
    const S: [u32; 3] = [109, 111, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:514-514 natGcdName
/// `Nat.gcd`.
pub fn nat_gcd_name() -> Name {
    const S: [u32; 3] = [103, 99, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:515-515 natLandName
/// `Nat.land`.
pub fn nat_land_name() -> Name {
    const S: [u32; 4] = [108, 97, 110, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:516-516 natLorName
/// `Nat.lor`.
pub fn nat_lor_name() -> Name {
    const S: [u32; 3] = [108, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:517-517 natXorName
/// `Nat.xor`.
pub fn nat_xor_name() -> Name {
    const S: [u32; 3] = [120, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:518-518 natShiftLeftName
/// `Nat.shiftLeft`.
pub fn nat_shift_left_name() -> Name {
    const S: [u32; 9] = [115, 104, 105, 102, 116, 76, 101, 102, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:519-519 natShiftRightName
/// `Nat.shiftRight`.
pub fn nat_shift_right_name() -> Name {
    const S: [u32; 10] = [115, 104, 105, 102, 116, 82, 105, 103, 104, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:520-520 boolName
/// `Bool`.
pub fn bool_name() -> Name {
    const S: [u32; 4] = [66, 111, 111, 108];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:521-521 boolTrueName
/// `Bool.true`.
pub fn bool_true_name() -> Name {
    const S: [u32; 4] = [116, 114, 117, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:522-522 boolFalseName
/// `Bool.false`.
pub fn bool_false_name() -> Name {
    const S: [u32; 5] = [102, 97, 108, 115, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/Core.lean:524-529 Expr.isBoolTrue
/// Is `e` the constant `Bool.true` — the name, no universe levels?
pub fn is_bool_true(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Const(c, us) => {
            if us.len() == 0 {
                name::beq(c, &bool_true_name())
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:531-543 Expr.quickPair
/// The pairs official's `quick_is_def_eq` decides by itself: two sorts, two
/// literals, two `∀`s, two `λ`s.  Charon expands the cited wildcard arm, as
/// in `expr::beq_go` (task #11's note).
pub fn quick_pair(a: &Expr, b: &Expr) -> bool {
    match &a.0.kind {
        ExprKind::Sort(_) => is_sort(b),
        ExprKind::Lit(_) => is_lit(b),
        ExprKind::ForallE(_, _, _) => is_forall(b),
        ExprKind::Lam(_, _, _) => is_lam_k(b),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:531-543 Expr.quickPair
/// The four one-constructor tests `quick_pair`'s second slot needs; Rust has
/// no `.sort _` pattern outside a `match`, so each is a named function
/// (`expr_ops::is_lam` is the `Expr.isLam` of `ExprOps.lean`, a different
/// declaration).
pub fn is_sort(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Sort(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:531-543 Expr.quickPair
/// See `is_sort`.
pub fn is_lit(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Lit(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:531-543 Expr.quickPair
/// See `is_sort`.
pub fn is_forall(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::ForallE(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:531-543 Expr.quickPair
/// See `is_sort`.
pub fn is_lam_k(e: &Expr) -> bool {
    match &e.0.kind {
        ExprKind::Lam(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:545-553 natOpNames
/// The certified structural-`Nat` operations.
pub fn nat_op_names() -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    ns.push(nat_pred_name());
    ns.push(nat_add_name());
    ns.push(nat_sub_name());
    ns.push(nat_mul_name());
    ns.push(nat_pow_name());
    ns.push(nat_beq_name());
    ns.push(nat_ble_name());
    ns
}

/// con-leche: ConLeche/Kernel/Core.lean:555-570 natDivModNames
/// The WF-recursive operations with a *pinned-declaration* certified fast
/// path.
pub fn nat_div_mod_names() -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    ns.push(nat_div_name());
    ns.push(nat_mod_name());
    ns.push(nat_gcd_name());
    ns.push(nat_land_name());
    ns.push(nat_lor_name());
    ns.push(nat_xor_name());
    ns.push(nat_shift_left_name());
    ns.push(nat_shift_right_name());
    ns
}

/// con-leche: ConLeche/Kernel/Core.lean:572-595 natOpDeps
/// The operations (transitively) involved in `c`'s recurrences.  The cited
/// `if … else if …` chain, arm for arm; the empty tail is `[]`.
pub fn nat_op_deps(c: &Name) -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    if name::beq(c, &nat_pred_name()) {
        ns.push(nat_pred_name());
    } else if name::beq(c, &nat_add_name()) {
        ns.push(nat_add_name());
    } else if name::beq(c, &nat_sub_name()) {
        ns.push(nat_pred_name());
        ns.push(nat_sub_name());
    } else if name::beq(c, &nat_mul_name()) {
        ns.push(nat_add_name());
        ns.push(nat_mul_name());
    } else if name::beq(c, &nat_pow_name()) {
        ns.push(nat_add_name());
        ns.push(nat_mul_name());
        ns.push(nat_pow_name());
    } else if name::beq(c, &nat_beq_name()) {
        ns.push(nat_beq_name());
    } else if name::beq(c, &nat_ble_name()) {
        ns.push(nat_ble_name());
    } else if name::beq(c, &nat_div_name()) {
        ns.push(nat_pred_name());
        ns.push(nat_sub_name());
        ns.push(nat_ble_name());
        ns.push(nat_div_name());
    } else if name::beq(c, &nat_mod_name()) {
        ns.push(nat_pred_name());
        ns.push(nat_sub_name());
        ns.push(nat_ble_name());
        ns.push(nat_mod_name());
    } else if name::beq(c, &nat_gcd_name()) {
        ns.push(nat_ble_name());
        ns.push(nat_mod_name());
        ns.push(nat_gcd_name());
    } else if name::beq(c, &nat_land_name()) {
        ns.push(nat_add_name());
        ns.push(nat_mul_name());
        ns.push(nat_ble_name());
        ns.push(nat_div_name());
        ns.push(nat_mod_name());
        ns.push(nat_land_name());
    } else if name::beq(c, &nat_lor_name()) {
        ns.push(nat_add_name());
        ns.push(nat_sub_name());
        ns.push(nat_mul_name());
        ns.push(nat_ble_name());
        ns.push(nat_div_name());
        ns.push(nat_mod_name());
        ns.push(nat_lor_name());
    } else if name::beq(c, &nat_xor_name()) {
        ns.push(nat_add_name());
        ns.push(nat_mul_name());
        ns.push(nat_ble_name());
        ns.push(nat_div_name());
        ns.push(nat_mod_name());
        ns.push(nat_xor_name());
    } else if name::beq(c, &nat_shift_left_name()) {
        ns.push(nat_sub_name());
        ns.push(nat_mul_name());
        ns.push(nat_ble_name());
        ns.push(nat_shift_left_name());
    } else if name::beq(c, &nat_shift_right_name()) {
        ns.push(nat_sub_name());
        ns.push(nat_ble_name());
        ns.push(nat_div_name());
        ns.push(nat_shift_right_name());
    }
    ns
}

/// con-leche: ConLeche/Kernel/Core.lean:597-626 natOpEquations
/// The `s : Expr → Expr` local of the cited `let`-block: `Nat.succ ·`.
/// §3.4 forbids closures, so the three spine builders are named functions.
pub fn nat_eq_s(a: Expr) -> Expr {
    expr::app(expr::mk_const(basis_names::nat_succ_name(), Vec::new()), a)
}

/// con-leche: ConLeche/Kernel/Core.lean:597-626 natOpEquations
/// The `ap1 : Name → Expr → Expr` local.
pub fn nat_eq_ap1(n: &Name, a: Expr) -> Expr {
    expr::app(expr::mk_const(name::dup(n), Vec::new()), a)
}

/// con-leche: ConLeche/Kernel/Core.lean:597-626 natOpEquations
/// The `ap2 : Name → Expr → Expr → Expr` local.
pub fn nat_eq_ap2(n: &Name, a: Expr, b: Expr) -> Expr {
    expr::app(expr::app(expr::mk_const(name::dup(n), Vec::new()), a), b)
}

/// con-leche: ConLeche/Kernel/Core.lean:597-626 natOpEquations
/// The defining recurrence equations of a structural-`Nat` operation, over
/// constructor forms with free variables `d`, `d + 1` (binder-free, so the
/// equation sides carry no annotations).  Run by the install
/// (`Kernel/Checker.lean`), never by reduction.
pub fn nat_op_equations(d: u64, c: &Name) -> Vec<(Expr, Expr)> {
    let nat_ty = expr::mk_const(basis_names::nat_name(), Vec::new());
    let x = expr::fvar(d, expr::dup(&nat_ty));
    let y = expr::fvar(d + 1, nat_ty);
    let z = expr::mk_const(basis_names::nat_zero_name(), Vec::new());
    let b_t = expr::mk_const(bool_true_name(), Vec::new());
    let b_f = expr::mk_const(bool_false_name(), Vec::new());
    let mut eqs: Vec<(Expr, Expr)> = Vec::new();
    if name::beq(c, &nat_pred_name()) {
        eqs.push((nat_eq_ap1(c, expr::dup(&z)), expr::dup(&z)));
        eqs.push((nat_eq_ap1(c, nat_eq_s(expr::dup(&x))), expr::dup(&x)));
    } else if name::beq(c, &nat_add_name()) {
        eqs.push((nat_eq_ap2(c, expr::dup(&x), expr::dup(&z)), expr::dup(&x)));
        eqs.push((
            nat_eq_ap2(c, expr::dup(&x), nat_eq_s(expr::dup(&y))),
            nat_eq_s(nat_eq_ap2(c, expr::dup(&x), expr::dup(&y))),
        ));
    } else if name::beq(c, &nat_sub_name()) {
        eqs.push((nat_eq_ap2(c, expr::dup(&x), expr::dup(&z)), expr::dup(&x)));
        eqs.push((
            nat_eq_ap2(c, expr::dup(&x), nat_eq_s(expr::dup(&y))),
            nat_eq_ap1(
                &nat_pred_name(),
                nat_eq_ap2(c, expr::dup(&x), expr::dup(&y)),
            ),
        ));
    } else if name::beq(c, &nat_mul_name()) {
        eqs.push((nat_eq_ap2(c, expr::dup(&x), expr::dup(&z)), expr::dup(&z)));
        eqs.push((
            nat_eq_ap2(c, expr::dup(&x), nat_eq_s(expr::dup(&y))),
            nat_eq_ap2(
                &nat_add_name(),
                nat_eq_ap2(c, expr::dup(&x), expr::dup(&y)),
                expr::dup(&x),
            ),
        ));
    } else if name::beq(c, &nat_pow_name()) {
        eqs.push((
            nat_eq_ap2(c, expr::dup(&x), expr::dup(&z)),
            nat_eq_s(expr::dup(&z)),
        ));
        eqs.push((
            nat_eq_ap2(c, expr::dup(&x), nat_eq_s(expr::dup(&y))),
            nat_eq_ap2(
                &nat_mul_name(),
                nat_eq_ap2(c, expr::dup(&x), expr::dup(&y)),
                expr::dup(&x),
            ),
        ));
    } else if name::beq(c, &nat_beq_name()) {
        eqs.push((
            nat_eq_ap2(c, expr::dup(&z), expr::dup(&z)),
            expr::dup(&b_t),
        ));
        eqs.push((
            nat_eq_ap2(c, expr::dup(&z), nat_eq_s(expr::dup(&y))),
            expr::dup(&b_f),
        ));
        eqs.push((
            nat_eq_ap2(c, nat_eq_s(expr::dup(&x)), expr::dup(&z)),
            expr::dup(&b_f),
        ));
        eqs.push((
            nat_eq_ap2(c, nat_eq_s(expr::dup(&x)), nat_eq_s(expr::dup(&y))),
            nat_eq_ap2(c, expr::dup(&x), expr::dup(&y)),
        ));
    } else if name::beq(c, &nat_ble_name()) {
        eqs.push((
            nat_eq_ap2(c, expr::dup(&z), expr::dup(&y)),
            expr::dup(&b_t),
        ));
        eqs.push((
            nat_eq_ap2(c, nat_eq_s(expr::dup(&x)), expr::dup(&z)),
            expr::dup(&b_f),
        ));
        eqs.push((
            nat_eq_ap2(c, nat_eq_s(expr::dup(&x)), nat_eq_s(expr::dup(&y))),
            nat_eq_ap2(c, expr::dup(&x), expr::dup(&y)),
        ));
    }
    eqs
}

/// con-leche: ConLeche/Kernel/Core.lean:628-654 natOpResult
/// The reduct of op `c` on literal arguments (`pred` ignores the second
/// slot).  The arithmetic is `ron::Nat`'s (DESIGN.md §3.3).
///
/// Two deviations, both in the direction of declining:
/// * the cited `b > 16777216` guard on `pow` is the audit's S2 bound; the
///   port compares bignums and then narrows the exponent to `u64` for
///   `nat::pow`, which takes a machine exponent (the bound makes that safe);
/// * `shiftLeft`/`shiftRight` take a `u64` shift amount, so an amount beyond
///   `u64` answers `None` — the fast path declines and the `whnf` loop
///   unfolds the definition instead.  Lean would compute (and exhaust
///   memory); answering `None` where Lean answers `some` can only make the
///   Rust *reject*, which is sound for the accept direction (DESIGN.md §1).
pub fn nat_op_result(c: &Name, a: &Nat, b: &Nat) -> Option<Expr> {
    if name::beq(c, &nat_pred_name()) {
        Some(expr::lit(Literal::NatVal(nat::pred(a))))
    } else if name::beq(c, &nat_add_name()) {
        Some(expr::lit(Literal::NatVal(nat::add(a, b))))
    } else if name::beq(c, &nat_sub_name()) {
        Some(expr::lit(Literal::NatVal(nat::sub(a, b))))
    } else if name::beq(c, &nat_mul_name()) {
        Some(expr::lit(Literal::NatVal(nat::mul(a, b))))
    } else if name::beq(c, &nat_pow_name()) {
        if nat::blt(&nat::from_u64(16777216), b) {
            None
        } else {
            match nat::to_u64(b) {
                Some(e) => Some(expr::lit(Literal::NatVal(nat::pow(a, e)))),
                None => None,
            }
        }
    } else if name::beq(c, &nat_div_name()) {
        Some(expr::lit(Literal::NatVal(nat::div(a, b))))
    } else if name::beq(c, &nat_mod_name()) {
        Some(expr::lit(Literal::NatVal(nat::modulo(a, b))))
    } else if name::beq(c, &nat_gcd_name()) {
        Some(expr::lit(Literal::NatVal(nat::gcd(a, b))))
    } else if name::beq(c, &nat_land_name()) {
        Some(expr::lit(Literal::NatVal(nat::land(a, b))))
    } else if name::beq(c, &nat_lor_name()) {
        Some(expr::lit(Literal::NatVal(nat::lor(a, b))))
    } else if name::beq(c, &nat_xor_name()) {
        Some(expr::lit(Literal::NatVal(nat::xor(a, b))))
    } else if name::beq(c, &nat_shift_left_name()) {
        match nat::to_u64(b) {
            Some(k) => Some(expr::lit(Literal::NatVal(nat::shift_left(a, k)))),
            None => None,
        }
    } else if name::beq(c, &nat_shift_right_name()) {
        match nat::to_u64(b) {
            Some(k) => Some(expr::lit(Literal::NatVal(nat::shift_right(a, k)))),
            None => None,
        }
    } else if name::beq(c, &nat_beq_name()) {
        let n = if nat::beq(a, b) {
            bool_true_name()
        } else {
            bool_false_name()
        };
        Some(expr::mk_const(n, Vec::new()))
    } else if name::beq(c, &nat_ble_name()) {
        let n = if nat::ble(a, b) {
            bool_true_name()
        } else {
            bool_false_name()
        };
        Some(expr::mk_const(n, Vec::new()))
    } else {
        None
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:656-672 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
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

/// con-leche: ConLeche/Kernel/Core.lean:656-672 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
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

/// con-leche: ConLeche/Kernel/Core.lean:656-672 natOpGuard
/// con-leche: ConLeche/Kernel/FEnv.lean:132-145 natOpGuardF
/// Stored-constant guards for op `c`: the `Nat` basis, every dependency
/// stored as a level-monomorphic definition, and (for the `Bool`-valued ops
/// and the `ble`-guarded `div`/`mod`) the `Bool` constructors stored.
/// Established once, at install; `nat_op_stored` is what reduction runs.
pub fn nat_op_guard(fe: &FEnv, c: &Name) -> bool {
    if nat_lit_supported(fe) {
        if deps_all_stored(fe, &nat_op_deps(c), 0) {
            if name::beq(c, &nat_beq_name())
                || name::beq(c, &nat_ble_name())
                || name::contains(&nat_div_mod_names(), c)
            {
                if lp_empty(fe, &bool_true_name()) {
                    lp_empty(fe, &bool_false_name())
                } else {
                    false
                }
            } else {
                true
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:674-684 natOpWfNames
/// The pin-certified WF-recursive `Nat` operations, as a *safety net*: the
/// same eight names as `natDivModNames`, spelled separately in the Lean and
/// separately here.
pub fn nat_op_wf_names() -> Vec<Name> {
    let mut ns: Vec<Name> = Vec::new();
    ns.push(nat_div_name());
    ns.push(nat_mod_name());
    ns.push(nat_gcd_name());
    ns.push(nat_land_name());
    ns.push(nat_lor_name());
    ns.push(nat_xor_name());
    ns.push(nat_shift_left_name());
    ns.push(nat_shift_right_name());
    ns
}

/// con-leche: ConLeche/Kernel/Core.lean:686-692 Expr.substConst0
/// Substitute the level-monomorphic constant `n` by `r` through an
/// application spine (the certification equations' self-references; the
/// equation sides are binder-free, so only `app` recurses).
pub fn subst_const0(n: &Name, r: &Expr, e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Const(c, us) => {
            if us.len() == 0 && name::beq(c, n) {
                expr::dup(r)
            } else {
                expr::dup(e)
            }
        }
        ExprKind::App(f, a) => expr::app(subst_const0(n, r, f), subst_const0(n, r, a)),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:694-710 Expr.substConstAll
/// Substitute the level-monomorphic constant `n` by the *closed* term `r`
/// everywhere, including under binders.  `fvar` annotations are not entered:
/// the substitution runs on closed input terms only.
pub fn subst_const_all(n: &Name, r: &Expr, e: &Expr) -> Expr {
    match &e.0.kind {
        ExprKind::Const(c, us) => {
            if us.len() == 0 && name::beq(c, n) {
                expr::dup(r)
            } else {
                expr::dup(e)
            }
        }
        ExprKind::App(f, a) => expr::app(subst_const_all(n, r, f), subst_const_all(n, r, a)),
        ExprKind::Lam(ty, b, mb) => expr::lam(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, b),
            expr::binder_meta_dup(mb),
        ),
        ExprKind::ForallE(ty, b, mb) => expr::forall_e(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, b),
            expr::binder_meta_dup(mb),
        ),
        ExprKind::LetE(ty, v, b) => expr::let_e(
            subst_const_all(n, r, ty),
            subst_const_all(n, r, v),
            subst_const_all(n, r, b),
        ),
        ExprKind::Proj(s, i, pe) => expr::proj(name::dup(s), *i, subst_const_all(n, r, pe)),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:712-722 natOpCod
/// con-leche: ConLeche/Kernel/DeclCheck.lean:209-217 natOpCodF
/// The pinned codomain of a structural-`Nat` operation: `Bool` (itself
/// stored level-monomorphically at type `Sort 1`) for the comparisons, `Nat`
/// otherwise.
pub fn nat_op_cod(fe: &FEnv, c: &Name, e: &Expr) -> bool {
    if name::beq(c, &nat_beq_name()) || name::beq(c, &nat_ble_name()) {
        if expr::beq(e, &expr::mk_const(bool_name(), Vec::new())) {
            bool_stored_ok(fe)
        } else {
            false
        }
    } else {
        expr::beq(e, &expr::mk_const(basis_names::nat_name(), Vec::new()))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:712-722 natOpCod
/// The cited `match env.find? boolName with | some ci =>
/// ci.toConstantVal.levelParams.isEmpty ∧ ci.toConstantVal.type == .sort
/// (.succ .zero) | none => false`, factored out.
pub fn bool_stored_ok(fe: &FEnv) -> bool {
    match fenv::find(fe, &bool_name()) {
        Some(ci) => {
            let cv = env::to_constant_val(ci);
            if cv.level_params.len() == 0 {
                expr::beq(&cv.ty, &expr::sort(level::succ(level::zero())))
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:724-739 natOpTyPinned
/// con-leche: ConLeche/Kernel/DeclCheck.lean:219-231 natOpTyPinnedF
/// The pinned type of a certified `Nat` operation: `Nat → Nat` for the unary
/// `pred`, `Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat →
/// Bool` for the comparisons.
pub fn nat_op_ty_pinned(fe: &FEnv, c: &Name, ty: &Expr) -> bool {
    let nat_ty = expr::mk_const(basis_names::nat_name(), Vec::new());
    if name::beq(c, &nat_pred_name()) {
        match &ty.0.kind {
            ExprKind::ForallE(dom, body, _) => {
                if expr::beq(dom, &nat_ty) {
                    nat_op_cod(fe, c, body)
                } else {
                    false
                }
            }
            _ => false,
        }
    } else {
        match &ty.0.kind {
            ExprKind::ForallE(dom, inner, _) => match &inner.0.kind {
                ExprKind::ForallE(dom2, body, _) => {
                    if expr::beq(dom, &nat_ty) && expr::beq(dom2, &nat_ty) {
                        nat_op_cod(fe, c, body)
                    } else {
                        false
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:741-747 natOpStoredOk
/// con-leche: ConLeche/Kernel/DeclCheck.lean:233-238 natOpStoredOkF
/// con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
/// Op `n` is stored as a level-monomorphic definition with the pinned type.
pub fn nat_op_stored_ok(fe: &FEnv, n: &Name) -> bool {
    match defn_probe(fe, n) {
        Some((cv, _, _)) => {
            if cv.level_params.len() == 0 {
                nat_op_ty_pinned(fe, n, &cv.ty)
            } else {
                false
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:749-772 natOpStored
/// **The reduction-time test for a certified `Nat` operation**: is `c`
/// stored as a definition at all?  The install fold invariant carries
/// `natOpGuard` for all sixteen guarded names, so on every environment the
/// checker builds the two tests agree and the cheap one is a single `find?`.
pub fn nat_op_stored(fe: &FEnv, c: &Name) -> bool {
    match fenv::find(fe, c) {
        Some(ConstantInfo::DefnInfo(_, _, _)) => true,
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// The fourteen binary operations the cited `∨`-chain names, as their own
/// predicate.
pub fn is_nat_bin_op(c: &Name) -> bool {
    name::beq(c, &nat_add_name())
        || name::beq(c, &nat_sub_name())
        || name::beq(c, &nat_mul_name())
        || name::beq(c, &nat_pow_name())
        || name::beq(c, &nat_beq_name())
        || name::beq(c, &nat_ble_name())
        || name::beq(c, &nat_div_name())
        || name::beq(c, &nat_mod_name())
        || name::beq(c, &nat_gcd_name())
        || name::beq(c, &nat_land_name())
        || name::beq(c, &nat_lor_name())
        || name::beq(c, &nat_xor_name())
        || name::beq(c, &nat_shift_left_name())
        || name::beq(c, &nat_shift_right_name())
}

/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// Literal acceleration (the official kernel's `reduceNat`, run in the
/// `whnf` loop *before* delta-unfolding): pack `Nat.succ` applied to a
/// literal back into a literal, and fold the fourteen binary operations on
/// literal arguments.
///
/// The argument order is load-bearing (the audit's D15): the **first**
/// argument is head-normalised and, unless it is a literal, the step fails
/// *without touching the second*.  The `.app (.app (.const c []) a) b`
/// pattern is read outermost-in, so the Rust's `a` is the cited `b` and the
/// inner application's argument is the cited `a`.
pub fn reduce_nat(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Option<Expr>> {
    const M: [u32; 34] = [
        110, 97, 116, 105, 118, 101, 32, 78, 97, 116, 32, 99, 111, 109, 112, 117, 116, 97,
        116, 105, 111, 110, 32, 111, 110, 32, 108, 105, 116, 101, 114, 97, 108, 115,
    ];
    match &e.0.kind {
        ExprKind::App(f, b) => match &f.0.kind {
            ExprKind::Const(c, us) => {
                if us.len() == 0
                    && name::beq(c, &basis_names::nat_succ_name())
                    && nat_lit_supported(fe)
                {
                    match core_c::whnf(mode, fuel, st, fe, depth, b) {
                        Err(err) => Err(err),
                        Ok(wa) => match raw_nat_lit(&wa) {
                            Some(n) => Ok(Some(expr::lit(Literal::NatVal(nat::add(
                                &n,
                                &nat::one(),
                            ))))),
                            None => Ok(None),
                        },
                    }
                } else {
                    Ok(None)
                }
            }
            ExprKind::App(g, a) => match &g.0.kind {
                ExprKind::Const(c, us) => {
                    if us.len() != 0 {
                        Ok(None)
                    } else if is_nat_bin_op(c) && nat_op_stored(fe, c) {
                        reduce_nat_bin(mode, fuel, st, fe, depth, c, a, b)
                    } else if name::contains(&nat_op_wf_names(), c) && nat_lit_supported(fe) {
                        match reduce_nat_lits(mode, fuel, st, fe, depth, a, b) {
                            Err(err) => Err(err),
                            Ok(None) => Ok(None),
                            Ok(Some(_)) => Err(core_types::not_implemented(
                                core_types::code_points(&M),
                            )),
                        }
                    } else {
                        Ok(None)
                    }
                }
                _ => Ok(None),
            },
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// The certified-operation arm of `reduce_nat`: both arguments read as
/// literals, first one then the other, and `nat_op_result` folds.
pub fn reduce_nat_bin(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    a: &Expr,
    b: &Expr,
) -> CheckM<Option<Expr>> {
    match reduce_nat_lits(mode, fuel, st, fe, depth, a, b) {
        Err(err) => Err(err),
        Ok(None) => Ok(None),
        Ok(Some(p)) => Ok(nat_op_result(c, &p.0, &p.1)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// The two-literal read both binary arms share: head-normalise the first
/// argument and stop unless it is a literal, then the second.  `None` is the
/// cited `pure none`.
pub fn reduce_nat_lits(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<Option<(Nat, Nat)>> {
    match core_c::whnf(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(wa) => match raw_nat_lit(&wa) {
            None => Ok(None),
            Some(n1) => match core_c::whnf(mode, fuel, st, fe, depth, b) {
                Err(err) => Err(err),
                Ok(wb) => match raw_nat_lit(&wb) {
                    None => Ok(None),
                    Some(n2) => Ok(Some((n1, n2))),
                },
            },
        },
    }
}

// ---------------------------------------------------------------------------
// Telescope certificates and proof irrelevance (`Core.lean:848-981`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:828-860 iotaCerts
/// Certify a spine against a recursor telescope: each argument's inferred
/// type is defeq to the corresponding (instantiated) domain.  This is what
/// hands the soundness proof the memberships the iota equations need.
///
/// **The ι-slot licence**: at a *licensed* walk (`lic = true`, set only by
/// `iota_rec`'s two calls) a slot whose `∀`-binder datum is `.never` is
/// skipped.  The `i = 0` wrapper of the index recursion below.
pub fn iota_certs(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    lic: bool,
    ty: &Expr,
    args: &Vec<Expr>,
) -> CheckM<bool> {
    iota_certs_from(mode, fuel, st, fe, depth, lic, ty, args, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:828-860 iotaCerts
/// The index recursion behind `iota_certs`: `i` is the position of the
/// cited `arg :: rest` in `args`, and `ty` is the telescope already
/// instantiated at `args[..i]`.  The cited three arms are, in order, `i >=
/// args.len()`, the `∀` arm, and "arguments left but no binder".
pub fn iota_certs_from(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    lic: bool,
    ty: &Expr,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<bool> {
    if i >= args.len() {
        Ok(true)
    } else {
        match &ty.0.kind {
            ExprKind::ForallE(dom, body, mb) => {
                let dom = expr::dup(dom);
                let next = expr_ops::instantiate1(body, &args[i], 0);
                if lic && prop_when::is_never(&mb.pw) {
                    iota_certs_from(mode, fuel, st, fe, depth, lic, &next, args, i + 1)
                } else {
                    match core_c::infer_io(mode, fuel, st, fe, depth, &args[i]) {
                        Err(err) => Err(err),
                        Ok(ta) => match core_c::defeq(mode, fuel, st, fe, depth, &ta, &dom) {
                            Err(err) => Err(err),
                            Ok(true) => iota_certs_from(
                                mode, fuel, st, fe, depth, lic, &next, args, i + 1,
                            ),
                            Ok(false) => Ok(false),
                        },
                    }
                }
            }
            _ => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:862-867 piResidual
/// Peel a `∀`-telescope along an argument list (the residual type of a fully
/// applied telescope).  The `i = 0` wrapper of the index recursion below.
pub fn pi_residual(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    pi_residual_from(e, args, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:862-867 piResidual
/// The index recursion behind `pi_residual`.
pub fn pi_residual_from(e: &Expr, args: &Vec<Expr>, i: usize) -> Option<Expr> {
    if i >= args.len() {
        Some(expr::dup(e))
    } else {
        match &e.0.kind {
            ExprKind::ForallE(_, b, _) => {
                let next = expr_ops::instantiate1(b, &args[i], 0);
                pi_residual_from(&next, args, i + 1)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:869-878 defEqList
/// Pairwise definitional equality of two spines.  The `i = 0` wrapper of the
/// index recursion below.
pub fn def_eq_list(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ys: &Vec<Expr>,
) -> CheckM<bool> {
    def_eq_list_from(mode, fuel, st, fe, depth, xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:869-878 defEqList
/// The index recursion behind `def_eq_list`: the cited `[], []` arm is "both
/// exhausted", the cons arm is "both in range", and the wildcard is the
/// length mismatch.
pub fn def_eq_list_from(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ys: &Vec<Expr>,
    i: usize,
) -> CheckM<bool> {
    if i >= xs.len() && i >= ys.len() {
        Ok(true)
    } else if i < xs.len() && i < ys.len() {
        match core_c::defeq(mode, fuel, st, fe, depth, &xs[i], &ys[i]) {
            Err(err) => Err(err),
            Ok(true) => def_eq_list_from(mode, fuel, st, fe, depth, xs, ys, i + 1),
            Ok(false) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:880-896 iotaIndexOk
/// The canonical-index comparison of a firing ι redex: where the recursor
/// has indices (`rP < mI`) the residual of the constructor's telescope along
/// the major's spine must agree, past the `cnP` parameters, with the
/// recursor's index arguments.  At `mI = rP` there is nothing to compare.
pub fn iota_index_ok(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    m_i: u64,
    r_p: u64,
    cn_p: u64,
    ty_ctor: &Expr,
    margs: &Vec<Expr>,
    idx: &Vec<Expr>,
) -> CheckM<bool> {
    if m_i == r_p {
        Ok(true)
    } else {
        match pi_residual(ty_ctor, margs) {
            Some(residual) => {
                let args = expr_ops::get_app_args(&residual);
                let rest = drop_exprs(&args, cn_p as usize);
                def_eq_list(mode, fuel, st, fe, depth, &rest, idx)
            }
            None => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:898-929 proofIrrel
/// Proof irrelevance certification: both sides' types whnf to the basis unit
/// type, or both sides' types' *sorts* are `Prop`.  Every inference here is
/// at the io grade (official's `is_def_eq_proof_irrel` runs `infer_type`,
/// always `infer_only`).
pub fn proof_irrel(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match core_c::infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match core_c::whnf(mode, fuel, st, fe, depth, &ta) {
            Err(err) => Err(err),
            Ok(wta) => {
                if is_unit_like_ty(fe, &wta) {
                    match core_c::infer_io(mode, fuel, st, fe, depth, b) {
                        Err(err) => Err(err),
                        Ok(tb) => match core_c::whnf(mode, fuel, st, fe, depth, &tb) {
                            Err(err) => Err(err),
                            Ok(wtb) => Ok(is_unit_like_ty(fe, &wtb)),
                        },
                    }
                } else {
                    prop_legs(mode, fuel, st, fe, depth, &ta, b)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:898-929 proofIrrel
/// con-leche: ConLeche/Kernel/Core.lean:931-973 propIrrel
/// The two `Prop` legs both irrelevance tests end in, verbatim in the Lean
/// and therefore one function here: the type of `ta` whnfs to a sort that is
/// `Prop`, and so does the type of the type of `b`.  `ta` is the caller's
/// already-computed `inferIO a` (the cited `let ta ← r.inferIO depth a`).
pub fn prop_legs(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ta: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match core_c::infer_io(mode, fuel, st, fe, depth, ta) {
        Err(err) => Err(err),
        Ok(tta) => match core_c::whnf(mode, fuel, st, fe, depth, &tta) {
            Err(err) => Err(err),
            Ok(wtta) => match &wtta.0.kind {
                ExprKind::Sort(u_t) => match lift_fueled(level::is_equiv(u_t, &level::zero())) {
                    Err(err) => Err(err),
                    Ok(ok_a) => match core_c::infer_io(mode, fuel, st, fe, depth, b) {
                        Err(err) => Err(err),
                        Ok(tb) => match core_c::infer_io(mode, fuel, st, fe, depth, &tb) {
                            Err(err) => Err(err),
                            Ok(ttb) => {
                                match core_c::whnf(mode, fuel, st, fe, depth, &ttb) {
                                    Err(err) => Err(err),
                                    Ok(wttb) => match &wttb.0.kind {
                                        ExprKind::Sort(v_t) => match lift_fueled(
                                            level::is_equiv(v_t, &level::zero()),
                                        ) {
                                            Err(err) => Err(err),
                                            Ok(ok_b) => Ok(ok_a && ok_b),
                                        },
                                        _ => Ok(false),
                                    },
                                }
                            }
                        },
                    },
                },
                _ => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:931-973 propIrrel
/// **The hoisted proof-irrelevance test**: the `Prop` branch of `proof_irrel`
/// alone, with the two head-symbol fast arms in front — the "not a proof"
/// arm (`prop_read::not_proof_fast` on either side refuses the shortcut) and
/// the "yes" arm (`prop_read::is_proof_fast` on both sides answers `true`,
/// the squash-regime licence).  Both fire in both modes (con-leche's user
/// ruling of 2026-09-06).
pub fn prop_irrel(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    if prop_read::not_proof_fast(fe, a) || prop_read::not_proof_fast(fe, b) {
        Ok(false)
    } else if prop_read::is_proof_fast(fe, a) && prop_read::is_proof_fast(fe, b) {
        Ok(true)
    } else {
        match core_c::infer_io(mode, fuel, st, fe, depth, a) {
            Err(err) => Err(err),
            Ok(ta) => prop_legs(mode, fuel, st, fe, depth, &ta, b),
        }
    }
}

// ---------------------------------------------------------------------------
// Structure eta (`Core.lean:983-1213`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:975-998 structEtaProjCerts
/// The per-projection telescope certificates of a structural eta
/// certification at a **projection-function** slot family: for every field
/// index, the installed projection function's telescope is certified against
/// the type's arguments and the stuck side.  A tower-backed family has no
/// per-field telescope and needs no certificate.
///
/// Deviation: the cited `List Nat` argument is always `List.range nF`
/// (`structEtaCertWith`'s only call site), so the port takes the count and
/// walks `j = 0 … nF - 1`.
pub fn struct_eta_proj_certs(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    t: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    b: &Expr,
    lps_t: &Vec<Name>,
    n_f: u64,
) -> CheckM<bool> {
    struct_eta_proj_certs_from(mode, fuel, st, fe, depth, t, us2, targs, b, lps_t, n_f, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:975-998 structEtaProjCerts
/// The index recursion behind `struct_eta_proj_certs`.
pub fn struct_eta_proj_certs_from(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    t: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    b: &Expr,
    lps_t: &Vec<Name>,
    n_f: u64,
    j: u64,
) -> CheckM<bool> {
    if j >= n_f {
        Ok(true)
    } else {
        match rec_probe(fe, &env::proj_fn_name(t, j)) {
            Some((cvp, _, _, _)) => {
                if prop_when::names_beq(&cvp.level_params, lps_t)
                    && expr_ops::strip_pis((targs.len() as u64) + 1, &cvp.ty).is_some()
                {
                    let pty =
                        expr_ops::instantiate_level_params(&cvp.level_params, us2, &cvp.ty);
                    let spine = append_exprs(env::exprs_copy(targs), &expr_singleton(b));
                    match iota_certs(mode, fuel, st, fe, depth, false, &pty, &spine) {
                        Err(err) => Err(err),
                        Ok(true) => struct_eta_proj_certs_from(
                            mode, fuel, st, fe, depth, t, us2, targs, b, lps_t, n_f, j + 1,
                        ),
                        Ok(false) => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            }
            None => Ok(false),
        }
    }
}

/// con-leche: none — the `[e]` singleton list of `targs ++ [b]`, as a `Vec`
/// A one-element `Vec<Expr>` (`level::singleton` is its `Level` twin).
pub fn expr_singleton(e: &Expr) -> Vec<Expr> {
    let mut v: Vec<Expr> = Vec::new();
    v.push(expr::dup(e));
    v
}

/// con-leche: ConLeche/Kernel/Core.lean:1017-1027 etaProjs
/// The fabricated projections of a structure-eta spine: `.proj T j b` nodes
/// when every slot has a table entry (the direct install's structures — the
/// node is what the table types and reduces), else the modeled path's
/// projection-function applications.  The cited `towerSlotsAll` is read once,
/// as in the Lean's `if`.
pub fn eta_projs(
    fe: &FEnv,
    t: &Name,
    us: &Vec<Level>,
    targs: &Vec<Expr>,
    b: &Expr,
    n_f: u64,
) -> Vec<Expr> {
    let tower = fenv::tower_slots_all_f(fe, t, n_f);
    eta_projs_from(tower, t, us, targs, b, n_f, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Core.lean:1017-1027 etaProjs
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

/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The structure-eta certificate against a *given* weak-head-normal type of
/// the stuck side (callers that already reduced it pass their own copy).
/// `a` is a fully applied constructor of an eta-capable structure, `b`
/// inhabits that structure type, the constructor's parameters are the type's
/// arguments, and every field is the corresponding installed projection
/// applied to `b`.
///
/// The deep cited `if … then … else pure false` nest is kept arm for arm;
/// the syntactic conjunction block is `struct_eta_shape_ok` so that the
/// state-touching steps below it read in sequence.
pub fn struct_eta_cert_with(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
    wtb: &Expr,
) -> CheckM<bool> {
    let fa = expr_ops::get_app_fn(a);
    match &fa.0.kind {
        ExprKind::Const(c, us) => match ctor_probe(fe, c) {
            Some((cvc, cn_p, cn_f)) => {
                let aargs = expr_ops::get_app_args(a);
                if aargs.len() as u64 != cn_p + cn_f {
                    Ok(false)
                } else {
                    let ftb = expr_ops::get_app_fn(wtb);
                    match &ftb.0.kind {
                        ExprKind::Const(t, us2) => match ind_probe(fe, t) {
                            Some((cvt, caps)) => {
                                let targs = expr_ops::get_app_args(wtb);
                                if struct_eta_shape_ok(
                                    fe, c, us2, &targs, &cvc, &cvt, &caps, t,
                                ) {
                                    struct_eta_cert_steps(
                                        mode, fuel, st, fe, depth, us, us2, &aargs, &targs,
                                        b, &cvc, &cvt, &caps, t,
                                    )
                                } else {
                                    Ok(false)
                                }
                            }
                            None => Ok(false),
                        },
                        _ => Ok(false),
                    }
                }
            }
            None => Ok(false),
        },
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The cited syntactic conjunction block: the η capability and its
/// constructor, neither name reserved, the parameter count, the level count,
/// the constructor's own level parameters, and the one-kind slot discipline
/// (`towerSlotsAll || recSlotsAll`).  The `∧` cascade is an `if` nest.
pub fn struct_eta_shape_ok(
    fe: &FEnv,
    c: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    cvc: &ConstantVal,
    cvt: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
) -> bool {
    if !caps.eta {
        false
    } else if !name::beq(&caps.eta_ctor, c) {
        false
    } else if name::contains(&basis_names::reserved_basis_names(), t) {
        false
    } else if name::contains(&basis_names::reserved_basis_names(), c) {
        false
    } else if targs.len() as u64 != caps.eta_params {
        false
    } else if us2.len() != cvt.level_params.len() {
        false
    } else if !prop_when::names_beq(&cvc.level_params, &cvt.level_params) {
        false
    } else {
        fenv::tower_slots_all_f(fe, t, caps.eta_fields)
            || fenv::rec_slots_all_f(fe, t, caps.eta_fields)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The certificate's state-touching steps, in the cited order: the level
/// lists are equivalent, the type application is certified against the type
/// former's telescope, the per-slot certificates run at a
/// projection-function family (a tabled one has none), the constructor's
/// parameters are the type's arguments, the TT-lane synthetic-spine
/// certificate runs at `mode.ttChecks`, and the fields are the fabricated
/// projections.
pub fn struct_eta_cert_steps(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    us: &Vec<Level>,
    us2: &Vec<Level>,
    aargs: &Vec<Expr>,
    targs: &Vec<Expr>,
    b: &Expr,
    cvc: &ConstantVal,
    cvt: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
) -> CheckM<bool> {
    match lift_fueled(level::is_equiv_list(us, us2)) {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let tty = expr_ops::instantiate_level_params(&cvt.level_params, us2, &cvt.ty);
            match iota_certs(mode, fuel, st, fe, depth, false, &tty, targs) {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => {
                    let slots = if fenv::tower_slots_all_f(fe, t, caps.eta_fields) {
                        Ok(true)
                    } else {
                        struct_eta_proj_certs(
                            mode,
                            fuel,
                            st,
                            fe,
                            depth,
                            t,
                            us2,
                            targs,
                            b,
                            &cvt.level_params,
                            caps.eta_fields,
                        )
                    };
                    match slots {
                        Err(err) => Err(err),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            let params = expr_ops::take_exprs(aargs, caps.eta_params as usize);
                            match def_eq_list(mode, fuel, st, fe, depth, &params, targs) {
                                Err(err) => Err(err),
                                Ok(false) => Ok(false),
                                Ok(true) => struct_eta_cert_fields(
                                    mode, fuel, st, fe, depth, us, us2, aargs, targs, b, cvc,
                                    caps, t,
                                ),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The last two steps: the TT-lane synthetic-spine certification (con-leche's
/// task #137, skipped unless `mode.ttChecks` — which is constantly `false`
/// since con-leche's task #148, so this arm is dead but ported) and the
/// field comparison against `eta_projs`.
pub fn struct_eta_cert_fields(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    us: &Vec<Level>,
    us2: &Vec<Level>,
    aargs: &Vec<Expr>,
    targs: &Vec<Expr>,
    b: &Expr,
    cvc: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
) -> CheckM<bool> {
    let projs = eta_projs(fe, t, us2, targs, b, caps.eta_fields);
    let tt = if env::tt_checks(mode) {
        let cty = expr_ops::instantiate_level_params(&cvc.level_params, us, &cvc.ty);
        let spine = append_exprs(env::exprs_copy(targs), &projs);
        iota_certs(mode, fuel, st, fe, depth, false, &cty, &spine)
    } else {
        Ok(true)
    };
    match tt {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let fields = drop_exprs(aargs, caps.eta_params as usize);
            def_eq_list(mode, fuel, st, fe, depth, &fields, &projs)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1103-1114 etaCtorShape
/// The constructor shape official's `try_eta_struct_core` tests before
/// inferring anything: the candidate's head is a stored constructor applied
/// to exactly its parameters and fields.
pub fn eta_ctor_shape(fe: &FEnv, a: &Expr) -> bool {
    let f = expr_ops::get_app_fn(a);
    match &f.0.kind {
        ExprKind::Const(c, _) => match fenv::find(fe, c) {
            Some(ConstantInfo::CtorInfo(_, cn_p, cn_f)) => {
                (expr_ops::get_app_args(a).len() as u64) == *cn_p + *cn_f
            }
            Some(_) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1116-1139 structEtaCert
/// Structural eta certification for a stored eta-capable structure, with the
/// constructor-shape test **first** (the divergence audit's D13): official
/// `try_eta_struct_core` reads `s`'s head and arity syntactically and infers
/// nothing unless they fit.
pub fn struct_eta_cert(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    if eta_ctor_shape(fe, a) {
        match core_c::infer_io(mode, fuel, st, fe, depth, b) {
            Err(err) => Err(err),
            Ok(tb) => match core_c::whnf(mode, fuel, st, fe, depth, &tb) {
                Err(err) => Err(err),
                Ok(wtb) => struct_eta_cert_with(mode, fuel, st, fe, depth, a, b, &wtb),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1141-1169 structUnitCert
/// Unit-likeness certification: `a` and `b` inhabit the same stored unit-like
/// family (the types are definitionally equal and the type application is
/// certified against the family's telescope), so their values coincide by the
/// stored unit law.
pub fn struct_unit_cert(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match core_c::infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match core_c::whnf(mode, fuel, st, fe, depth, &ta) {
            Err(err) => Err(err),
            Ok(wta) => {
                let f = expr_ops::get_app_fn(&wta);
                match &f.0.kind {
                    ExprKind::Const(t, us2) => match ind_probe(fe, t) {
                        Some((cvt, caps)) => {
                            let targs = expr_ops::get_app_args(&wta);
                            if unit_shape_ok(t, us2, &targs, &cvt, &caps) {
                                struct_unit_steps(
                                    mode, fuel, st, fe, depth, &wta, b, us2, &targs, &cvt,
                                )
                            } else {
                                Ok(false)
                            }
                        }
                        None => Ok(false),
                    },
                    _ => Ok(false),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1141-1169 structUnitCert
/// The cited syntactic conjunction: the unit-like capability, the name not
/// reserved, the parameter count and the level count.
pub fn unit_shape_ok(
    t: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    cvt: &ConstantVal,
    caps: &IndCaps,
) -> bool {
    if !caps.unitlike {
        false
    } else if name::contains(&basis_names::reserved_basis_names(), t) {
        false
    } else if targs.len() as u64 != caps.unit_params {
        false
    } else {
        us2.len() == cvt.level_params.len()
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1141-1169 structUnitCert
/// The state-touching tail: `b`'s reduced type is definitionally equal to
/// `a`'s, and the type application is certified against the family's
/// telescope.
pub fn struct_unit_steps(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    wta: &Expr,
    b: &Expr,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    cvt: &ConstantVal,
) -> CheckM<bool> {
    match core_c::infer_io(mode, fuel, st, fe, depth, b) {
        Err(err) => Err(err),
        Ok(tb) => match core_c::whnf(mode, fuel, st, fe, depth, &tb) {
            Err(err) => Err(err),
            Ok(wtb) => match core_c::defeq(mode, fuel, st, fe, depth, wta, &wtb) {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => {
                    let tty =
                        expr_ops::instantiate_level_params(&cvt.level_params, us2, &cvt.ty);
                    iota_certs(mode, fuel, st, fe, depth, false, &tty, targs)
                }
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1171-1196 etaCert
/// Eta certification for a one-sided λ against a stuck term `b`: `b`'s type
/// whnfs to a `∀` whose domain is defeq to the λ's, and the λ's body is
/// pointwise the application of `b`.  The prop-ness annotations are compared
/// **last** (con-leche's task #161), so a mismatch fires only on an otherwise
/// successful η certification.
pub fn eta_cert(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty1: &Expr,
    body1: &Expr,
    m1: &BinderMeta,
    b: &Expr,
) -> CheckM<bool> {
    match core_c::infer_io(mode, fuel, st, fe, depth, b) {
        Err(err) => Err(err),
        Ok(tb) => match core_c::whnf(mode, fuel, st, fe, depth, &tb) {
            Err(err) => Err(err),
            Ok(wtb) => match &wtb.0.kind {
                ExprKind::ForallE(ty2, _, m2) => {
                    let ty2 = expr::dup(ty2);
                    let pw2 = prop_when::dup(&m2.pw);
                    match core_c::defeq(mode, fuel, st, fe, depth, &ty2, ty1) {
                        Err(err) => Err(err),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            eta_cert_body(mode, fuel, st, fe, depth, ty1, body1, m1, b, &pw2)
                        }
                    }
                }
                _ => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1171-1196 etaCert
/// The pointwise comparison and the annotation check of `eta_cert`, once the
/// domains have matched.
pub fn eta_cert_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty1: &Expr,
    body1: &Expr,
    m1: &BinderMeta,
    b: &Expr,
    pw2: &PropWhen,
) -> CheckM<bool> {
    const M: [u32; 30] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 101, 116, 97, 41,
    ];
    let v = expr::fvar(depth, expr::dup(ty1));
    let lhs = expr_ops::instantiate1(body1, &v, 0);
    let rhs = expr::app(expr::dup(b), expr::dup(&v));
    match core_c::defeq(mode, fuel, st, fe, depth + 1, &lhs, &rhs) {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            if env::verified_checks(mode) && !prop_when::beq(&m1.pw, pw2) {
                Err(core_types::not_implemented(core_types::code_points(&M)))
            } else {
                Ok(true)
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1198-1208 stuckIrrel
/// The fallback for structurally distinct stuck terms: structural eta in
/// either direction, unit-likeness, else proof irrelevance.
pub fn stuck_irrel(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match struct_eta_cert(mode, fuel, st, fe, depth, a, b) {
        Err(err) => Err(err),
        Ok(true) => Ok(true),
        Ok(false) => match struct_eta_cert(mode, fuel, st, fe, depth, b, a) {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => match struct_unit_cert(mode, fuel, st, fe, depth, a, b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => proof_irrel(mode, fuel, st, fe, depth, a, b),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1210-1218 etaFabArgs
/// The eta-rescue fabrication's argument spine: the reduced type's arguments
/// followed by the installed projection functions applied to the stuck
/// major.  Nothing executable calls it — `etaFabArgsE` is what `majorToCtor`
/// uses — but it is ported so the provenance gate stays in step with its
/// source (task #11's `beqRecursive` rule).
pub fn eta_fab_args(
    t: &Name,
    ust: &Vec<Level>,
    targs: &Vec<Expr>,
    major: &Expr,
    n_f: u64,
) -> Vec<Expr> {
    let projs = eta_projs_from(false, t, ust, targs, major, n_f, 0, Vec::new());
    append_exprs(env::exprs_copy(targs), &projs)
}

/// con-leche: ConLeche/Kernel/Core.lean:1220-1225 etaFabArgsE
/// `eta_fab_args` at the entry kind: the projections are `eta_projs`' —
/// `.proj` nodes at an all-tower slot family, the modeled spelling otherwise.
pub fn eta_fab_args_e(
    fe: &FEnv,
    t: &Name,
    ust: &Vec<Level>,
    targs: &Vec<Expr>,
    major: &Expr,
    n_f: u64,
) -> Vec<Expr> {
    let projs = eta_projs(fe, t, ust, targs, major, n_f);
    append_exprs(env::exprs_copy(targs), &projs)
}

/// con-leche: ConLeche/Kernel/Core.lean:1227-1253 ProjEntry.fireOk
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

/// con-leche: ConLeche/Kernel/Core.lean:1255-1268 andRescueSlotsOf
/// con-leche: ConLeche/Kernel/Core.lean:1270-1272 andRescueSlots
/// con-leche: ConLeche/Kernel/FEnv.lean:101-103 andRescueSlotsF
/// **The pinned `And`'s projection slots, ready to fire**: the two tower
/// entries of `And` are stored, name the rule's constructor at the major's
/// parameter count, and their `Prop` guards pass at the levels `ust`.  The
/// three cited declarations are one function here (the module note's point
/// 3: the `findProj?` abstraction exists for the indexed twin, which is the
/// port's only spelling).
pub fn and_rescue_slots(fe: &FEnv, ctor: &Name, n_p: u64, ust: &Vec<Level>) -> bool {
    and_rescue_slots_from(fe, ctor, n_p, ust, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:1255-1268 andRescueSlotsOf
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

/// con-leche: ConLeche/Kernel/Core.lean:1255-1268 andRescueSlotsOf
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

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The scope guard all three rescue branches run on their fabrication
/// (cf. `annotateProjElim`): the fabricated major is well-scoped at the
/// ambient depth, closed under loose `bvar`s, and introduces no free
/// variable the major does not already have.  Keeping it syntactic keeps the
/// rescue's verification local.
pub fn fab_scope_ok(fab: &Expr, major: &Expr, depth: u64) -> bool {
    if !expr_ops::wscoped_b(depth, fab) {
        false
    } else if !expr_ops::loose_bvars_bounded(0, fab) {
        false
    } else {
        fvar_leaves_subset(&expr_ops::fvar_leaves(fab), &expr_ops::fvar_leaves(major))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure` in the
/// official kernel): a recursor's major premise that does not whnf to a
/// constructor application may still be *replaced* by one.  An uncertified
/// major stays put — sound, the reduction simply stays stuck.
///
/// This function is the cited cheap syntactic dispatch (a single-rule
/// recursor whose rule carries the matching install-time rescue bit); the
/// three branches are `major_to_ctor_k`, `major_to_ctor_eta` and
/// `major_to_ctor_and`, one per cited `if`.
///
/// Deviation: the cited `_recName : Name` parameter is unused in the Lean
/// too (hence its underscore), so the port drops it and `prepare_major`
/// passes one argument fewer.
pub fn major_to_ctor(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rules: &Vec<RecRule>,
    major: &Expr,
) -> CheckM<Expr> {
    if is_ctor_app(fe, major) {
        Ok(expr::dup(major))
    } else if rules.len() != 1 {
        Ok(expr::dup(major))
    } else {
        let rl: &RecRule = &rules[0];
        match ctor_probe(fe, &rl.ctor) {
            Some((cvj, cn_p, _)) => {
                let res = expr_ops::pi_result(&cvj.ty);
                let head = expr_ops::get_app_fn(&res);
                match &head.0.kind {
                    ExprKind::Const(t, _) => match ind_probe(fe, t) {
                        Some((cvt, caps)) => {
                            if rl.k {
                                major_to_ctor_k(
                                    mode, fuel, st, fe, depth, rl, &cvj, cn_p, t, major,
                                )
                            } else if rl.eta {
                                major_to_ctor_eta(
                                    mode, fuel, st, fe, depth, &cvj, &cvt, &caps, t, major,
                                )
                            } else if name::beq(t, &basis_names::and_name()) {
                                major_to_ctor_and(
                                    mode, fuel, st, fe, depth, rl, &cvj, cn_p, t, major,
                                )
                            } else {
                                Ok(expr::dup(major))
                            }
                        }
                        None => Ok(expr::dup(major)),
                    },
                    _ => Ok(expr::dup(major)),
                }
            }
            None => Ok(expr::dup(major)),
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The **K branch**: for a K-flagged inductive proposition the
/// parameters-only application of the single constructor is fabricated from
/// the major's type and certified by the synthetic-spine telescope, the
/// official type check (`tmaj ≡ infer fab`) and proof irrelevance.
pub fn major_to_ctor_k(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rl: &RecRule,
    cvj: &ConstantVal,
    cn_p: u64,
    t: &Name,
    major: &Expr,
) -> CheckM<Expr> {
    match infer_io_whnf(mode, fuel, st, fe, depth, major) {
        Err(err) => Err(err),
        Ok(tmaj) => {
            let head = expr_ops::get_app_fn(&tmaj);
            match &head.0.kind {
                ExprKind::Const(t2, ust) => {
                    let targs = expr_ops::get_app_args(&tmaj);
                    if !name::beq(t2, t) || cvj.level_params.len() != ust.len() {
                        Ok(expr::dup(major))
                    } else if cn_p > targs.len() as u64 {
                        Ok(expr::dup(major))
                    } else {
                        let params = expr_ops::take_exprs(&targs, cn_p as usize);
                        let fab = expr_ops::mk_app_n(
                            expr::mk_const(name::dup(&rl.ctor), env::levels_copy(ust)),
                            &params,
                        );
                        if !fab_scope_ok(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cty = expr_ops::instantiate_level_params(
                                &cvj.level_params,
                                ust,
                                &cvj.ty,
                            );
                            match iota_certs(mode, fuel, st, fe, depth, false, &cty, &params)
                            {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => k_type_and_irrel(
                                    mode, fuel, st, fe, depth, &tmaj, &fab, major,
                                ),
                            }
                        }
                    }
                }
                _ => Ok(expr::dup(major)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The K branch's last two certificates, shared with the `And` branch: the
/// fabrication's type against the major's (for `Eq` this is the endpoint
/// condition) and then proof irrelevance as the soundness certificate.
pub fn k_type_and_irrel(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    tmaj: &Expr,
    fab: &Expr,
    major: &Expr,
) -> CheckM<Expr> {
    match core_c::infer_io(mode, fuel, st, fe, depth, fab) {
        Err(err) => Err(err),
        Ok(tfab) => match core_c::defeq(mode, fuel, st, fe, depth, tmaj, &tfab) {
            Err(err) => Err(err),
            Ok(false) => Ok(expr::dup(major)),
            Ok(true) => match proof_irrel(mode, fuel, st, fe, depth, fab, major) {
                Err(err) => Err(err),
                Ok(true) => Ok(expr::dup(fab)),
                Ok(false) => Ok(expr::dup(major)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// `r.whnf depth (← r.inferIO depth major)` — the major's reduced type, which
/// all three rescue branches open with.
pub fn infer_io_whnf(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match core_c::infer_io(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(t) => core_c::whnf(mode, fuel, st, fe, depth, &t),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The **η branch**: for an eta-capable structure the constructor of the
/// major's projections is fabricated and certified by the structure-eta
/// certificate.  The provably-nonzero test is the *instantiated* one
/// (con-leche's task #61): a static `piResultIsProp cvT.type = false` would
/// pass a parametric `Sort u` that a `Prop` instantiation collapses.
pub fn major_to_ctor_eta(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    cvj: &ConstantVal,
    cvt: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
    major: &Expr,
) -> CheckM<Expr> {
    match infer_io_whnf(mode, fuel, st, fe, depth, major) {
        Err(err) => Err(err),
        Ok(tmaj) => {
            let head = expr_ops::get_app_fn(&tmaj);
            match &head.0.kind {
                ExprKind::Const(t2, ust) => {
                    let targs = expr_ops::get_app_args(&tmaj);
                    if !name::beq(t2, t) {
                        Ok(expr::dup(major))
                    } else if targs.len() as u64 != caps.eta_params {
                        Ok(expr::dup(major))
                    } else if ust.len() != cvt.level_params.len() {
                        Ok(expr::dup(major))
                    } else if !caps_never_zero(&cvt.level_params, ust, caps) {
                        Ok(expr::dup(major))
                    } else {
                        let spine =
                            eta_fab_args_e(fe, t, ust, &targs, major, caps.eta_fields);
                        let fab = expr_ops::mk_app_n(
                            expr::mk_const(
                                name::dup(&caps.eta_ctor),
                                env::levels_copy(ust),
                            ),
                            &spine,
                        );
                        if !fab_scope_ok(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cty = expr_ops::instantiate_level_params(
                                &cvj.level_params,
                                ust,
                                &cvj.ty,
                            );
                            match iota_certs(mode, fuel, st, fe, depth, false, &cty, &spine) {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => eta_rescue_certs(
                                    mode, fuel, st, fe, depth, &fab, major, &tmaj, caps,
                                ),
                            }
                        }
                    }
                }
                _ => Ok(expr::dup(major)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The η branch's certificate: the structure-eta certificate against the
/// major's own reduced type, with the **0-field rescue** for the pinned basis
/// `PUnit` behind it (the generic certificate excludes reserved names; the
/// fabrication is the bare constructor, certified by proof irrelevance's
/// unit-likeness branch).
pub fn eta_rescue_certs(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    fab: &Expr,
    major: &Expr,
    tmaj: &Expr,
    caps: &IndCaps,
) -> CheckM<Expr> {
    match struct_eta_cert_with(mode, fuel, st, fe, depth, fab, major, tmaj) {
        Err(err) => Err(err),
        Ok(true) => Ok(expr::dup(fab)),
        Ok(false) => {
            if caps.eta_fields == 0 {
                match proof_irrel(mode, fuel, st, fe, depth, fab, major) {
                    Err(err) => Err(err),
                    Ok(true) => Ok(expr::dup(fab)),
                    Ok(false) => Ok(expr::dup(major)),
                }
            } else {
                Ok(expr::dup(major))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// **THE `And`-ONLY η RESCUE** (con-leche's user ruling: `And` and nothing
/// else).  `And.rec F h` at a stuck PROOF `h` fires through the fabrication
/// `And.intro a b (.proj And 0 h) (.proj And 1 h)`, certified the K branch's
/// way.  Official does not η-rescue a proposition, so this is an
/// accept-superset there.
pub fn major_to_ctor_and(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rl: &RecRule,
    cvj: &ConstantVal,
    cn_p: u64,
    t: &Name,
    major: &Expr,
) -> CheckM<Expr> {
    match infer_io_whnf(mode, fuel, st, fe, depth, major) {
        Err(err) => Err(err),
        Ok(tmaj) => {
            let head = expr_ops::get_app_fn(&tmaj);
            match &head.0.kind {
                ExprKind::Const(t2, ust) => {
                    let targs = expr_ops::get_app_args(&tmaj);
                    if !name::beq(t2, t) {
                        Ok(expr::dup(major))
                    } else if targs.len() as u64 != cn_p {
                        Ok(expr::dup(major))
                    } else if cvj.level_params.len() != ust.len() {
                        Ok(expr::dup(major))
                    } else if !and_rescue_slots(fe, &rl.ctor, cn_p, ust) {
                        Ok(expr::dup(major))
                    } else {
                        let mut projs: Vec<Expr> = Vec::new();
                        projs.push(expr::proj(name::dup(t), 0, expr::dup(major)));
                        projs.push(expr::proj(name::dup(t), 1, expr::dup(major)));
                        let spine = append_exprs(env::exprs_copy(&targs), &projs);
                        let fab = expr_ops::mk_app_n(
                            expr::mk_const(name::dup(&rl.ctor), env::levels_copy(ust)),
                            &spine,
                        );
                        if !fab_scope_ok(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cty = expr_ops::instantiate_level_params(
                                &cvj.level_params,
                                ust,
                                &cvj.ty,
                            );
                            match iota_certs(mode, fuel, st, fe, depth, false, &cty, &spine) {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => k_type_and_irrel(
                                    mode, fuel, st, fe, depth, &tmaj, &fab, major,
                                ),
                            }
                        }
                    }
                }
                _ => Ok(expr::dup(major)),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1458-1470 litMajorToCtor
/// Convert a literal major premise to constructor form: a `Nat` literal one
/// layer (`lit_to_ctor_if_nat`); a `String` literal to its *reduced*
/// constructor form — the reference kernels re-reduce after
/// `strLitToConstructor` since `String.ofList` is a definition.
pub fn lit_major_to_ctor(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match &e.0.kind {
        ExprKind::Lit(Literal::StrVal(s)) => {
            if str_lit_supported(fe) {
                let c = str_lit_to_constructor(s);
                core_c::whnf(mode, fuel, st, fe, depth, &c)
            } else {
                Ok(expr::dup(e))
            }
        }
        _ => Ok(lit_to_ctor_if_nat(fe, e)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1472-1486 projLitToCtor
/// Convert a string-literal projection scrutinee to its *reduced*
/// constructor form — the references' proj expansion site.  Only `String`
/// literals; anything else passes through unchanged (this is where it differs
/// from `lit_major_to_ctor`, which also packs a `Nat` literal).
pub fn proj_lit_to_ctor(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match &e.0.kind {
        ExprKind::Lit(Literal::StrVal(s)) => {
            if str_lit_supported(fe) {
                let c = str_lit_to_constructor(s);
                core_c::whnf(mode, fuel, st, fe, depth, &c)
            } else {
                Ok(expr::dup(e))
            }
        }
        _ => Ok(expr::dup(e)),
    }
}

// ---------------------------------------------------------------------------
// The install-time rule bits (`Core.lean:1494-1621`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1488-1503 recRuleKOf
/// **The K bit at install** (`RecRule.k`): the rule's constructor has no
/// fields and belongs to an inductive stored with the K capability.  Together
/// with a singleton rule list this is the official kernel's
/// `recursor_val::is_k()`.
pub fn rec_rule_k_of(fe: &FEnv, ctor: &Name) -> bool {
    match ctor_probe(fe, ctor) {
        Some((cvj, _, cn_f)) => {
            let res = expr_ops::pi_result(&cvj.ty);
            let head = expr_ops::get_app_fn(&res);
            match &head.0.kind {
                ExprKind::Const(t, _) => match ind_probe(fe, t) {
                    Some((_, caps)) => caps.rule_k && cn_f == 0,
                    None => false,
                },
                _ => false,
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1505-1531 recRuleEtaOf
/// **The η-rescue bit at install** (`RecRule.eta`): the rule's constructor is
/// the η constructor of a stored η-capable inductive, carries that
/// inductive's own level parameters, and the recursor is not itself a
/// projection function (whose rescue would reduce to its own reduct and
/// loop).
pub fn rec_rule_eta_of(fe: &FEnv, rec_name: &Name, ctor: &Name) -> bool {
    match ctor_probe(fe, ctor) {
        Some((cvj, _, _)) => {
            let res = expr_ops::pi_result(&cvj.ty);
            let head = expr_ops::get_app_fn(&res);
            match &head.0.kind {
                ExprKind::Const(t, _) => match ind_probe(fe, t) {
                    Some((cvt, caps)) => {
                        if !caps.eta {
                            false
                        } else if !name::beq(&caps.eta_ctor, ctor) {
                            false
                        } else if level::name_is_proj_fn_shape(rec_name) {
                            false
                        } else {
                            prop_when::names_beq(&cvj.level_params, &cvt.level_params)
                        }
                    }
                    None => false,
                },
                _ => false,
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1533-1543 recRuleBits
/// **Stamp a rule's two rescue bits at install** — the one place the K and
/// η-rescue conditions are decided.  The cited `{ rl with … }` takes the
/// record by value and rewrites the two fields.
pub fn rec_rule_bits(fe: &FEnv, rec_name: &Name, rl: RecRule) -> RecRule {
    let k = rec_rule_k_of(fe, &rl.ctor);
    let eta = rec_rule_eta_of(fe, rec_name, &rl.ctor);
    let mut rl = rl;
    rl.k = k;
    rl.eta = eta;
    rl
}

/// con-leche: ConLeche/Kernel/Core.lean:1582-1594 projFnRule
/// The stored rule of a projection function, with its bits stamped by
/// `rec_rule_bits`.  The cited record literal leaves `k`/`eta` at their
/// `false` defaults, which `rec_rule_bits` then overwrites.
pub fn proj_fn_rule(
    fe: &FEnv,
    t: &Name,
    ctor_name: &Name,
    pty: &Expr,
    n_p: u64,
    n_f: u64,
    i: u64,
    rhs_a: Expr,
) -> RecRule {
    let fire = if expr_ops::rec_rule_plain(pty, n_p, n_p, n_p) {
        RecRuleFire::Plain
    } else {
        RecRuleFire::Inert
    };
    let rl = RecRule {
        ctor: name::dup(ctor_name),
        nfields: n_f,
        ctor_params: n_p,
        fire,
        rhs: rhs_a,
        k: false,
        eta: false,
        params_blind: false,
    };
    rec_rule_bits(fe, &env::proj_fn_name(t, i), rl)
}

/// con-leche: ConLeche/Kernel/Core.lean:1612-1619 recRuleK
/// Is a recursor K-flagged?  The stored bit of its single rule.
pub fn rec_rule_k(rules: &Vec<RecRule>) -> bool {
    if rules.len() == 1 {
        rules[0].k
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1621-1658 prepareMajor
/// The major premise's preparation before a rule fires, in the official
/// kernel's order: at a K-flagged recursor the K rescue runs on the **raw**
/// major (it reads only the major's *type*) and only then is the major
/// head-normalized and its literal converted; elsewhere the major is
/// head-normalized first, its literal converted, and the structure-eta rescue
/// tried on the reduct.
///
/// The order matters (the Mathlib `decide`-over-`Rat` frontier): with the
/// whnf *first*, an `Eq.rec` whose major is a theorem application
/// delta-unfolds the proofs and iota-grinds a `Nat.brecOn` tower unarily.
pub fn prepare_major(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rules: &Vec<RecRule>,
    major: &Expr,
) -> CheckM<Expr> {
    if rec_rule_k(rules) {
        match major_to_ctor(mode, fuel, st, fe, depth, rules, major) {
            Err(err) => Err(err),
            Ok(major_k) => match core_c::whnf(mode, fuel, st, fe, depth, &major_k) {
                Err(err) => Err(err),
                Ok(major0) => lit_major_to_ctor(mode, fuel, st, fe, depth, &major0),
            },
        }
    } else {
        match core_c::whnf(mode, fuel, st, fe, depth, major) {
            Err(err) => Err(err),
            Ok(major0) => match lit_major_to_ctor(mode, fuel, st, fe, depth, &major0) {
                Err(err) => Err(err),
                Ok(major1) => major_to_ctor(mode, fuel, st, fe, depth, rules, &major1),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The `cvjLps.map (fun p => Level.subst lps us (.param p))` of the `.plain`
/// arm, as an index recursion (§3.4 forbids closures).
pub fn params_subst(lps: &Vec<Name>, us: &Vec<Level>, ps: &Vec<Name>) -> Vec<Level> {
    params_subst_from(lps, us, ps, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The index recursion behind `params_subst`.
pub fn params_subst_from(
    lps: &Vec<Name>,
    us: &Vec<Level>,
    ps: &Vec<Name>,
    i: usize,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= ps.len() {
        out
    } else {
        let mut out = out;
        out.push(level::subst(
            lps,
            us,
            &level::param(name::dup(&ps[i])),
        ));
        params_subst_from(lps, us, ps, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The `pins.map (fun p => Expr.instSpine (args.take rP) (rP - 1)
/// (p.instantiateLevelParams lps us))` of the `.nested` arm, as an index
/// recursion.  `rP - 1` is Lean's truncated `Nat` subtraction, hence
/// `expr_ops::sub_nat`.
pub fn pins_subst_from(
    lps: &Vec<Name>,
    us: &Vec<Level>,
    pins: &Vec<Expr>,
    pargs: &Vec<Expr>,
    r_p: u64,
    i: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if i >= pins.len() {
        out
    } else {
        let mut out = out;
        let p = expr_ops::instantiate_level_params(lps, us, &pins[i]);
        out.push(expr_ops::inst_spine(
            pargs,
            expr_ops::sub_nat(r_p, 1),
            &p,
        ));
        pins_subst_from(lps, us, pins, pargs, r_p, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The level and constructor-parameter comparands a firing rule's checks
/// compare the major's constructor levels and parameters against: for a
/// canonical (`.plain`) rule the constructor's levels link to the recursor's
/// by name and its parameters are the recursor's leading arguments; for a
/// certified nested rule both are the stored major-domain instantiations.
/// Junk for `.inert` rules — `iota_rec` declines before reading it.
pub fn rec_fire_comparands(
    rl: &RecRule,
    lps: &Vec<Name>,
    us: &Vec<Level>,
    cvj_lps: &Vec<Name>,
    args: &Vec<Expr>,
    r_p: u64,
) -> (Vec<Level>, Vec<Expr>) {
    match &rl.fire {
        RecRuleFire::Nested(lvls, pins) => {
            let pargs = expr_ops::take_exprs(args, r_p as usize);
            (
                state_c::subst_level_trees(lps, us, lvls),
                pins_subst_from(lps, us, pins, &pargs, r_p, 0, Vec::new()),
            )
        }
        _ => (
            params_subst(lps, us, cvj_lps),
            expr_ops::take_exprs(args, rl.ctor_params as usize),
        ),
    }
}

// ---------------------------------------------------------------------------
// Iota (`Core.lean:1695-1800`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// `args.getD i (.bvar 0)` — Lean's out-of-range default is
/// `Inhabited Expr`'s `.bvar 0` (`env::default_expr`).
pub fn get_d_expr(args: &Vec<Expr>, i: u64) -> Expr {
    if i < args.len() as u64 {
        expr::dup(&args[i as usize])
    } else {
        env::default_expr()
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
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

/// con-leche: ConLeche/Kernel/Env.lean:203-247 RecRuleFire
/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The cited `rl.fire = .inert` test; Rust has no equality on the enum
/// (§3.4 keeps `derive` off the core types), so it is a one-arm match.
pub fn fire_is_inert(f: &RecRuleFire) -> bool {
    match f {
        RecRuleFire::Inert => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// One iota step: the expression is a stored recursor applied to exactly its
/// telescope, the major premise whnfs to a fully applied constructor with a
/// matching rule, and the spine is certified against the recursor's own
/// (pinned, annotated) type.  Over-application is handled by the outer app
/// recursion.
///
/// This function is the cited head/arity dispatch; `iota_rec_rule` matches
/// the prepared major against a rule and `iota_rec_checks` runs the cascade.
pub fn iota_rec(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Option<Expr>> {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(c, us) => match rec_probe(fe, c) {
            Some((cv, m_i, r_p, rules)) => {
                let args = expr_ops::get_app_args(e);
                if (args.len() as u64) == m_i + 1 && us.len() == cv.level_params.len() {
                    let raw = get_d_expr(&args, m_i);
                    match prepare_major(mode, fuel, st, fe, depth, &rules, &raw) {
                        Err(err) => Err(err),
                        Ok(major) => iota_rec_rule(
                            mode, fuel, st, fe, depth, &cv, m_i, r_p, &rules, us, &args,
                            &major,
                        ),
                    }
                } else {
                    Ok(None)
                }
            }
            None => Ok(None),
        },
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The prepared major's head must be a stored constructor with a matching
/// rule at a matching spine length; a matched **inert** rule is a positive
/// detection of an unsupported feature and declines here (staying silently
/// stuck would surface as a spurious *reject* downstream).
pub fn iota_rec_rule(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    cv: &ConstantVal,
    m_i: u64,
    r_p: u64,
    rules: &Vec<RecRule>,
    us: &Vec<Level>,
    args: &Vec<Expr>,
    major: &Expr,
) -> CheckM<Option<Expr>> {
    const M: [u32; 52] = [
        105, 111, 116, 97, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 111, 118, 101,
        114, 32, 97, 32, 110, 101, 115, 116, 101, 100, 32, 97, 117, 120, 105, 108, 105, 97,
        114, 121, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 117, 108, 101,
    ];
    let fj = expr_ops::get_app_fn(major);
    match &fj.0.kind {
        ExprKind::Const(cj, usj) => match ctor_probe(fe, cj) {
            Some((cvj, _, _)) => match rules_find(rules, cj, 0) {
                Some(k) => {
                    let rl = env::rec_rule_dup(&rules[k]);
                    let margs = expr_ops::get_app_args(major);
                    if (margs.len() as u64) != rl.ctor_params + rl.nfields {
                        Ok(None)
                    } else if fire_is_inert(&rl.fire) {
                        Err(core_types::not_implemented(core_types::code_points(&M)))
                    } else {
                        iota_rec_checks(
                            mode, fuel, st, fe, depth, cv, &cvj, m_i, r_p, &rl, us, usj,
                            args, &margs, major,
                        )
                    }
                }
                None => Ok(None),
            },
            None => Ok(None),
        },
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The firing cascade, in the cited order: the constructor's levels against
/// the rule's comparands, the parameter comparison (unless the rule is
/// `paramsBlind`), the two *licensed* telescope runs (the redex is a subterm
/// of the subject, so the mode's β gate licenses the `.never` skip), the
/// canonical-index comparison, and then the rule's rhs applied to the
/// non-index prefix and the constructor's fields.
pub fn iota_rec_checks(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    cv: &ConstantVal,
    cvj: &ConstantVal,
    m_i: u64,
    r_p: u64,
    rl: &RecRule,
    us: &Vec<Level>,
    usj: &Vec<Level>,
    args: &Vec<Expr>,
    margs: &Vec<Expr>,
    major: &Expr,
) -> CheckM<Option<Expr>> {
    let comp = rec_fire_comparands(rl, &cv.level_params, us, &cvj.level_params, args, r_p);
    match lift_fueled(level::is_equiv_list(usj, &comp.0)) {
        Err(err) => Err(err),
        Ok(false) => Ok(None),
        Ok(true) => {
            let params = expr_ops::take_exprs(margs, rl.ctor_params as usize);
            let pcmp = if env::rec_rule_compare_params(rl) {
                def_eq_list(mode, fuel, st, fe, depth, &params, &comp.1)
            } else {
                Ok(true)
            };
            match pcmp {
                Err(err) => Err(err),
                Ok(false) => Ok(None),
                Ok(true) => iota_rec_telescopes(
                    mode, fuel, st, fe, depth, cv, cvj, m_i, r_p, rl, us, usj, args, margs,
                    major,
                ),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The two licensed telescope certificates, the index comparison and the
/// reduct.
pub fn iota_rec_telescopes(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    cv: &ConstantVal,
    cvj: &ConstantVal,
    m_i: u64,
    r_p: u64,
    rl: &RecRule,
    us: &Vec<Level>,
    usj: &Vec<Level>,
    args: &Vec<Expr>,
    margs: &Vec<Expr>,
    major: &Expr,
) -> CheckM<Option<Expr>> {
    let rty = expr_ops::instantiate_level_params(&cv.level_params, us, &cv.ty);
    let cty = expr_ops::instantiate_level_params(&cvj.level_params, usj, &cvj.ty);
    let pre = expr_ops::take_exprs(args, m_i as usize);
    let rspine = append_exprs(env::exprs_copy(&pre), &expr_singleton(major));
    let lic = env::beta_gate(mode);
    match iota_certs(mode, fuel, st, fe, depth, lic, &rty, &rspine) {
        Err(err) => Err(err),
        Ok(false) => Ok(None),
        Ok(true) => match iota_certs(mode, fuel, st, fe, depth, lic, &cty, margs) {
            Err(err) => Err(err),
            Ok(false) => Ok(None),
            Ok(true) => {
                let idx = drop_exprs(&pre, r_p as usize);
                match iota_index_ok(
                    mode, fuel, st, fe, depth, m_i, r_p, rl.ctor_params, &cty, margs, &idx,
                ) {
                    Err(err) => Err(err),
                    Ok(false) => Ok(None),
                    Ok(true) => {
                        let rhs = expr_ops::instantiate_level_params(
                            &cv.level_params,
                            us,
                            &rl.rhs,
                        );
                        let fields = drop_exprs(margs, rl.ctor_params as usize);
                        let spine = append_exprs(
                            expr_ops::take_exprs(args, r_p as usize),
                            &fields,
                        );
                        Ok(Some(expr_ops::mk_app_n(rhs, &spine)))
                    }
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Projections (`Core.lean:1803-1888`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1797-1806 ProjEntry.typeAt
/// **The type of a `.proj` node at a tower-backed entry**: the stored body
/// level-instantiated at the subject type's levels, with the subject type's
/// arguments and the subject substituted for its `numParams + 1` loose
/// variables in ONE traversal (`bvar 0` is the subject, `bvar (numParams -
/// k)` parameter `k`).
///
/// Deviation: the cited `pe :: targs.reverse` is built as a `Vec` (the
/// reversal copies the spine; Lean's `List.reverse` allocates too).
pub fn proj_entry_type_at(
    entry: &ProjEntry,
    us: &Vec<Level>,
    targs: &Vec<Expr>,
    pe: &Expr,
) -> Expr {
    let body = expr_ops::instantiate_level_params(&entry.level_params, us, &entry.body);
    let mut vs: Vec<Expr> = Vec::new();
    vs.push(expr::dup(pe));
    let vs = rev_append_exprs(vs, targs, targs.len());
    expr_ops::instantiate_list_fast(&body, &vs, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:1797-1806 ProjEntry.typeAt
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

/// con-leche: ConLeche/Kernel/Core.lean:1808-1843 projCert
/// **The structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)`
/// fires only after its constructor spine is certified against `C`'s stored
/// type at the redex's own levels.  The spine is a subterm of the subject, so
/// the certificate is *licensed* like the ι slot's.
pub fn proj_cert(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    lic: bool,
    c: &Name,
    us: &Vec<Level>,
    args: &Vec<Expr>,
) -> CheckM<bool> {
    match ctor_probe(fe, c) {
        Some((cvc, _, _)) => {
            let cty = expr_ops::instantiate_level_params(&cvc.level_params, us, &cvc.ty);
            iota_certs(mode, fuel, st, fe, depth, lic, &cty, args)
        }
        None => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1845-1857 projCertAt
/// **The fire certificate as the mode runs it**: the P core certifies the
/// constructor spine; the parity core is the official kernel's
/// (`reduce_proj` reduces every constructor redex with no certificate), so at
/// `verified = false` the rule fires unconditionally.
pub fn proj_cert_at(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    verified: bool,
    lic: bool,
    c: &Name,
    us: &Vec<Level>,
    args: &Vec<Expr>,
) -> CheckM<bool> {
    if verified {
        proj_cert(mode, fuel, st, fe, depth, lic, c, us, args)
    } else {
        Ok(true)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1859-1891 betaGateFires
/// **THE β SITE'S GATE**: at `mode.betaGate` a λ-binder whose *validated*
/// annotation datum is `.never` licenses skipping the certificate.  Mode and
/// datum only — no expression is read and no computation is run, which is
/// what makes the gate decidable before the certificate would have started.
pub fn beta_gate_fires(mode: &CheckMode, pw: &PropWhen) -> bool {
    env::beta_gate(mode) && prop_when::is_never(pw)
}

// ---------------------------------------------------------------------------
// `whnfCore` (`Core.lean:1898-1990`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// The head-normalization body: beta (with the per-redex argument
/// certificate), iota (with the stuck-major machinery) and the structural
/// projection rule — but **no delta**; unfolding happens in the `whnf` loop.
/// Values (sorts, binders, constants, literals) return themselves.
///
/// Deviations: the identity arms hand back an `Rc` bump (`expr::dup`) where
/// the Lean rebuilds the node — the same value, and it is what keeps the DAG
/// shared (task #13's pattern 2); and the `.letE`/`.bvar` arms are the cited
/// throws, whose messages are `const` code points.
pub fn whnf_core_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_LET: [u32; 42] = [
        119, 104, 110, 102, 67, 111, 114, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105, 110,
        32, 97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112, 114,
        101, 115, 115, 105, 111, 110,
    ];
    const M_BVAR: [u32; 34] = [
        119, 104, 110, 102, 32, 98, 101, 121, 111, 110, 100, 32, 116, 104, 101, 32, 115, 117,
        112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109, 101, 110, 116,
    ];
    match &e.0.kind {
        ExprKind::Sort(_) => Ok(expr::dup(e)),
        ExprKind::Fvar(_, _) => Ok(expr::dup(e)),
        ExprKind::ForallE(_, _, _) => Ok(expr::dup(e)),
        ExprKind::Lam(_, _, _) => Ok(expr::dup(e)),
        ExprKind::Const(_, _) => Ok(expr::dup(e)),
        ExprKind::Lit(_) => Ok(expr::dup(e)),
        ExprKind::App(f, a) => {
            let a = expr::dup(a);
            match core_c::whnf_core(mode, fuel, st, fe, d, f) {
                Err(err) => Err(err),
                Ok(fr) => whnf_core_app(mode, fuel, st, fe, d, &fr, &a),
            }
        }
        ExprKind::Proj(sn, i, pe) => {
            let sn = name::dup(sn);
            let i = *i;
            match core_c::whnf(mode, fuel, st, fe, d, pe) {
                Err(err) => Err(err),
                Ok(w) => match proj_lit_to_ctor(mode, fuel, st, fe, d, &w) {
                    Err(err) => Err(err),
                    Ok(e2) => whnf_core_proj(mode, fuel, st, fe, d, &sn, i, &e2),
                },
            }
        }
        ExprKind::LetE(_, _, _) => {
            Err(core_types::internal(core_types::code_points(&M_LET)))
        }
        ExprKind::Bvar(_) => Err(core_types::not_implemented(core_types::code_points(
            &M_BVAR,
        ))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// The `.app` arm's continuation, on the head-normalized function part: a λ
/// head is a β redex, whose argument is certified against the domain before
/// reducing (unconditionally since con-leche's task #100 de-gating, except at
/// the task-#161 β gate, which reads a *validated* annotation); any other
/// head goes to `iota_rec`.
pub fn whnf_core_app(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    fr: &Expr,
    a: &Expr,
) -> CheckM<Expr> {
    match &fr.0.kind {
        ExprKind::Lam(ty, body, mb) => {
            let ty = expr::dup(ty);
            let red = expr_ops::instantiate1(body, a, 0);
            if beta_gate_fires(mode, &mb.pw) {
                core_c::whnf_core(mode, fuel, st, fe, d, &red)
            } else {
                match core_c::infer_io(mode, fuel, st, fe, d, a) {
                    Err(err) => Err(err),
                    Ok(ta) => match core_c::defeq(mode, fuel, st, fe, d, &ta, &ty) {
                        Err(err) => Err(err),
                        Ok(true) => core_c::whnf_core(mode, fuel, st, fe, d, &red),
                        Ok(false) => {
                            Ok(expr::app(expr::dup(fr), expr::dup(a)))
                        }
                    },
                }
            }
        }
        _ => {
            let ap = expr::app(expr::dup(fr), expr::dup(a));
            match iota_rec(mode, fuel, st, fe, d, &ap) {
                Err(err) => Err(err),
                Ok(Some(e2)) => core_c::whnf_core(mode, fuel, st, fe, d, &e2),
                Ok(None) => Ok(ap),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// The `.proj` arm's continuation, on the reduced (and string-literal
/// expanded) scrutinee: the structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`,
/// driven by the projection table (never by basis names), behind the
/// table's own counts and its possibly-`Prop` level guard.
pub fn whnf_core_proj(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    sn: &Name,
    i: u64,
    e2: &Expr,
) -> CheckM<Expr> {
    match fenv::find_proj(fe, sn, i) {
        Some(entry) => {
            let f = expr_ops::get_app_fn(e2);
            match &f.0.kind {
                ExprKind::Const(c, us) => {
                    let args = expr_ops::get_app_args(e2);
                    if proj_fire_shape_ok(&entry, c, i, us, &args) {
                        let arg = get_d_expr(&args, entry.num_params + i);
                        match proj_cert_at(
                            mode,
                            fuel,
                            st,
                            fe,
                            d,
                            env::verified_checks(mode),
                            env::beta_gate(mode),
                            c,
                            us,
                            &args,
                        ) {
                            Err(err) => Err(err),
                            Ok(true) => core_c::whnf_core(mode, fuel, st, fe, d, &arg),
                            Ok(false) => {
                                Ok(expr::proj(name::dup(sn), i, expr::dup(e2)))
                            }
                        }
                    } else {
                        Ok(expr::proj(name::dup(sn), i, expr::dup(e2)))
                    }
                }
                _ => Ok(expr::proj(name::dup(sn), i, expr::dup(e2))),
            }
        }
        None => Ok(expr::proj(name::dup(sn), i, expr::dup(e2))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// The cited five-conjunct fire guard of the `.proj` arm, as an `if` nest:
/// the head is the entry's constructor, the field index is in range, the
/// spine is exactly parameters plus fields, the level count matches, and the
/// possibly-`Prop` guard passes.
pub fn proj_fire_shape_ok(
    entry: &ProjEntry,
    c: &Name,
    i: u64,
    us: &Vec<Level>,
    args: &Vec<Expr>,
) -> bool {
    if !name::beq(c, &entry.ctor) {
        false
    } else if i >= entry.num_fields {
        false
    } else if (args.len() as u64) != entry.num_params + entry.num_fields {
        false
    } else if us.len() != entry.level_params.len() {
        false
    } else {
        proj_entry_fire_ok(entry, us)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1984-1992 whnfCoreLoopFuel
/// Step budget of the `whnfCore` head-normalization loop (con-leche's task
/// #106).  Nothing in this module reads it — the *interned* `whnfCoreLoopI`
/// does (`Cached/CoreC.lean`, task #19) — but it is ported so the provenance
/// gate stays in step with its source.
pub fn whnf_core_loop_fuel() -> u64 {
    1000000
}

/// con-leche: ConLeche/Kernel/Core.lean:1994-2001 whnfLoopFuel
/// Step budget of the `whnf` reduction loop (lean4lean's `FuelConfig.whnf`,
/// same value).  Literal-acceleration and delta steps are *iteration*, not
/// recursion.
pub fn whnf_loop_fuel() -> u64 {
    100000
}

/// con-leche: ConLeche/Kernel/Core.lean:2003-2018 whnfStep
/// One iteration of the reduction loop (the official kernel's `whnf` body):
/// head-normalize, try literal acceleration, unfold one definition — and hand
/// the reduct to the loop's continuation.
///
/// Deviation: the Lean abstracts the continuation as `k : Expr → m Expr` so
/// that every lemma about the body is proven once; §3.4 forbids closures, so
/// the port takes the continuation's *step budget* `n` instead and spells `k
/// x` as `whnf_loop(…, n, x)` — which is exactly what `whnfLoop`'s
/// `whnfStep r env depth (whnfLoop r env depth n)` passes.  Both functions
/// survive.
pub fn whnf_step(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match core_c::whnf_core(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(e1) => match reduce_nat(mode, fuel, st, fe, depth, &e1) {
            Err(err) => Err(err),
            Ok(Some(e2)) => whnf_loop(mode, fuel, st, fe, depth, n, &e2),
            Ok(None) => match unfold_definition(fe, &e1) {
                Some(e2) => whnf_loop(mode, fuel, st, fe, depth, n, &e2),
                None => Ok(e1),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2020-2025 whnfLoop
/// The reduction loop: iterate `whnf_step` on its own step budget, so the
/// whole chain costs one knot level however many steps it takes.
pub fn whnf_loop(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 25] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102, 32, 108, 111, 111, 112,
    ];
    if n == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        whnf_step(mode, fuel, st, fe, depth, n - 1, e)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2027-2029 whnfBody
/// The reduction loop's body: run `whnf_loop` at its own step budget.
pub fn whnf_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    whnf_loop(mode, fuel, st, fe, depth, whnf_loop_fuel(), e)
}

/// con-leche: ConLeche/Kernel/Core.lean:2031-2037 ensureSort
/// Ensure `e` (the type of some expression) is a sort, returning its level.
pub fn ensure_sort(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Level> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    match core_c::whnf(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(w) => match &w.0.kind {
            ExprKind::Sort(u) => Ok(level::dup(u)),
            _ => Err(core_types::invalid(core_types::code_points(&M))),
        },
    }
}

// ---------------------------------------------------------------------------
// Inference (`Core.lean:2042-2337`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The `.const` arm, which is byte-identical in the two bodies and calls no
/// entry point: the constant is stored, is not a projection table, and
/// carries the right number of universe levels.
pub fn infer_const(fe: &FEnv, n: &Name, us: &Vec<Level>) -> CheckM<Expr> {
    const M_UNKNOWN: [u32; 16] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116,
    ];
    const M_TOWER: [u32; 41] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 101,
        110, 116, 114, 121, 32, 117, 115, 101, 100, 32, 97, 115, 32, 97, 32, 99, 111, 110,
        115, 116, 97, 110, 116,
    ];
    const M_LEVELS: [u32; 35] = [
        105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
        102, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115,
    ];
    match fenv::find(fe, n) {
        None => Err(core_types::invalid(core_types::code_points(&M_UNKNOWN))),
        Some(ci) => {
            if env::is_tower_entry(ci) {
                Err(core_types::invalid(core_types::code_points(&M_TOWER)))
            } else {
                let cv = env::to_constant_val(ci);
                if us.len() != cv.level_params.len() {
                    Err(core_types::invalid(core_types::code_points(&M_LEVELS)))
                } else {
                    Ok(expr_ops::instantiate_level_params(
                        &cv.level_params,
                        us,
                        &cv.ty,
                    ))
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// A `Nat` literal types as `Nat`, and without the basis declarations it is
/// *invalid* (not merely unimplemented).
pub fn infer_lit_nat(fe: &FEnv) -> CheckM<Expr> {
    const M: [u32; 46] = [
        78, 97, 116, 32, 108, 105, 116, 101, 114, 97, 108, 32, 119, 105, 116, 104, 111, 117,
        116, 32, 116, 104, 101, 32, 78, 97, 116, 32, 98, 97, 115, 105, 115, 32, 100, 101, 99,
        108, 97, 114, 97, 116, 105, 111, 110, 115,
    ];
    if nat_lit_supported(fe) {
        Ok(expr::mk_const(basis_names::nat_name(), Vec::new()))
    } else {
        Err(core_types::invalid(core_types::code_points(&M)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// A string literal types as `String`; without the pinned support
/// declarations this is a positively detected unsupported feature — decline.
pub fn infer_lit_str(fe: &FEnv) -> CheckM<Expr> {
    const M: [u32; 54] = [
        115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 98, 101,
        102, 111, 114, 101, 32, 116, 104, 101, 32, 83, 116, 114, 105, 110, 103, 32, 115, 117,
        112, 112, 111, 114, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115,
    ];
    if str_lit_supported(fe) {
        Ok(expr::mk_const(basis_names::string_name(), Vec::new()))
    } else {
        Err(core_types::not_implemented(core_types::code_points(&M)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The `.fvar` arm's scope check at the leaf of a traversal that happens
/// anyway (`O(1)`, never a fresh walk): a free variable must refer to an
/// enclosing opened binder.  On raw (closed) input at depth 0 this rejects
/// any `fvar` outright.
pub fn infer_fvar(idx: u64, ty: &Expr, depth: u64) -> CheckM<Expr> {
    const M: [u32; 26] = [
        102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 111, 117, 116, 32,
        111, 102, 32, 115, 99, 111, 112, 101,
    ];
    if idx < depth {
        Ok(expr::dup(ty))
    } else {
        Err(core_types::invalid(core_types::code_points(&M)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The cited propositional-structure restriction of the two `.proj` arms
/// (official `infer_proj`'s task #175 W4c/O4 test): at a `Prop`-declared
/// structure the field must be a proposition at this instantiation.  The two
/// tests the Lean inlines here are `ProjEntry.fireOk`'s body verbatim, so the
/// port calls that function; the throw fires exactly at `fireOk = false`.
pub fn proj_type_at_checked(
    entry: &ProjEntry,
    sn: &Name,
    t: &Name,
    us: &Vec<Level>,
    targs: &Vec<Expr>,
    pe: &Expr,
) -> CheckM<Expr> {
    const M_NOENTRY: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 119, 105, 116, 104, 111, 117,
        116, 32, 97, 32, 110, 97, 116, 105, 118, 101, 32, 101, 110, 116, 114, 121,
    ];
    const M_PROP: [u32; 63] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 102, 114, 111, 109, 32, 97, 32,
        112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 97, 108, 32, 115, 116, 114,
        117, 99, 116, 117, 114, 101, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 32, 112,
        114, 111, 112, 111, 115, 105, 116, 105, 111, 110,
    ];
    if !name::beq(t, sn)
        || (targs.len() as u64) != entry.num_params
        || us.len() != entry.level_params.len()
    {
        Err(core_types::not_implemented(core_types::code_points(
            &M_NOENTRY,
        )))
    } else if !proj_entry_fire_ok(entry, us) {
        Err(core_types::invalid(core_types::code_points(&M_PROP)))
    } else {
        Ok(proj_entry_type_at(entry, us, targs, pe))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The inference body — **infer-only**: the application rule's argument check
/// ran once, in the annotation pass, and is trusted here (so speculative
/// inference inside reduction cannot reject).
pub fn infer_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_LET: [u32; 43] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105,
        110, 32, 97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112,
        114, 101, 115, 115, 105, 111, 110,
    ];
    const M_BVAR: [u32; 39] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 32, 98, 101, 121, 111, 110, 100, 32, 116,
        104, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109,
        101, 110, 116,
    ];
    match &e.0.kind {
        ExprKind::Sort(u) => Ok(expr::sort(level::succ(level::dup(u)))),
        ExprKind::Fvar(idx, ty) => infer_fvar(*idx, ty, depth),
        ExprKind::Const(n, us) => infer_const(fe, n, us),
        ExprKind::Lit(Literal::NatVal(_)) => infer_lit_nat(fe),
        ExprKind::Lit(Literal::StrVal(_)) => infer_lit_str(fe),
        ExprKind::ForallE(ty, body, mb) => {
            infer_forall(mode, fuel, st, fe, depth, ty, body, mb, false)
        }
        ExprKind::Lam(ty, body, mb) => infer_lam(mode, fuel, st, fe, depth, ty, body, mb),
        ExprKind::App(f, a) => infer_app(mode, fuel, st, fe, depth, f, a),
        ExprKind::Proj(sn, i, pe) => infer_proj(mode, fuel, st, fe, depth, sn, *i, pe),
        ExprKind::LetE(_, _, _) => {
            Err(core_types::internal(core_types::code_points(&M_LET)))
        }
        ExprKind::Bvar(_) => Err(core_types::not_implemented(core_types::code_points(
            &M_BVAR,
        ))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The ∀-formation rule, official-kernel style: the codomain sort is
/// *inferred* from the opened body, and at the verified modes the node's
/// prop-ness annotation is VALIDATED against it (the datum is canonical, so
/// `==` decides zero-ness agreement, and a mismatch is a decline, never a
/// reject).
///
/// The two cited clauses are byte-identical apart from the grade of the two
/// recursive inferences, so they are one function with an `io` flag: at `io =
/// true` the recursion is `core_c::infer_io` (the knot's io-grade view), at
/// `io = false` it is `core_c::infer`.
pub fn infer_forall(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
    io: bool,
) -> CheckM<Expr> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    match infer_at(mode, fuel, st, fe, depth, ty, io) {
        Err(err) => Err(err),
        Ok(tty) => match core_c::whnf(mode, fuel, st, fe, depth, &tty) {
            Err(err) => Err(err),
            Ok(w) => match &w.0.kind {
                ExprKind::Sort(u) => {
                    let u = level::dup(u);
                    let v = expr::fvar(depth, expr::dup(ty));
                    let opened = expr_ops::instantiate1(body, &v, 0);
                    match infer_at(mode, fuel, st, fe, depth + 1, &opened, io) {
                        Err(err) => Err(err),
                        Ok(bt) => {
                            match ensure_sort(mode, fuel, st, fe, depth + 1, &bt) {
                                Err(err) => Err(err),
                                Ok(vv) => infer_forall_check(mode, u, vv, mb),
                            }
                        }
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The ∀ clause's annotation validation and its result `.sort (.imax u v)`.
pub fn infer_forall_check(
    mode: &CheckMode,
    u: Level,
    v: Level,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    const M: [u32; 37] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 102, 111, 114, 97, 108, 108, 45, 99, 111, 100, 41,
    ];
    if env::verified_checks(mode) && !prop_when::beq(&level::zeroness_of(&v), &mb.pw) {
        Err(core_types::not_implemented(core_types::code_points(&M)))
    } else {
        Ok(expr::sort(level::imax(u, v)))
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:61-87 CoreFns
/// The knot slot a body's `r.infer` call resolves to: the full-grade `infer`
/// wrapper in `inferBody`, the io-grade one in `inferBodyIO` (whose knot is
/// `CoreFns.ioView`, `Core.lean:94-95`).  The two bodies' shared clauses
/// carry the flag rather than being written twice, so this is where the
/// `ioView` substitution happens in the port.
pub fn infer_at(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
    io: bool,
) -> CheckM<Expr> {
    if io {
        core_c::infer_io(mode, fuel, st, fe, depth, e)
    } else {
        core_c::infer(mode, fuel, st, fe, depth, e)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The λ rule at the full grade: the domain must be a type (as in the ∀
/// rule), the body is inferred at the opened binder, and at the verified
/// modes the *codomain* sort is validated — by datum equality with the inner
/// neighbour along a λ chain (`lamPw`), by one leaf computation at the
/// innermost binder.
pub fn infer_lam(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    match core_c::infer(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(tty) => match core_c::whnf(mode, fuel, st, fe, depth, &tty) {
            Err(err) => Err(err),
            Ok(w) => {
                if is_sort(&w) {
                    infer_lam_after_dom(mode, fuel, st, fe, depth, ty, body, mb, false)
                } else {
                    Err(core_types::invalid(core_types::code_points(&M)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The λ clause past the domain-sort run (which the io body skips —
/// official's `infer_lambda` skips it at `infer_only`): the body's type, the
/// codomain validation, and the result `∀ ty (bt.abstract1 depth) mb`.  One
/// function for the two bodies, with the grade as a flag (`infer_at`).
pub fn infer_lam_after_dom(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
    io: bool,
) -> CheckM<Expr> {
    let v = expr::fvar(depth, expr::dup(ty));
    let opened = expr_ops::instantiate1(body, &v, 0);
    match infer_at(mode, fuel, st, fe, depth + 1, &opened, io) {
        Err(err) => Err(err),
        Ok(bt) => {
            let chk = if env::verified_checks(mode) {
                infer_lam_cod(mode, fuel, st, fe, depth, body, mb, &bt)
            } else {
                Ok(())
            };
            match chk {
                Err(err) => Err(err),
                Ok(()) => Ok(expr::forall_e(
                    expr::dup(ty),
                    expr_ops::abstract1(&bt, depth, 0),
                    expr::binder_meta_dup(mb),
                )),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The codomain-sort validation of the λ clause: **the chain rule** at an
/// outer binder (an outer λ's codomain is the inner λ's own ∀-type, whose
/// sort's zero-ness is the inner codomain's — datum equality with the
/// neighbour, no inference), and the leaf computation at the innermost
/// binder.
///
/// The leaf's `btt` is the io slot in *both* cited clauses — `inferBody`
/// writes `r.inferIO (depth + 1) bt` and `inferBodyIO` writes `r.infer
/// (depth + 1) bt`, which under `CoreFns.ioView` *is* the io slot — so the
/// function needs no grade flag.
pub fn infer_lam_cod(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    body: &Expr,
    mb: &BinderMeta,
    bt: &Expr,
) -> CheckM<()> {
    const M_CHAIN: [u32; 40] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 99, 104, 97,
        105, 110, 41,
    ];
    const M_LEAF: [u32; 39] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 108, 101, 97,
        102, 41,
    ];
    match expr_ops::lam_pw(body) {
        Some(pw_i) => {
            if prop_when::beq(&mb.pw, &pw_i) {
                Ok(())
            } else {
                Err(core_types::not_implemented(core_types::code_points(
                    &M_CHAIN,
                )))
            }
        }
        None => {
            match core_c::infer_io(mode, fuel, st, fe, depth + 1, bt) {
                Err(err) => Err(err),
                Ok(t) => match ensure_sort(mode, fuel, st, fe, depth + 1, &t) {
                    Err(err) => Err(err),
                    Ok(vb) => {
                        if prop_when::beq(&level::zeroness_of(&vb), &mb.pw) {
                            Ok(())
                        } else {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_LEAF,
                            )))
                        }
                    }
                },
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The application rule at the full grade: the function's type whnfs to a
/// `∀`, and the argument is re-checked against its domain
/// *unconditionally* (con-leche's task #100 de-gating).
pub fn infer_app(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    f: &Expr,
    a: &Expr,
) -> CheckM<Expr> {
    const M_MISMATCH: [u32; 25] = [
        97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 109,
        105, 115, 109, 97, 116, 99, 104,
    ];
    const M_FN: [u32; 17] = [
        102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100,
    ];
    match core_c::infer(mode, fuel, st, fe, depth, f) {
        Err(err) => Err(err),
        Ok(tf) => match core_c::whnf(mode, fuel, st, fe, depth, &tf) {
            Err(err) => Err(err),
            Ok(w) => match &w.0.kind {
                ExprKind::ForallE(ty, body, _) => {
                    let ty = expr::dup(ty);
                    let body = expr::dup(body);
                    match core_c::infer(mode, fuel, st, fe, depth, a) {
                        Err(err) => Err(err),
                        Ok(ta) => match core_c::defeq(mode, fuel, st, fe, depth, &ta, &ty) {
                            Err(err) => Err(err),
                            Ok(false) => Err(core_types::invalid(core_types::code_points(
                                &M_MISMATCH,
                            ))),
                            Ok(true) => Ok(expr_ops::instantiate1(&body, a, 0)),
                        },
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M_FN))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The `.proj` rule at the full grade: a `.proj` node is typed by its
/// projection-table entry — the stored body, level-instantiated at the
/// subject type's levels and instantiated at its arguments and the subject.
/// Only stored table entries type bare nodes.
pub fn infer_proj(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    sn: &Name,
    i: u64,
    pe: &Expr,
) -> CheckM<Expr> {
    match core_c::infer(mode, fuel, st, fe, depth, pe) {
        Err(err) => Err(err),
        Ok(tpe) => match core_c::whnf(mode, fuel, st, fe, depth, &tpe) {
            Err(err) => Err(err),
            Ok(te) => infer_proj_at(fe, sn, i, pe, &te),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The table lookup and the checks of the two `.proj` clauses, on the already
/// reduced type of the subject — byte-identical in the two bodies, so one
/// function here.
pub fn infer_proj_at(
    fe: &FEnv,
    sn: &Name,
    i: u64,
    pe: &Expr,
    te: &Expr,
) -> CheckM<Expr> {
    const M_NOENTRY: [u32; 33] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 119, 105, 116, 104, 111, 117,
        116, 32, 97, 32, 110, 97, 116, 105, 118, 101, 32, 101, 110, 116, 114, 121,
    ];
    let f = expr_ops::get_app_fn(te);
    match &f.0.kind {
        ExprKind::Const(t, us) => match fenv::find_proj(fe, t, i) {
            Some(entry) => {
                let targs = expr_ops::get_app_args(te);
                proj_type_at_checked(&entry, sn, t, us, &targs, pe)
            }
            None => Err(core_types::not_implemented(core_types::code_points(
                &M_NOENTRY,
            ))),
        },
        _ => Err(core_types::not_implemented(core_types::code_points(
            &M_NOENTRY,
        ))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// **The io inference body**: `infer_body` with two clauses changed — the λ
/// rule runs no domain-sort check (official's `infer_lambda` skips it at
/// `infer_only`) and the application rule's per-argument certificate is
/// skipped when the `∀`'s validated annotation licenses it.  Recursion is
/// through the io slot (`infer_at` with `io = true`), which is how the grade
/// propagates — official's `infer_type_core(e, infer_only)` passing
/// `infer_only` to every recursive call.
pub fn infer_body_io(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_LET: [u32; 43] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105,
        110, 32, 97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112,
        114, 101, 115, 115, 105, 111, 110,
    ];
    const M_BVAR: [u32; 39] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 32, 98, 101, 121, 111, 110, 100, 32, 116,
        104, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109,
        101, 110, 116,
    ];
    match &e.0.kind {
        ExprKind::Sort(u) => Ok(expr::sort(level::succ(level::dup(u)))),
        ExprKind::Fvar(idx, ty) => infer_fvar(*idx, ty, depth),
        ExprKind::Const(n, us) => infer_const(fe, n, us),
        ExprKind::Lit(Literal::NatVal(_)) => infer_lit_nat(fe),
        ExprKind::Lit(Literal::StrVal(_)) => infer_lit_str(fe),
        ExprKind::ForallE(ty, body, mb) => {
            infer_forall(mode, fuel, st, fe, depth, ty, body, mb, true)
        }
        ExprKind::Lam(ty, body, mb) => {
            infer_lam_after_dom(mode, fuel, st, fe, depth, ty, body, mb, true)
        }
        ExprKind::App(f, a) => infer_app_io(mode, fuel, st, fe, depth, f, a),
        ExprKind::Proj(sn, i, pe) => infer_proj_io(mode, fuel, st, fe, depth, sn, *i, pe),
        ExprKind::LetE(_, _, _) => {
            Err(core_types::internal(core_types::code_points(&M_LET)))
        }
        ExprKind::Bvar(_) => Err(core_types::not_implemented(core_types::code_points(
            &M_BVAR,
        ))),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// **THE io SITE.**  At a `∀` whose datum is `never` the certificate is dead
/// weight: the premise-form io claim derives the membership from the
/// subject's own `WellDenoted` app slot.  At a possibly-zero datum the
/// certificate runs unconditionally — the squash regime's membership is
/// model-class-wide unrecoverable, and that fence is absolute.  The read is
/// the DATUM ALONE (con-leche's licence ruling of 2026-09-06).
pub fn infer_app_io(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    f: &Expr,
    a: &Expr,
) -> CheckM<Expr> {
    const M_FN: [u32; 17] = [
        102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100,
    ];
    match core_c::infer_io(mode, fuel, st, fe, depth, f) {
        Err(err) => Err(err),
        Ok(tf) => match core_c::whnf(mode, fuel, st, fe, depth, &tf) {
            Err(err) => Err(err),
            Ok(w) => match &w.0.kind {
                ExprKind::ForallE(ty, body, mt) => {
                    let ty = expr::dup(ty);
                    let body = expr::dup(body);
                    if prop_when::is_never(&mt.pw) {
                        Ok(expr_ops::instantiate1(&body, a, 0))
                    } else {
                        infer_app_cert(mode, fuel, st, fe, depth, a, &ty, &body)
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M_FN))),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The io application clause's *certificate*, and the reduct behind it:
/// `let ta ← r.infer depth a; unless ← r.defeq depth ta ty do throw …;
/// pure (body.instantiate1 a)`.
///
/// Deviation — the module's **one Aeneas error** and its fix (task #14's
/// borrow rule again).  Written the Lean's way, the `unless mt.pw.isNever do
/// …` guard is a branch whose two arms carry different borrow contexts (one
/// binds `ta` and threads the state, the other does neither) and then *join*
/// on the shared `pure (body.instantiate1 a)`; Aeneas answered *"Could not
/// match the contexts"* both when the guard was spelled inline and when only
/// the `Bool` was factored out.  What works is the shape con-leche's own
/// `betaGateFires` docstring calls for — a **pure early return**: the skip arm
/// returns the reduct directly (`infer_app_io`) and the certifying arm is this
/// whole function, so nothing joins.  The price is that the reduct is written
/// twice; it is the same expression, and `whnf_core_app` already has the same
/// duplication for the β gate, where the Lean itself spells the early return.
pub fn infer_app_cert(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    ty: &Expr,
    body: &Expr,
) -> CheckM<Expr> {
    const M_MISMATCH: [u32; 25] = [
        97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 109,
        105, 115, 109, 97, 116, 99, 104,
    ];
    match core_c::infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match core_c::defeq(mode, fuel, st, fe, depth, &ta, ty) {
            Err(err) => Err(err),
            Ok(false) => {
                Err(core_types::invalid(core_types::code_points(&M_MISMATCH)))
            }
            Ok(true) => Ok(expr_ops::instantiate1(body, a, 0)),
        },
    }
}


/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The `.proj` rule at the io grade: as `infer_proj`, with the subject's type
/// inferred through the io slot.
pub fn infer_proj_io(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    sn: &Name,
    i: u64,
    pe: &Expr,
) -> CheckM<Expr> {
    match core_c::infer_io(mode, fuel, st, fe, depth, pe) {
        Err(err) => Err(err),
        Ok(tpe) => match core_c::whnf(mode, fuel, st, fe, depth, &tpe) {
            Err(err) => Err(err),
            Ok(te) => infer_proj_at(fe, sn, i, pe, &te),
        },
    }
}

// ---------------------------------------------------------------------------
// Definitional equality (`Core.lean:2346-2660`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:2336-2348 boolTrueShortcut
/// **The eq-true shortcut** (the divergence audit's E2): the left side is
/// fully head-normalised and the verdict is `true` iff the reduct is
/// `Bool.true`.  Only the reduction is here; the guard is `defeq_step`'s.
pub fn bool_true_shortcut(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
) -> CheckM<bool> {
    match core_c::whnf(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(w) => Ok(is_bool_true(&w)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2350-2369 defeqSpine
/// Levels-and-spine congruence for two applications of the same stored
/// constant — the lazy delta *same-head short-circuit*.  A `false` verdict is
/// never final (the caller falls back to unfolding), so an inconclusive level
/// comparison simply answers `false` here.
pub fn defeq_spine(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    let fa = expr_ops::get_app_fn(a);
    let fb = expr_ops::get_app_fn(b);
    match &fa.0.kind {
        ExprKind::Const(n, us) => match &fb.0.kind {
            ExprKind::Const(n2, us2) => {
                let args_a = expr_ops::get_app_args(a);
                let args_b = expr_ops::get_app_args(b);
                if name::beq(n, n2) && args_a.len() == args_b.len() {
                    match level::is_equiv_list(us, us2) {
                        Some(true) => {
                            def_eq_list(mode, fuel, st, fe, depth, &args_a, &args_b)
                        }
                        Some(false) => Ok(false),
                        None => Ok(false),
                    }
                } else {
                    Ok(false)
                }
            }
            _ => Ok(false),
        },
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// The definitional-equality body's one iteration: the syntactic fast path,
/// the eq-true shortcut, head normalization of both sides (**no delta** —
/// `whnfCore`), the hoisted proof irrelevance, then lazy delta, then
/// structural congruence with the stuck fallbacks.
///
/// Deviation: as in `whnf_step`, the cited continuation `k : Bool → Expr →
/// Expr → m Bool` is replaced by the loop's step budget `n` — `k pi x y` is
/// `defeq_loop(…, n, pi, x, y)`, which is exactly what `defeqLoop` passes.
/// The body's five stages are five functions, so each cited `else` arm stays
/// a tail position rather than a twenty-deep nest.
pub fn defeq_step(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    pi: bool,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    if expr::beq(a, b) {
        Ok(true)
    } else {
        let sc = if pi && is_bool_true(b) && !expr_ops::has_fvar(a) {
            bool_true_shortcut(mode, fuel, st, fe, depth, a)
        } else {
            Ok(false)
        };
        match sc {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => match core_c::whnf_core(mode, fuel, st, fe, depth, a) {
                Err(err) => Err(err),
                Ok(a2) => match core_c::whnf_core(mode, fuel, st, fe, depth, b) {
                    Err(err) => Err(err),
                    Ok(b2) => {
                        if expr::beq(&a2, &b2) {
                            Ok(true)
                        } else {
                            defeq_after_whnf(mode, fuel, st, fe, depth, n, pi, &a2, &b2)
                        }
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// The hoisted proof-irrelevance probe, run **once per `is_def_eq_core`
/// entry** (the audit's D3, hence the `pi` flag) and never on a pair
/// official's `quick_is_def_eq` decides itself (D4, hence `quick_pair`).
pub fn defeq_after_whnf(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    pi: bool,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let pir = if pi && !quick_pair(a2, b2) {
        prop_irrel(mode, fuel, st, fe, depth, a2, b2)
    } else {
        Ok(false)
    };
    match pir {
        Err(err) => Err(err),
        Ok(true) => Ok(true),
        Ok(false) => defeq_lits(mode, fuel, st, fe, depth, n, a2, b2),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Literal acceleration, guarded on *both* sides being free of free
/// variables, mirroring the official kernel: unguarded folding is a forbidden
/// strategy superset (on an open `Int32`/`Int64` arithmetic pair it whnfs an
/// open argument and delta-grinds the `Nat.brecOn` tower).  A fold re-enters
/// the loop at `pi = true`, as official restarts `is_def_eq_core` there.
///
/// Deviation: the cited `!a'.hasFvar && !b'.hasFvar` guard is an `if` nest
/// rather than a `&&` of two negations.  A `let`-bound `!b` comes out of
/// Aeneas as Lean's *propositional* `¬ b` (`Bool` coerces to `b = true`), and
/// the `if` that later reads it then asks for a `Decidable` instance the
/// elaborator does not find — the one **Lean-side** error this module
/// produced, and the only place in it where a negation is `let`-bound rather
/// than used directly as a branch condition.
pub fn defeq_lits(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    // `!hasFvar a' && !hasFvar b'`, as an `if` nest: see the note above.
    let closed = if expr_ops::has_fvar(a2) {
        false
    } else if expr_ops::has_fvar(b2) {
        false
    } else {
        true
    };
    let ra = if closed {
        reduce_nat(mode, fuel, st, fe, depth, a2)
    } else {
        Ok(None)
    };
    match ra {
        Err(err) => Err(err),
        Ok(Some(a3)) => defeq_loop(mode, fuel, st, fe, depth, n, true, &a3, b2),
        Ok(None) => {
            let rb = if closed {
                reduce_nat(mode, fuel, st, fe, depth, b2)
            } else {
                Ok(None)
            };
            match rb {
                Err(err) => Err(err),
                Ok(Some(b3)) => defeq_loop(mode, fuel, st, fe, depth, n, true, a2, &b3),
                Ok(None) => defeq_delta(mode, fuel, st, fe, depth, n, a2, b2),
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Lazy delta, **decision before materialization**: the two heads and their
/// hints decide which side to unfold, and `unfold_definition` runs only
/// inside the branch that consumes it.  The `pure false` fallbacks are
/// unreachable (`unfoldable_head` is `unfold_definition(…).is_some()` by
/// construction) and sound.
pub fn defeq_delta(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let ua = unfoldable_head(fe, a2);
    let ub = unfoldable_head(fe, b2);
    if ua && !ub {
        match unfold_definition(fe, a2) {
            Some(a3) => defeq_loop(mode, fuel, st, fe, depth, n, false, &a3, b2),
            None => Ok(false),
        }
    } else if !ua && ub {
        match unfold_definition(fe, b2) {
            Some(b3) => defeq_loop(mode, fuel, st, fe, depth, n, false, a2, &b3),
            None => Ok(false),
        }
    } else if ua && ub {
        defeq_delta_both(mode, fuel, st, fe, depth, n, a2, b2)
    } else {
        defeq_struct(mode, fuel, st, fe, depth, a2, b2)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Both heads unfoldable: unfold only the side with the greater hint; at
/// equal *regular* hints try the same-head congruence short-circuit first
/// (the `sameRegular` guard mirrors the reference kernels exactly and is
/// deliberate — at equal `abbrev` hints both sides unfold eagerly instead);
/// otherwise unfold both.
pub fn defeq_delta_both(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let ha = head_hint(fe, a2);
    let hb = head_hint(fe, b2);
    if env::reducibility_hint_lt(&hb, &ha) {
        match unfold_definition(fe, a2) {
            Some(a3) => defeq_loop(mode, fuel, st, fe, depth, n, false, &a3, b2),
            None => Ok(false),
        }
    } else if env::reducibility_hint_lt(&ha, &hb) {
        match unfold_definition(fe, b2) {
            Some(b3) => defeq_loop(mode, fuel, st, fe, depth, n, false, a2, &b3),
            None => Ok(false),
        }
    } else if env::reducibility_hint_same_regular(&ha, &hb) && same_const_heads(a2, b2) {
        match defeq_spine(mode, fuel, st, fe, depth, a2, b2) {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => defeq_unfold_both(mode, fuel, st, fe, depth, n, a2, b2),
        }
    } else {
        defeq_unfold_both(mode, fuel, st, fe, depth, n, a2, b2)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// `match unfoldDefinition env a', unfoldDefinition env b' with | some a₂,
/// some b₂ => k false a₂ b₂ | _, _ => pure false`, the tail both equal-hint
/// arms share.
pub fn defeq_unfold_both(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    match unfold_definition(fe, a2) {
        None => Ok(false),
        Some(a3) => match unfold_definition(fe, b2) {
            None => Ok(false),
            Some(b3) => defeq_loop(mode, fuel, st, fe, depth, n, false, &a3, &b3),
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Neither head unfolds: structural congruence with the stuck fallbacks, in
/// the cited arm order (which is load-bearing — the literal/constructor-form
/// arms come before the general stuck ones, and the one-sided λ η arms come
/// after the binder congruences).  Spelled as one `match` on the pair of
/// constructors, as `expr::beq_go` is.
pub fn defeq_struct(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match (&a.0.kind, &b.0.kind) {
        (ExprKind::Sort(u), ExprKind::Sort(v)) => lift_fueled(level::is_equiv(u, v)),
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => Ok(expr::literal_beq(l1, l2)),
        (ExprKind::Lit(Literal::NatVal(nn)), ExprKind::Const(c, us)) => {
            if us.len() == 0 && name::beq(c, &basis_names::nat_zero_name()) {
                Ok(nat::is_zero(nn))
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Const(c, us), ExprKind::Lit(Literal::NatVal(nn))) => {
            if us.len() == 0 && name::beq(c, &basis_names::nat_zero_name()) {
                Ok(nat::is_zero(nn))
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Lit(Literal::NatVal(nn)), ExprKind::App(f, x)) => {
            match succ_of(nn, f) {
                Some(k) => {
                    let lk = expr::lit(Literal::NatVal(k));
                    core_c::defeq(mode, fuel, st, fe, depth, &lk, x)
                }
                None => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            }
        }
        (ExprKind::App(f, x), ExprKind::Lit(Literal::NatVal(nn))) => {
            match succ_of(nn, f) {
                Some(k) => {
                    let lk = expr::lit(Literal::NatVal(k));
                    core_c::defeq(mode, fuel, st, fe, depth, x, &lk)
                }
                None => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            }
        }
        (ExprKind::Lit(Literal::StrVal(s)), ExprKind::App(f, _)) => {
            if str_expansion_fires(fe, f) {
                let c = str_lit_to_constructor(s);
                core_c::defeq(mode, fuel, st, fe, depth, &c, b)
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::App(f, _), ExprKind::Lit(Literal::StrVal(s))) => {
            if str_expansion_fires(fe, f) {
                let c = str_lit_to_constructor(s);
                core_c::defeq(mode, fuel, st, fe, depth, a, &c)
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Fvar(i, _), ExprKind::Fvar(j, _)) => {
            if *i == *j {
                Ok(true)
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Const(n1, us1), ExprKind::Const(n2, us2)) => {
            if name::beq(n1, n2) {
                match lift_fueled(level::is_equiv_list(us1, us2)) {
                    Err(err) => Err(err),
                    Ok(true) => Ok(true),
                    Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
                }
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::ForallE(t1, b1, m1), ExprKind::ForallE(t2, b2, m2)) => {
            defeq_binders(mode, fuel, st, fe, depth, t1, b1, m1, t2, b2, m2, true)
        }
        (ExprKind::Lam(t1, b1, m1), ExprKind::Lam(t2, b2, m2)) => {
            defeq_binders(mode, fuel, st, fe, depth, t1, b1, m1, t2, b2, m2, false)
        }
        (ExprKind::App(_, _), ExprKind::App(_, _)) => {
            defeq_apps(mode, fuel, st, fe, depth, a, b)
        }
        (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
            if name::beq(s1, s2) && *i1 == *i2 {
                let e1 = expr::dup(e1);
                let e2 = expr::dup(e2);
                match core_c::defeq(mode, fuel, st, fe, depth, &e1, &e2) {
                    Err(err) => Err(err),
                    Ok(true) => Ok(true),
                    Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
                }
            } else {
                stuck_irrel(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Lam(t1, b1, m1), _) => {
            let t1 = expr::dup(t1);
            let b1 = expr::dup(b1);
            let m1 = expr::binder_meta_dup(m1);
            match eta_cert(mode, fuel, st, fe, depth, &t1, &b1, &m1, b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            }
        }
        (_, ExprKind::Lam(t2, b2, m2)) => {
            let t2 = expr::dup(t2);
            let b2 = expr::dup(b2);
            let m2 = expr::binder_meta_dup(m2);
            match eta_cert(mode, fuel, st, fe, depth, &t2, &b2, &m2, a) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            }
        }
        _ => stuck_irrel(mode, fuel, st, fe, depth, a, b),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// The cited `match nn, f with | k + 1, .const c [] => if c = natSuccName …`
/// of the packed-literal-against-`Nat.succ` arms: the predecessor, when the
/// literal is positive and the function part is the bare `Nat.succ`.
pub fn succ_of(nn: &Nat, f: &Expr) -> Option<Nat> {
    if nat::is_zero(nn) {
        None
    } else {
        match &f.0.kind {
            ExprKind::Const(c, us) => {
                if us.len() == 0 && name::beq(c, &basis_names::nat_succ_name()) {
                    Some(nat::pred(nn))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// The cited `cO = stringOfListName ∧ usO = [] ∧ strLitSupported env` guard
/// of the string-literal expansion arms — the reference kernels'
/// `tryStringLitExpansion`, which fires exactly when the other side's
/// function part is the bare `String.ofList` constant.
pub fn str_expansion_fires(fe: &FEnv, f: &Expr) -> bool {
    match &f.0.kind {
        ExprKind::Const(c, us) => {
            if us.len() == 0 && name::beq(c, &basis_names::string_of_list_name()) {
                str_lit_supported(fe)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Binder congruence, the ∀ and λ arms together (they are byte-identical
/// apart from the message tag): the domains, then the bodies at a fresh
/// variable of the *right* side's domain, and **last** the two prop-ness
/// annotations at the verified modes — only a pair that is otherwise
/// definitionally equal reaches the comparison, so a firing mismatch is
/// exactly the cross-provenance coherence corner, declined loudly.
pub fn defeq_binders(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    t1: &Expr,
    b1: &Expr,
    m1: &BinderMeta,
    t2: &Expr,
    b2: &Expr,
    m2: &BinderMeta,
    is_forall: bool,
) -> CheckM<bool> {
    const M_PI: [u32; 39] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 102, 111, 114, 97,
        108, 108, 41,
    ];
    const M_LAM: [u32; 36] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 108, 97, 109, 41,
    ];
    match core_c::defeq(mode, fuel, st, fe, depth, t1, t2) {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let v = expr::fvar(depth, expr::dup(t2));
            let o1 = expr_ops::instantiate1(b1, &v, 0);
            let o2 = expr_ops::instantiate1(b2, &v, 0);
            match core_c::defeq(mode, fuel, st, fe, depth + 1, &o1, &o2) {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => {
                    if env::verified_checks(mode) && !prop_when::beq(&m1.pw, &m2.pw) {
                        if is_forall {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_PI,
                            )))
                        } else {
                            Err(core_types::not_implemented(core_types::code_points(
                                &M_LAM,
                            )))
                        }
                    } else {
                        Ok(true)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Stuck applications: **spine-wise** congruence (the official kernel's
/// `is_def_eq_app`) — equal spine lengths, one head comparison, then the
/// argument lists pairwise, then the stuck fallbacks.  Recursing on the
/// *partial* applications would re-enter the whole body once per spine node
/// (con-leche's task #106), which no reference kernel does.
pub fn defeq_apps(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    let args_a = expr_ops::get_app_args(a);
    let args_b = expr_ops::get_app_args(b);
    if args_a.len() != args_b.len() {
        stuck_irrel(mode, fuel, st, fe, depth, a, b)
    } else {
        let fa = expr_ops::get_app_fn(a);
        let fb = expr_ops::get_app_fn(b);
        match core_c::defeq(mode, fuel, st, fe, depth, &fa, &fb) {
            Err(err) => Err(err),
            Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            Ok(true) => match def_eq_list(mode, fuel, st, fe, depth, &args_a, &args_b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel(mode, fuel, st, fe, depth, a, b),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2633-2638 defeqLoop
/// The lazy-delta loop: iterate `defeq_step` on its own step budget.
pub fn defeq_loop(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    pi: bool,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    const M: [u32; 26] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101,
        102, 101, 113, 32, 108, 111, 111, 112,
    ];
    if n == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        defeq_step(mode, fuel, st, fe, depth, n - 1, pi, a, b)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2640-2644 defeqLoopFuel
/// Step budget of the lazy-delta loop (lean4lean's `FuelConfig.lazyDelta`,
/// generously sized here because this loop also absorbs the
/// literal-acceleration re-entries).  Exhaustion is an internal error, never
/// a verdict.
pub fn defeq_loop_fuel() -> u64 {
    100000
}

/// con-leche: ConLeche/Kernel/Core.lean:2646-2649 defeqBody
/// The definitional-equality body: the lazy-delta loop at its own step
/// budget, entered at `pi = true`.
pub fn defeq_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    defeq_loop(mode, fuel, st, fe, depth, defeq_loop_fuel(), true, a, b)
}

/// con-leche: ConLeche/Kernel/Core.lean:2651-2660 isPropType
/// Check that a (raw) type is a `Prop` by annotating it and inferring its
/// sort.  The inference is at the io grade: `ty'` is the pass's own output,
/// already annotated — the bottom-up circularity guard.
pub fn is_prop_type(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
) -> CheckM<bool> {
    match core_c::annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => match core_c::infer_io(mode, fuel, st, fe, depth, &ty2) {
            Err(err) => Err(err),
            Ok(t) => match ensure_sort(mode, fuel, st, fe, depth, &t) {
                Err(err) => Err(err),
                Ok(s) => lift_fueled(level::is_equiv(&s, &level::zero())),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The annotation pass (`Core.lean:2677-2858`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:2676-2677 pwWritten
/// Is this datum a real (non-placeholder) input annotation?  The parser's
/// placeholder for an absent `"pw"` field is `.never`, which is also a
/// legitimate value, so the pass recomputes over `.never` unconditionally.
///
/// The cited `!pw.isNever` is an `if` nest, as `defeq_lits`' guard is and for
/// the same reason (see its note): a `!` in a *value* position is Lean's
/// propositional `¬` in the model.
pub fn pw_written(pw: &PropWhen) -> bool {
    if prop_when::is_never(pw) {
        false
    } else {
        true
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2679-2685 annotBinderMeta
/// The datum a rebuilt binder ends up with: the one threaded in from the node
/// below (the chain rule), unless it carries a real input annotation — those
/// are judged by validation, never overwritten.  Nothing in this module calls
/// it (`annotateBody` writes `⟨pw⟩` directly); the interned pass
/// (`Cached/CoreC.lean`, task #19) is its consumer.
pub fn annot_binder_meta(pw: Option<PropWhen>, mb: &BinderMeta) -> BinderMeta {
    match pw {
        Some(p) => {
            if pw_written(&mb.pw) {
                expr::binder_meta_dup(mb)
            } else {
                BinderMeta { pw: p }
            }
        }
        None => expr::binder_meta_dup(mb),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2687-2718 annotPwPi
/// The ∀ node's datum: the zero-ness of the *codomain*'s sort, on the
/// already-annotated opened body — exactly the value `infer_body`'s ∀ clause
/// validates against.  The head-symbol reader comes first: it subsumes the
/// chain read (`typeSortPW` of a ∀ *is* its `forallPw`) and answers most
/// leaves without inference.
pub fn annot_pw_pi(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    body2: &Expr,
) -> CheckM<PropWhen> {
    match prop_read::type_sort_pw(fe, body2) {
        Some(pw) => Ok(pw),
        None => match core_c::infer_io(mode, fuel, st, fe, depth, body2) {
            Err(err) => Err(err),
            Ok(t) => match ensure_sort(mode, fuel, st, fe, depth, &t) {
                Err(err) => Err(err),
                Ok(v) => Ok(level::zeroness_of(&v)),
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2720-2734 annotPwLam
/// The λ node's datum: the zero-ness of the sort of the *body's type*.
/// Mirrors `infer_body`'s λ clause exactly — the reader first (it subsumes
/// the `lamPw` chain read), then one leaf computation.
pub fn annot_pw_lam(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    body2: &Expr,
) -> CheckM<PropWhen> {
    match prop_read::proof_pw(fe, body2) {
        Some(pw) => Ok(pw),
        None => match core_c::infer_io(mode, fuel, st, fe, depth, body2) {
            Err(err) => Err(err),
            Ok(bt) => match core_c::infer_io(mode, fuel, st, fe, depth, &bt) {
                Err(err) => Err(err),
                Ok(btt) => match ensure_sort(mode, fuel, st, fe, depth, &btt) {
                    Err(err) => Err(err),
                    Ok(vb) => Ok(level::zeroness_of(&vb)),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The annotation body: compute the codomain-sort annotations of every
/// binder, bottom-up, by real inference on the opened (already annotated)
/// body.  The `.app` clause is structural — the application rule is not
/// checked here; the inference sweep that follows re-checks every application
/// and every binder body and validates each annotation against its own
/// result.
pub fn annotate_body(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_FVAR: [u32; 26] = [
        102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 32, 111, 117, 116, 32,
        111, 102, 32, 115, 99, 111, 112, 101,
    ];
    const M_NAT: [u32; 46] = [
        78, 97, 116, 32, 108, 105, 116, 101, 114, 97, 108, 32, 119, 105, 116, 104, 111, 117,
        116, 32, 116, 104, 101, 32, 78, 97, 116, 32, 98, 97, 115, 105, 115, 32, 100, 101, 99,
        108, 97, 114, 97, 116, 105, 111, 110, 115,
    ];
    const M_STR: [u32; 54] = [
        115, 116, 114, 105, 110, 103, 32, 108, 105, 116, 101, 114, 97, 108, 115, 32, 98, 101,
        102, 111, 114, 101, 32, 116, 104, 101, 32, 83, 116, 114, 105, 110, 103, 32, 115, 117,
        112, 112, 111, 114, 116, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115,
    ];
    match &e.0.kind {
        ExprKind::Bvar(_) => Ok(expr::dup(e)),
        ExprKind::Fvar(idx, _) => {
            if *idx < depth {
                Ok(expr::dup(e))
            } else {
                Err(core_types::invalid(core_types::code_points(&M_FVAR)))
            }
        }
        ExprKind::Sort(_) => Ok(expr::dup(e)),
        ExprKind::Const(_, _) => Ok(expr::dup(e)),
        ExprKind::Lit(Literal::NatVal(_)) => {
            if nat_lit_supported(fe) {
                Ok(expr::dup(e))
            } else {
                Err(core_types::invalid(core_types::code_points(&M_NAT)))
            }
        }
        ExprKind::Lit(Literal::StrVal(_)) => {
            if str_lit_supported(fe) {
                Ok(expr::dup(e))
            } else {
                Err(core_types::not_implemented(core_types::code_points(&M_STR)))
            }
        }
        ExprKind::App(f, a) => match core_c::annotate(mode, fuel, st, fe, depth, f) {
            Err(err) => Err(err),
            Ok(f2) => match core_c::annotate(mode, fuel, st, fe, depth, a) {
                Err(err) => Err(err),
                Ok(a2) => Ok(expr::app(f2, a2)),
            },
        },
        ExprKind::ForallE(ty, body, mb) => {
            annotate_binder(mode, fuel, st, fe, depth, ty, body, mb, true)
        }
        ExprKind::Lam(ty, body, mb) => {
            annotate_binder(mode, fuel, st, fe, depth, ty, body, mb, false)
        }
        ExprKind::LetE(ty, v, b) => annotate_let(mode, fuel, st, fe, depth, ty, v, b),
        ExprKind::Proj(sn, i, pe) => {
            annotate_proj(mode, fuel, st, fe, depth, sn, *i, pe)
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The ∀ and λ clauses, which differ only in the node they rebuild and the
/// datum function they call (`annot_pw_pi` / `annot_pw_lam`): annotate the
/// domain, annotate the body opened at a variable of the *annotated* domain,
/// compute the datum unless the input carries a real one, and rebuild with
/// the body closed again.
pub fn annotate_binder(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
    is_forall: bool,
) -> CheckM<Expr> {
    match core_c::annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => {
            let v = expr::fvar(depth, expr::dup(&ty2));
            let opened = expr_ops::instantiate1(body, &v, 0);
            match core_c::annotate(mode, fuel, st, fe, depth + 1, &opened) {
                Err(err) => Err(err),
                Ok(body2) => {
                    let pw = if !pw_written(&mb.pw) {
                        if is_forall {
                            annot_pw_pi(mode, fuel, st, fe, depth + 1, &body2)
                        } else {
                            annot_pw_lam(mode, fuel, st, fe, depth + 1, &body2)
                        }
                    } else {
                        Ok(prop_when::dup(&mb.pw))
                    };
                    match pw {
                        Err(err) => Err(err),
                        Ok(p) => {
                            let closed = expr_ops::abstract1(&body2, depth, 0);
                            if is_forall {
                                Ok(expr::forall_e(ty2, closed, BinderMeta { pw: p }))
                            } else {
                                Ok(expr::lam(ty2, closed, BinderMeta { pw: p }))
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The `.letE` clause: the official `infer_let` triple —
/// `ensure_sort(infer(type))`, `infer(val)`, `is_def_eq(val_type, type)` —
/// runs HERE, on the annotated annotation and the annotated value, before the
/// ζ reduct is taken (con-leche's task #217).  The body is annotated *with
/// the value transparent*, i.e. as its ζ reduct, and the reduct substitutes
/// the **raw** `v`, not the annotated `v'` — the Lean's own spelling.
pub fn annotate_let(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    v: &Expr,
    b: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 23] = [
        108, 101, 116, 32, 118, 97, 108, 117, 101, 32, 116, 121, 112, 101, 32, 109, 105, 115,
        109, 97, 116, 99, 104,
    ];
    match core_c::annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => match core_c::infer(mode, fuel, st, fe, depth, &ty2) {
            Err(err) => Err(err),
            Ok(tty) => match ensure_sort(mode, fuel, st, fe, depth, &tty) {
                Err(err) => Err(err),
                Ok(_) => match core_c::annotate(mode, fuel, st, fe, depth, v) {
                    Err(err) => Err(err),
                    Ok(v2) => match core_c::infer(mode, fuel, st, fe, depth, &v2) {
                        Err(err) => Err(err),
                        Ok(tv) => {
                            match core_c::defeq(mode, fuel, st, fe, depth, &tv, &ty2) {
                                Err(err) => Err(err),
                                Ok(false) => Err(core_types::invalid(
                                    core_types::code_points(&M),
                                )),
                                Ok(true) => {
                                    let red = expr_ops::instantiate1(b, v, 0);
                                    core_c::annotate(mode, fuel, st, fe, depth, &red)
                                }
                            }
                        }
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The `.proj` clause: run the projection rule (the one place it is checked).
/// A table entry types the node directly, and the display name is normalized
/// to the type's head so reduction's table lookup is complete on annotated
/// terms — but the node's OWN structure name is official's `infer_proj`
/// premise and is checked HERE (con-leche's task #271 / issue #7), since the
/// normalization below would otherwise repair a node that names another
/// inductive.
pub fn annotate_proj(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    sn: &Name,
    i: u64,
    pe: &Expr,
) -> CheckM<Expr> {
    const M_NONSTRUCT: [u32; 34] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 110, 32, 97, 32, 110, 111,
        110, 45, 115, 116, 114, 117, 99, 116, 117, 114, 101, 32, 116, 121, 112, 101,
    ];
    match core_c::annotate(mode, fuel, st, fe, depth, pe) {
        Err(err) => Err(err),
        Ok(e2) => match infer_io_whnf(mode, fuel, st, fe, depth, &e2) {
            Err(err) => Err(err),
            Ok(te) => {
                let f = expr_ops::get_app_fn(&te);
                match &f.0.kind {
                    ExprKind::Const(t, _) => {
                        let targs = expr_ops::get_app_args(&te);
                        annotate_proj_entry(fe, sn, t, i, &e2, &targs)
                    }
                    _ => Err(core_types::not_implemented(core_types::code_points(
                        &M_NONSTRUCT,
                    ))),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The table lookup of `annotate_proj` and its three verdicts: the checked
/// node, the out-of-range index on a projectable structure (invalid), and the
/// shape without any projection support (decline).
pub fn annotate_proj_entry(
    fe: &FEnv,
    sn: &Name,
    t: &Name,
    i: u64,
    e2: &Expr,
    targs: &Vec<Expr>,
) -> CheckM<Expr> {
    const M_OTHER: [u32; 52] = [
        105, 110, 118, 97, 108, 105, 100, 32, 112, 114, 111, 106, 101, 99, 116, 105, 111, 110,
        58, 32, 116, 104, 101, 32, 110, 111, 100, 101, 32, 110, 97, 109, 101, 115, 32, 97,
        110, 111, 116, 104, 101, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101,
    ];
    const M_PARAMS: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 112, 97, 114, 97, 109, 101, 116,
        101, 114, 32, 109, 105, 115, 109, 97, 116, 99, 104,
    ];
    const M_RANGE: [u32; 29] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 105, 110, 100, 101, 120, 32, 111,
        117, 116, 32, 111, 102, 32, 114, 97, 110, 103, 101,
    ];
    const M_NONSTRUCTLIKE: [u32; 39] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 111, 110, 32, 97, 32, 110, 111,
        110, 45, 115, 116, 114, 117, 99, 116, 117, 114, 101, 45, 108, 105, 107, 101, 32, 116,
        121, 112, 101,
    ];
    match fenv::find_proj(fe, t, i) {
        Some(entry) => {
            if !name::beq(t, sn) {
                Err(core_types::invalid(core_types::code_points(&M_OTHER)))
            } else if (targs.len() as u64) != entry.num_params {
                Err(core_types::invalid(core_types::code_points(&M_PARAMS)))
            } else {
                Ok(expr::proj(name::dup(t), i, expr::dup(e2)))
            }
        }
        None => {
            if fenv::find_proj(fe, t, 0).is_some() {
                Err(core_types::invalid(core_types::code_points(&M_RANGE)))
            } else {
                Err(core_types::not_implemented(core_types::code_points(
                    &M_NONSTRUCTLIKE,
                )))
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:2901-2904 checkFuel
/// The shared fuel for the checker core: bounds the recursion depth of
/// reduction, inference and definitional equality.  Exhaustion is an internal
/// error, never a verdict.
pub fn check_fuel() -> u64 {
    100000
}

/* Not ported from `Kernel/Core.lean` (DESIGN.md §3.1), and why:

   * `instance : ToString CheckError` (`:53-57`) — rendering only; §3.1 says
     message strings need not match, and the CLI (outside the verified core)
     renders errors.  Already recorded by task #14, which ported the
     `CheckError` half of the file.
   * `structure CoreFns` (`:66-92`) and `CoreFns.ioView` (`:94-95`) — the
     record of closures the bodies are written against.  §3.1 ties the knot
     with a mutually recursive block of plain functions instead, so there is
     no record type: `r.whnf` is `core_c::whnf` by name, and `ioView`'s
     substitution of the `infer` slot by the `inferIO` slot is the `io` flag
     of `infer_at` (see `infer_forall`, `infer_lam_after_dom`).
   * `coreKnot` (`:2866-2900`) — the knot itself, which the port spells as
     the six memoizing wrappers of `crate::cached::core_c` (`coreKnotI`,
     `Cached/CoreC.lean:1916-1973`), cited there.
   * the eight `@[simp] theorem`s about `recRuleBits` (`:1545-1586`) and the
     four about `projFnRule` (`:1596-1613`) — field-projection equations,
     i.e. the *spec* this port will be proved against, not part of it.

   Everything else executable in the file is above.  The five `FEnv.lean`
   guards that read the same bodies through the index (`natLitSupportedF`,
   `strLitSupportedF`, `natOpGuardF`, `natOpStoredF`, `andRescueSlotsF`) are
   covered by the corresponding function here, with a second citation, per
   the module note's point 3. */

#[cfg(test)]
mod tests {
    use crate::cached::core_c;
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::basis_names;
    use crate::kernel::core_k;
    use crate::kernel::core_types::CheckError;
    use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal, Env};
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr, ExprKind};
    use crate::kernel::fenv;
    use crate::kernel::fenv::FEnv;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;

    /// A one-character name.
    fn nm(c: u32) -> Name {
        name::mk_str(name::anonymous(), vec![c])
    }

    /// The `.never` binder datum ("the codomain sort is nonzero at every
    /// valuation"), which is what a `Sort 1`-valued binder validates to.
    fn never_meta() -> BinderMeta {
        BinderMeta {
            pw: prop_when::never(),
        }
    }

    fn prop_meta() -> BinderMeta {
        BinderMeta {
            pw: prop_when::if_all_zero(Vec::new()),
        }
    }

    fn ax(n: Name, ty: Expr) -> ConstantInfo {
        ConstantInfo::AxiomInfo(ConstantVal {
            name: n,
            level_params: Vec::new(),
            ty,
        })
    }

    /// `A : Sort 1`, `a : A`, `f : ∀ (_ : A), A` — hand-built axioms, newest
    /// first as `Env.consts` is.  A `Nat`-like inductive is far too big for a
    /// unit test, and none of these paths needs one.
    fn env_afa() -> FEnv {
        let a_ty = expr::mk_const(nm(65), Vec::new());
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ax(
            nm(102),
            expr::forall_e(expr::dup(&a_ty), expr::dup(&a_ty), never_meta()),
        ));
        consts.push(ax(nm(97), expr::dup(&a_ty)));
        consts.push(ax(nm(65), expr::sort(level::succ(level::zero()))));
        fenv::mk_fenv(Env { consts })
    }

    fn a_ty() -> Expr {
        expr::mk_const(nm(65), Vec::new())
    }

    /// `whnf` performs the β step of `(λ (x : A). x) a`, with the per-redex
    /// argument certificate actually running (the λ's datum is not `.never`,
    /// so `beta_gate_fires` is false and `infer_io a ≡ A` is checked).
    #[test]
    fn whnf_beta_reduces_an_identity_application() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        let id = expr::lam(a_ty(), expr::bvar(0), prop_meta());
        let redex = expr::app(id, expr::dup(&a));
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(r) => assert!(expr::beq(&r, &a), "β should have produced `a`"),
            Err(_) => panic!("β reduction failed"),
        }
        // and with the gate firing (a `.never` datum) the same reduct comes
        // out, without the certificate
        let mut st2: CState = state_c::cstate_new();
        let id2 = expr::lam(a_ty(), expr::bvar(0), never_meta());
        let redex2 = expr::app(id2, expr::dup(&a));
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &redex2) {
            Ok(r) => assert!(expr::beq(&r, &a)),
            Err(_) => panic!("β reduction under the gate failed"),
        }
        // `whnfCore` alone does the same (β is not delta)
        let mut st3: CState = state_c::cstate_new();
        match core_c::whnf_core(&mode, core_k::check_fuel(), &mut st3, &fe, 0, &redex2) {
            Ok(r) => assert!(expr::beq(&r, &a)),
            Err(_) => panic!("whnfCore β failed"),
        }
    }

    /// `infer` of `λ (x : Sort 1). x` is a `∀`, with the domain and the
    /// codomain both `Sort 1`, and the λ's datum validated against the
    /// codomain sort (`Sort 2` is nonzero at every valuation, so `.never`).
    #[test]
    fn infer_of_a_lambda_is_a_pi() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let s1 = expr::sort(level::succ(level::zero()));
        let lam = expr::lam(expr::dup(&s1), expr::bvar(0), never_meta());
        match core_c::infer(&mode, core_k::check_fuel(), &mut st, &fe, 0, &lam) {
            Ok(t) => match &t.0.kind {
                ExprKind::ForallE(dom, body, m) => {
                    assert!(expr::beq(dom, &s1));
                    assert!(expr::beq(body, &s1));
                    assert!(prop_when::is_never(&m.pw));
                }
                _ => panic!("inferring a λ must give a ∀"),
            },
            Err(_) => panic!("inference failed"),
        }
        // a wrong datum on the innermost binder is a *decline*, not a reject
        let mut st2: CState = state_c::cstate_new();
        let bad = expr::lam(expr::dup(&s1), expr::bvar(0), prop_meta());
        match core_c::infer(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &bad) {
            Err(CheckError::NotImplemented(_)) => (),
            Err(_) => panic!("a datum mismatch must be `notImplemented`"),
            Ok(_) => panic!("a datum mismatch must not be accepted"),
        }
        // and `Sort 1` itself infers as `Sort 2`
        let mut st3: CState = state_c::cstate_new();
        match core_c::infer(&mode, core_k::check_fuel(), &mut st3, &fe, 0, &s1) {
            Ok(t) => assert!(expr::beq(
                &t,
                &expr::sort(level::succ(level::succ(level::zero())))
            )),
            Err(_) => panic!("inferring a sort failed"),
        }
    }

    /// `defeq` equates `λ (x : A). f x` with `f` by the η certificate, and
    /// separates `f` from `a`.
    #[test]
    fn defeq_eta_equal_lambdas() {
        let fe = env_afa();
        let mode = CheckMode::Verified;
        let f = expr::mk_const(nm(102), Vec::new());
        let a = expr::mk_const(nm(97), Vec::new());
        let eta = expr::lam(
            a_ty(),
            expr::app(expr::dup(&f), expr::bvar(0)),
            never_meta(),
        );
        let mut st: CState = state_c::cstate_new();
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st, &fe, 0, &eta, &f) {
            Ok(b) => assert!(b, "η-expansion of `f` must be defeq to `f`"),
            Err(_) => panic!("η certification failed"),
        }
        // the other direction too (the one-sided λ arm on the right)
        let mut st2: CState = state_c::cstate_new();
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &f, &eta) {
            Ok(b) => assert!(b),
            Err(_) => panic!("η certification failed (mirrored)"),
        }
        // two distinct axioms are not definitionally equal
        let mut st3: CState = state_c::cstate_new();
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st3, &fe, 0, &f, &a) {
            Ok(b) => assert!(!b, "`f` and `a` must differ"),
            Err(_) => panic!("defeq of two axioms should not error"),
        }
        // the syntactic fast path
        let mut st4: CState = state_c::cstate_new();
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st4, &fe, 0, &a, &a) {
            Ok(b) => assert!(b),
            Err(_) => panic!("reflexivity failed"),
        }
    }

    /// Fuel zero is the knot's zero arm: every slot throws `.internal "fuel
    /// exhausted: …"`, never a verdict (`Core.lean:2871-2880`).
    #[test]
    fn fuel_zero_is_an_internal_error() {
        let fe = env_afa();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        let mut st: CState = state_c::cstate_new();
        for r in [
            core_c::whnf(&mode, 0, &mut st, &fe, 0, &a),
            core_c::whnf_core(&mode, 0, &mut st, &fe, 0, &a),
            core_c::infer(&mode, 0, &mut st, &fe, 0, &a),
            core_c::infer_io(&mode, 0, &mut st, &fe, 0, &a),
            core_c::annotate(&mode, 0, &mut st, &fe, 0, &a),
        ] {
            match r {
                Err(CheckError::Internal(m)) => assert!(m.len() > 0),
                Err(_) => panic!("fuel exhaustion must be `.internal`"),
                Ok(_) => panic!("fuel 0 must not answer"),
            }
        }
        match core_c::defeq(&mode, 0, &mut st, &fe, 0, &a, &a) {
            Err(CheckError::Internal(_)) => (),
            Err(_) => panic!("fuel exhaustion must be `.internal`"),
            Ok(_) => panic!("fuel 0 must not answer, not even on a syntactic hit"),
        }
        // nothing was cached on the way
        assert_eq!(st.whnf_c.len(), 0);
        assert_eq!(st.whnf_core_c.len(), 0);
        assert_eq!(st.infer_c.len(), 0);
        assert_eq!(st.defeq_c.len(), 0);
        assert_eq!(st.annot_c.len(), 0);
        // a *deep* term at a small fuel exhausts inside, not at the entry
        let deep = expr::app(
            expr::lam(a_ty(), expr::bvar(0), prop_meta()),
            expr::dup(&a),
        );
        let mut st2: CState = state_c::cstate_new();
        match core_c::whnf(&mode, 2, &mut st2, &fe, 0, &deep) {
            Err(CheckError::Internal(_)) => (),
            Err(_) => panic!("expected the fuel error"),
            Ok(_) => panic!("fuel 2 cannot get through a β certificate"),
        }
    }

    /// The memo is a *hit* on the second call: the wrappers' maps do not grow,
    /// and the answer is the same (`memoEI`/`memoBI`, `CoreC.lean:1877-1905`).
    #[test]
    fn a_second_call_hits_the_memo() {
        let fe = env_afa();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        let redex = expr::app(
            expr::lam(a_ty(), expr::bvar(0), prop_meta()),
            expr::dup(&a),
        );
        let mut st: CState = state_c::cstate_new();
        let first = match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(r) => r,
            Err(_) => panic!("first whnf failed"),
        };
        let sizes = (
            st.whnf_c.len(),
            st.whnf_core_c.len(),
            st.infer_c.len(),
            st.infer_io_c.len(),
            st.defeq_c.len(),
        );
        assert!(sizes.0 > 0, "the `whnf` memo must have recorded the answer");
        assert!(sizes.1 > 0, "and so must `whnfCore`'s");
        let second = match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(r) => r,
            Err(_) => panic!("second whnf failed"),
        };
        assert!(expr::beq(&first, &second));
        assert_eq!(
            sizes,
            (
                st.whnf_c.len(),
                st.whnf_core_c.len(),
                st.infer_c.len(),
                st.infer_io_c.len(),
                st.defeq_c.len()
            ),
            "a memo hit must not write"
        );
        // the defeq memo behaves the same way under `memoBI`'s pair key
        let f = expr::mk_const(nm(102), Vec::new());
        let mut st2: CState = state_c::cstate_new();
        let _ = core_c::defeq(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &f, &a);
        let n = st2.defeq_c.len();
        assert!(n > 0);
        let _ = core_c::defeq(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &f, &a);
        assert_eq!(st2.defeq_c.len(), n);
    }

    /// `annotate` writes the binder datum the front door then validates: the
    /// parser's placeholder `.never` is recomputed, an `ifAllZero` input
    /// annotation is preserved, and the pass's output passes `infer`.
    #[test]
    fn annotate_writes_the_datum_infer_validates() {
        let fe = env_afa();
        let mode = CheckMode::Verified;
        let s1 = expr::sort(level::succ(level::zero()));
        let raw = expr::lam(expr::dup(&s1), expr::bvar(0), never_meta());
        let mut st: CState = state_c::cstate_new();
        let annotated =
            match core_c::annotate(&mode, core_k::check_fuel(), &mut st, &fe, 0, &raw) {
                Ok(r) => r,
                Err(_) => panic!("annotation failed"),
            };
        match &annotated.0.kind {
            ExprKind::Lam(dom, _, m) => {
                assert!(expr::beq(dom, &s1));
                assert!(prop_when::is_never(&m.pw), "`Sort 2` is never zero");
            }
            _ => panic!("annotating a λ must give a λ"),
        }
        match core_c::infer(&mode, core_k::check_fuel(), &mut st, &fe, 0, &annotated) {
            Ok(_) => (),
            Err(_) => panic!("infer must validate the pass's own output"),
        }
        // a real input annotation is never overwritten (`pwWritten`)
        assert!(!core_k::pw_written(&prop_when::never()));
        assert!(core_k::pw_written(&prop_when::if_all_zero(Vec::new())));
        let kept = expr::lam(a_ty(), expr::bvar(0), prop_meta());
        let mut st2: CState = state_c::cstate_new();
        match core_c::annotate(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &kept) {
            Ok(r) => match &r.0.kind {
                ExprKind::Lam(_, _, m) => {
                    assert!(!prop_when::is_never(&m.pw), "the input datum survives")
                }
                _ => panic!("expected a λ"),
            },
            Err(_) => panic!("annotation failed"),
        }
    }

    /// The pure readers of the file, on the hand-built environment: the delta
    /// decision, the reducibility hint, the `Nat`/`String` literal guards, the
    /// `Bool.true` test and the `quickPair` classification.
    #[test]
    fn the_syntactic_readers() {
        let fe = env_afa();
        let a = expr::mk_const(nm(97), Vec::new());
        let s1 = expr::sort(level::succ(level::zero()));
        // no definition is stored, so nothing unfolds
        assert!(!core_k::unfoldable_head(&fe, &a));
        assert!(core_k::unfold_definition(&fe, &a).is_none());
        assert!(!core_k::is_ctor_app(&fe, &a));
        // the literal guards fail without the basis
        assert!(!core_k::nat_lit_supported(&fe));
        assert!(!core_k::str_lit_supported(&fe));
        assert!(!core_k::nat_op_stored(&fe, &core_k::nat_add_name()));
        // `Bool.true` is the bare constant
        assert!(core_k::is_bool_true(&expr::mk_const(
            core_k::bool_true_name(),
            Vec::new()
        )));
        assert!(!core_k::is_bool_true(&expr::mk_const(
            core_k::bool_true_name(),
            level::singleton(level::zero())
        )));
        assert!(!core_k::is_bool_true(&a));
        // `quickPair`: the four same-constructor pairs and nothing else
        let pi = expr::forall_e(expr::dup(&s1), expr::dup(&s1), never_meta());
        let lam = expr::lam(expr::dup(&s1), expr::bvar(0), never_meta());
        assert!(core_k::quick_pair(&s1, &s1));
        assert!(core_k::quick_pair(&pi, &pi));
        assert!(core_k::quick_pair(&lam, &lam));
        assert!(!core_k::quick_pair(&pi, &lam));
        assert!(!core_k::quick_pair(&a, &a));
        // `sameConstHeads` needs *applications* on both sides
        let fa = expr::app(expr::mk_const(nm(102), Vec::new()), expr::dup(&a));
        assert!(core_k::same_const_heads(&fa, &fa));
        assert!(!core_k::same_const_heads(&a, &a));
        // the op-name tables are the cited sizes, and `natOpDeps` is reflexive
        assert_eq!(core_k::nat_op_names().len(), 7);
        assert_eq!(core_k::nat_div_mod_names().len(), 8);
        assert_eq!(core_k::nat_op_wf_names().len(), 8);
        assert!(name::contains(
            &core_k::nat_op_deps(&core_k::nat_pow_name()),
            &core_k::nat_pow_name()
        ));
        assert_eq!(core_k::nat_op_deps(&nm(122)).len(), 0);
        assert_eq!(core_k::nat_op_equations(0, &core_k::nat_beq_name()).len(), 4);
        assert_eq!(core_k::nat_op_equations(0, &nm(122)).len(), 0);
        // the decimal rendering behind `projModelName`
        assert_eq!(core_k::nat_to_dec(0), vec![48]);
        assert_eq!(core_k::nat_to_dec(1207), vec![49, 50, 48, 55]);
        // the fuel constants are the cited values
        assert_eq!(core_k::check_fuel(), 100000);
        assert_eq!(core_k::whnf_loop_fuel(), 100000);
        assert_eq!(core_k::defeq_loop_fuel(), 100000);
        assert_eq!(core_k::whnf_core_loop_fuel(), 1000000);
    }

    /// The `Nat`-literal fast path end to end: with `Nat`, `Nat.zero`,
    /// `Nat.succ` and a stored `Nat.add` in the environment, `whnf` folds
    /// `Nat.add 2 3` to the literal `5`, and `Nat.succ (lit 4)` packs back.
    #[test]
    fn the_nat_literal_fast_path() {
        use crate::kernel::env::ReducibilityHint;
        use crate::kernel::expr::Literal;
        use crate::ron::nat;
        let nat_ty = expr::mk_const(basis_names::nat_name(), Vec::new());
        let mut consts: Vec<ConstantInfo> = Vec::new();
        // `Nat.add : Nat → Nat → Nat`, stored as a definition whose value is
        // never looked at here (the fast path intercepts first)
        consts.push(ConstantInfo::DefnInfo(
            ConstantVal {
                name: core_k::nat_add_name(),
                level_params: Vec::new(),
                ty: expr::forall_e(
                    expr::dup(&nat_ty),
                    expr::forall_e(expr::dup(&nat_ty), expr::dup(&nat_ty), never_meta()),
                    never_meta(),
                ),
            },
            expr::dup(&nat_ty),
            ReducibilityHint::Regular(1),
        ));
        consts.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: basis_names::nat_succ_name(),
                level_params: Vec::new(),
                ty: expr::forall_e(expr::dup(&nat_ty), expr::dup(&nat_ty), never_meta()),
            },
            0,
            1,
        ));
        consts.push(ConstantInfo::CtorInfo(
            ConstantVal {
                name: basis_names::nat_zero_name(),
                level_params: Vec::new(),
                ty: expr::dup(&nat_ty),
            },
            0,
            0,
        ));
        consts.push(ConstantInfo::IndInfo(
            ConstantVal {
                name: basis_names::nat_name(),
                level_params: Vec::new(),
                ty: expr::sort(level::succ(level::zero())),
            },
            crate::kernel::env::ind_caps_default(),
        ));
        let fe = fenv::mk_fenv(Env { consts });
        assert!(core_k::nat_lit_supported(&fe));
        assert!(core_k::nat_op_stored(&fe, &core_k::nat_add_name()));
        assert!(core_k::nat_op_guard(&fe, &core_k::nat_add_name()));
        assert!(core_k::nat_op_stored_ok(&fe, &core_k::nat_add_name()));
        let mode = CheckMode::Verified;
        let lit = |k: u64| expr::lit(Literal::NatVal(nat::from_u64(k)));
        let sum = expr::app(
            expr::app(
                expr::mk_const(core_k::nat_add_name(), Vec::new()),
                lit(2),
            ),
            lit(3),
        );
        let mut st: CState = state_c::cstate_new();
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &sum) {
            Ok(r) => assert!(expr::beq(&r, &lit(5)), "2 + 3 must fold to 5"),
            Err(_) => panic!("the Nat fast path failed"),
        }
        // `Nat.succ (lit 4)` packs to `lit 5`
        let succ4 = expr::app(
            expr::mk_const(basis_names::nat_succ_name(), Vec::new()),
            lit(4),
        );
        let mut st2: CState = state_c::cstate_new();
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &succ4) {
            Ok(r) => assert!(expr::beq(&r, &lit(5))),
            Err(_) => panic!("the succ packing failed"),
        }
        // `rawNatLit?` reads a literal and `Nat.zero`, nothing else
        assert!(core_k::raw_nat_lit(&lit(7)).is_some());
        assert!(core_k::raw_nat_lit(&expr::mk_const(
            basis_names::nat_zero_name(),
            Vec::new()
        ))
        .is_some());
        assert!(core_k::raw_nat_lit(&nat_ty).is_none());
        // `natLitToConstructor` at both arms, and the literal's own type
        assert!(expr::beq(
            &core_k::nat_lit_to_constructor(&nat::zero()),
            &expr::mk_const(basis_names::nat_zero_name(), Vec::new())
        ));
        assert!(expr::beq(
            &core_k::nat_lit_to_constructor(&nat::from_u64(5)),
            &succ4
        ));
        let mut st3: CState = state_c::cstate_new();
        match core_c::infer(&mode, core_k::check_fuel(), &mut st3, &fe, 0, &lit(9)) {
            Ok(t) => assert!(expr::beq(&t, &nat_ty)),
            Err(_) => panic!("a literal must type as `Nat`"),
        }
        // `natOpResult` on the arithmetic the fast path folds
        let five = core_k::nat_op_result(
            &core_k::nat_add_name(),
            &nat::from_u64(2),
            &nat::from_u64(3),
        );
        match five {
            Some(e) => assert!(expr::beq(&e, &lit(5))),
            None => panic!("add must fold"),
        }
        // the `pow` blow-up bound declines instead of computing
        assert!(core_k::nat_op_result(
            &core_k::nat_pow_name(),
            &nat::from_u64(2),
            &nat::from_u64(16777217)
        )
        .is_none());
        assert!(core_k::nat_op_result(&nm(122), &nat::zero(), &nat::zero()).is_none());
    }
}
