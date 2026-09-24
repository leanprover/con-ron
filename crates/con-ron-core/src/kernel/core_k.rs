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
//!   `same_const_heads`, `raw_nat_lit`, `is_ctor_app`, `is_unit_like_ty`,
//!   `eta_ctor_shape`, `is_bool_true`, `quick_pair`, `succ_of`,
//!   `str_expansion_fires`, `pw_written`, `lift_fueled`.  **Seven of these
//!   carry a second citation to `Cached/StateC.lean`'s `*C` index guards**
//!   (`isUnitLikeTyC`, `isCtorAppC`, `headHintC`, `unfoldableHeadC`,
//!   `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC`): those are the same
//!   function, since the port reads the environment through `FEnv` anyway
//!   (deviation 3 below).  So are `litToCtorIfNatI` and `annotBinderMetaI`,
//!   whose twins are the spec's under a `pure`;
//! * the pinned name tables and the `Nat`-operation pin sets;
//! * the install-time rule bits (`rec_rule_bits`, `proj_fn_rule`,
//!   `rec_rule_k`) and the shape conjunctions the cached certificates read
//!   (`struct_eta_shape_ok`, `unit_shape_ok`, `proj_fire_shape_ok`,
//!   `fab_scope_ok`, `proj_entry_fire_ok`, `and_rescue_slots`);
//! * the pure pieces of the inference clauses (`infer_fvar`,
//!   `infer_lit_nat`, `infer_lit_str`, `infer_proj_at`,
//!   `proj_type_at_checked`, `proj_entry_type_at`, `annotate_proj_entry`);
//! * the four loop budgets (`whnf_core_loop_fuel`, `whnf_loop_fuel`,
//!   `defeq_loop_fuel`, `check_fuel`);
//! * the `Vec` helpers and the owning environment probes.
//!
//! Four functions here are **dead and deliberately kept**, as task #18's
//! eleven were, so the provenance ledger stays in step with its source:
//! `beta_gate_fires` (the pure β gate; the cached sites read
//! `mode.betaSkip`), `eta_projs`/`eta_projs_from` (superseded by
//! `core_c::proj_apps_i`, but `eta_fab_args`/`eta_fab_args_e` are written
//! against them and are dead in the Lean too), and `consts_resolve` (whose
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
use crate::kernel::core_types::CheckError;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{
    CheckMode, ConstantInfo, ConstantVal, IndCaps, ProjEntry, RecRule, RecRuleFire,
    ReducibilityHint,
};
use crate::kernel::expr;
use crate::kernel::expr::{BinderMeta, Expr, ExprView, Literal};
use crate::kernel::expr_ops;
use crate::kernel::fenv;
use crate::kernel::fenv::FEnv;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::nat;
use crate::ron::nat::Nat;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `Vec` helpers for the `List` operations the Lean uses for free
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:82-102 unknownConstError
/// **The verdict at a constant the environment does not know.**  `sorryAx`
/// is the one axiom the checker tolerates as a *declaration* and installs
/// nothing for (`basis_names::sorry_ax_name`), so a *use* of it is a
/// positively detected unsupported feature and the run declines, at the
/// record that uses it; every other unresolved name is a malformed stream
/// and rejects.  The cited interpolation is dropped (§3.1: message strings
/// need not match).
pub fn unknown_const_error(n: &Name) -> CheckError {
    const S: [u32; 24] = [
        117, 115, 101, 32, 111, 102, 32, 116, 104, 101, 32, 115, 111, 114, 114, 121, 65, 120,
        32, 97, 120, 105, 111, 109,
    ];
    const U: [u32; 16] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116,
    ];
    if name::beq(n, &basis_names::sorry_ax_name()) {
        core_types::not_implemented(core_types::code_points(&S))
    } else {
        core_types::invalid(core_types::code_points(&U))
    }
}

/// con-leche: none — `List.drop` on a `Vec`; Lean's list tail is shared
/// `xs.drop k`, as a fresh `Vec` of `P` bumps.
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

/// con-leche: none — `List.drop` at a `u64` count, without a `usize` cast
/// `xs.drop n` where the count is a machine word of the checker's own
/// arithmetic (a parameter count, a major-premise index).  Task #61: the
/// arity is a `u64` and `Vec` indexing is `usize`, so the obvious spelling
/// is `drop_exprs(xs, n as usize)` — which Aeneas models as a *truncating*
/// cast (DESIGN.md §3.4: no `as` on data).  The count is therefore consumed
/// by the recursion instead of converted: `i` walks the `Vec` and `n`
/// counts down, so no value ever crosses between the two widths.
pub fn drop_exprs_n(xs: &Vec<Expr>, n: u64) -> Vec<Expr> {
    drop_exprs_n_from(xs, n, 0)
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

/// con-leche: none — `List.take` at a `u64` count, without a `usize` cast
/// `xs.take n`, the counting twin of `drop_exprs_n` (task #61).
pub fn take_exprs_n(xs: &Vec<Expr>, n: u64) -> Vec<Expr> {
    take_exprs_n_from(xs, n, 0, Vec::new())
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

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// The scope guard's third conjunct,
/// `fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)` — a closure
/// over a `List.all`, so it becomes the index recursion below.  All three of
/// `majorToCtor`'s branches run it.
pub fn fvar_leaves_subset(xs: &Vec<(u64, Expr)>, ys: &Vec<(u64, Expr)>) -> bool {
    fvar_leaves_subset_from(xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName
/// `toString i` for a `Nat` index: the decimal code points, most significant
/// digit first, `0` for zero.  Lean's `Nat.toString` is the runtime's; on the
/// `u64` of DESIGN.md §3.3 this is the recursion that produces it.
pub fn nat_to_dec(i: u64) -> Vec<u32> {
    nat_to_dec_go(i, Vec::new())
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:136-155 unfoldDefinition
/// con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint
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

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
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

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
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

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// con-leche: ConLeche/Kernel/Core.lean:351-374 structEtaProjCerts
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
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

/// con-leche: ConLeche/Kernel/Core.lean:151-154 liftFueled
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:41-44 projModelName
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp
/// con-leche: ConLeche/Cached/StateC.lean:62-69 isCtorAppC
/// Is the expression headed by a stored constructor?
pub fn is_ctor_app(fe: &FEnv, e: &Expr) -> bool {
    let f = expr_ops::get_app_fn(e);
    match expr::view(&f) {
        ExprView::Const(c, _) => match fenv::find(fe, c) {
            Some(ci) => is_ctor_info(ci),
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:55-62 piResultIsProp
/// Does the syntactic pi telescope end in a (normalized) `Prop`?
pub fn pi_result_is_prop(e: &Expr) -> bool {
    let r = expr_ops::pi_result(e);
    match expr::view(&r) {
        ExprView::Sort(u) => match level::is_equiv(u, &level::zero()) {
            Some(true) => true,
            Some(false) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:64-72 piResultZ
/// The result-sort zero-ness datum of an inductive's type (`IndCaps.sortZ`,
/// computed at the block's install).  A telescope that does not end in a
/// sort gets `ifAllZero []` — "zero at every valuation".
pub fn pi_result_z(e: &Expr) -> PropWhen {
    let r = expr_ops::pi_result(e);
    match expr::view(&r) {
        ExprView::Sort(u) => level::zeroness_of(u),
        _ => prop_when::if_all_zero(Vec::new()),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:74-82 piResultNeverZero
/// The *specification* of `caps_never_zero`: the walk down the family's type
/// that the stored datum replaces.  Nothing executable calls it; ported so
/// the provenance gate stays in step with its source (task #11's
/// `beqRecursive` rule).
pub fn pi_result_never_zero(lps: &Vec<Name>, us: &Vec<Level>, e: &Expr) -> bool {
    let r = expr_ops::pi_result(e);
    match expr::view(&r) {
        ExprView::Sort(u) => level::is_never_zero(&level::subst(lps, us, u)),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:84-95 capsNeverZero
/// Is a stored inductive's result sort, at the given level instantiation,
/// provably nonzero?  Read off the stored datum.
pub fn caps_never_zero(lps: &Vec<Name>, us: &Vec<Level>, caps: &IndCaps) -> bool {
    prop_when::is_never(&level::subst_pw(lps, us, &caps.sort_z))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:97-134 isUnitLikeTy
/// con-leche: ConLeche/Cached/StateC.lean:48-60 isUnitLikeTyC
/// Is this (whnf'd) type expression a unit-like inductive type?  The
/// head-name comparison against the single pin that can pass (`PUnit`) comes
/// first, then the two stored-shape checks specialised to it — con-leche's
/// task #161 item C1 computation downgrade, licensed by `unitLike_eq_punit`.
/// The `&&` cascade is an `if` nest, and `[r]` is `rules.len() == 1`.
pub fn is_unit_like_ty(fe: &FEnv, e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Const(c, _) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:97-134 isUnitLikeTy
/// The cited `match env.find? punitName with | some (.indInfo _ _) => true |
/// _ => false`, factored out (task #14's probe rule).
pub fn is_punit_ind(fe: &FEnv) -> bool {
    match fenv::find(fe, &basis_names::punit_name()) {
        Some(ConstantInfo::IndInfo(_, _)) => true,
        Some(_) => false,
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:97-134 isUnitLikeTy
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:157-170 unfoldableHead
/// con-leche: ConLeche/Cached/StateC.lean:80-87 unfoldableHeadC
/// May the delta step unfold `e`'s head?  The *decision* the lazy delta step
/// takes; the unfolding itself is materialized only inside the branch that
/// consumes it.  By construction
/// `unfoldable_head(fe, e) = unfold_definition(fe, e).is_some()`.
pub fn unfoldable_head(fe: &FEnv, e: &Expr) -> bool {
    let f = expr_ops::get_app_fn(e);
    match expr::view(&f) {
        ExprView::Const(n, us) => match fenv::find(fe, n) {
            Some(ConstantInfo::DefnInfo(cv, _, _)) => us.len() == cv.level_params.len(),
            Some(_) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:172-181 headHint
/// con-leche: ConLeche/Cached/StateC.lean:71-78 headHintC
/// The reducibility hint of the constant at the head of `e` (`opaque` when
/// the head is not a stored definition — a theorem included).
pub fn head_hint(fe: &FEnv, e: &Expr) -> ReducibilityHint {
    let f = expr_ops::get_app_fn(e);
    match expr::view(&f) {
        ExprView::Const(n, _) => match defn_probe(fe, n) {
            Some((_, _, hint)) => hint,
            None => ReducibilityHint::Opaque,
        },
        _ => ReducibilityHint::Opaque,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:183-192 sameConstHeads
/// con-leche: ConLeche/Cached/StateC.lean:89-96 sameConstHeadsC
/// Are `a` and `b` applications of the *same* constant (the lazy delta
/// same-head short-circuit)?  Both sides must actually be applications.
pub fn same_const_heads(a: &Expr, b: &Expr) -> bool {
    match expr::view(&a) {
        ExprView::App(f1, _) => match expr::view(&b) {
            ExprView::App(f2, _) => {
                let g1 = expr_ops::get_app_fn(f1);
                let g2 = expr_ops::get_app_fn(f2);
                match expr::view(&g1) {
                    ExprView::Const(n1, _) => match expr::view(&g2) {
                        ExprView::Const(n2, _) => name::beq(n1, n2),
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:194-200 natLitToConstructor
/// The constructor form of a `Nat` literal, one layer: `n + 1` becomes
/// `Nat.succ (lit n)`, `0` becomes `Nat.zero`.  The cited `match n with | 0 |
/// k + 1` is `nat::is_zero` plus `nat::pred` on the bignum (§3.3).
pub fn nat_lit_to_constructor(n: &Nat) -> Expr {
    if nat::is_zero(n) {
        expr::mk_const(basis_names::nat_zero_name(), Vec::new())
    } else {
        expr::app(
            expr::mk_const(basis_names::nat_succ_name(), Vec::new()),
            expr::lit(expr::literal_nat(nat::pred(n))),
        )
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:202-206 natIndOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:208-212 natZeroOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:214-223 natSuccOk
/// The stored `Nat.succ` declaration has the expected (annotated) shape.
pub fn nat_succ_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(ConstantInfo::CtorInfo(cv, _, _)) => {
            if cv.level_params.len() == 0 {
                match expr::view(&cv.ty) {
                    ExprView::ForallE(dom, body, _) => match expr::view(&dom) {
                        ExprView::Const(c1, us1) => match expr::view(&body) {
                            ExprView::Const(c2, us2) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:225-233 natLitSupported
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:235-260 Expr.constsResolve
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:262-267 litToCtorIfNat
/// con-leche: ConLeche/Cached/CoreC.lean:84-90 litToCtorIfNatI
/// Convert a `Nat`-literal major premise to constructor form, one layer;
/// anything else passes through.
pub fn lit_to_ctor_if_nat(fe: &FEnv, e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::Lit(Literal::NatVal(n)) => {
            if nat_lit_supported(fe) {
                nat_lit_to_constructor(n)
            } else {
                expr::dup(e)
            }
        }
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:269-274 rawNatLit?
/// con-leche: ConLeche/Cached/StateC.lean:98-103 rawNatLitC?
/// A `Nat` literal reading of a whnf'd expression: literals and the
/// `Nat.zero` constant (the official kernel's `rawNatLitExt?`).
pub fn raw_nat_lit(e: &Expr) -> Option<Nat> {
    match expr::view(&e) {
        ExprView::Lit(Literal::NatVal(n)) => Some(nat::clone(n)),
        ExprView::Const(c, us) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:288-299 strLitToConstructor
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:301-307 stringTyOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:309-315 charTyOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:317-328 listTyOk
/// The stored `List` declaration has the expected (annotated) shape
/// `List.{p} : Type p → Type p`.
pub fn list_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 1 {
                let p: &Name = &cv.level_params[0];
                match expr::view(&cv.ty) {
                    ExprView::ForallE(dom, body, _) => match expr::view(&dom) {
                        ExprView::Sort(u1) => match expr::view(&body) {
                            ExprView::Sort(u2) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:330-341 listNilTyOk
/// The stored `List.nil` declaration has the expected (annotated) shape
/// `List.nil.{p} : ∀ (α : Type p), List.{p} α`.
pub fn list_nil_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 1 {
                let p: &Name = &cv.level_params[0];
                match expr::view(&cv.ty) {
                    ExprView::ForallE(dom, body, _) => match expr::view(&dom) {
                        ExprView::Sort(u1) => match expr::view(&body) {
                            ExprView::App(hd, arg) => match expr::view(&arg) {
                                ExprView::Bvar(0) => match expr::view(&hd) {
                                    ExprView::Const(l1, us1) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk
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
                match expr::view(&cv.ty) {
                    ExprView::ForallE(d1, b1, _) => match expr::view(&d1) {
                        ExprView::Sort(u1) => match expr::view(&b1) {
                            ExprView::ForallE(d2, b2, _) => match expr::view(&d2) {
                                ExprView::Bvar(0) => match expr::view(&b2) {
                                    ExprView::ForallE(d3, b3, _) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:343-360 listConsTyOk
/// The innermost two slots of `list_cons_ty_ok`'s pattern —
/// `.forallE (.app (.const l1 us1) (.bvar 1)) (.app (.const l2 us2) (.bvar 2))`
/// and the four comparisons — as their own function, so the nesting stays
/// readable.
pub fn list_cons_tail_ok(u1: &Level, d3: &Expr, b3: &Expr, p: &Name) -> bool {
    match expr::view(&d3) {
        ExprView::App(h1, a1) => match expr::view(&b3) {
            ExprView::App(h2, a2) => match expr::view(&a1) {
                ExprView::Bvar(1) => match expr::view(&a2) {
                    ExprView::Bvar(2) => match expr::view(&h1) {
                        ExprView::Const(l1, us1) => match expr::view(&h2) {
                            ExprView::Const(l2, us2) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:362-371 charOfNatTyOk
/// The stored `Char.ofNat` declaration has the expected (annotated) shape
/// `Char.ofNat : Nat → Char`.
pub fn char_of_nat_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                match expr::view(&cv.ty) {
                    ExprView::ForallE(dom, body, _) => match expr::view(&dom) {
                        ExprView::Const(c1, us1) => match expr::view(&body) {
                            ExprView::Const(c2, us2) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:373-383 stringOfListTyOk
/// The stored `String.ofList` declaration has the expected (annotated) shape
/// `String.ofList : List.{0} Char → String`.
pub fn string_of_list_ty_ok(ci: Option<&ConstantInfo>) -> bool {
    match ci {
        Some(c) => {
            let cv = env::to_constant_val(c);
            if cv.level_params.len() == 0 {
                match expr::view(&cv.ty) {
                    ExprView::ForallE(dom, body, _) => match expr::view(&dom) {
                        ExprView::App(hd, arg) => match expr::view(&body) {
                            ExprView::Const(c2, us2) => match expr::view(&hd) {
                                ExprView::Const(l1, us1) => match expr::view(&arg) {
                                    ExprView::Const(c1, us_c) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:385-403 strLitSupported
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:46-53 isCtorApp
/// The cited `match env.find? c with | some (.ctorInfo _ _ _) => true | _ =>
/// false`.  `env::is_rec_info` is `env.rs`'s twin of this (task #14); the
/// constructor test has no other consumer, so it lives here.
pub fn is_ctor_info(ci: &ConstantInfo) -> bool {
    match ci {
        ConstantInfo::CtorInfo(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:433 natPredName
/// `Nat.pred`.
pub fn nat_pred_name() -> Name {
    const S: [u32; 4] = [112, 114, 101, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:434 natAddName
/// `Nat.add`.
pub fn nat_add_name() -> Name {
    const S: [u32; 3] = [97, 100, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:435 natSubName
/// `Nat.sub`.
pub fn nat_sub_name() -> Name {
    const S: [u32; 3] = [115, 117, 98];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:436 natMulName
/// `Nat.mul`.
pub fn nat_mul_name() -> Name {
    const S: [u32; 3] = [109, 117, 108];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:437 natPowName
/// `Nat.pow`.
pub fn nat_pow_name() -> Name {
    const S: [u32; 3] = [112, 111, 119];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:438 natBeqName
/// `Nat.beq`.
pub fn nat_beq_name() -> Name {
    const S: [u32; 3] = [98, 101, 113];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:439 natBleName
/// `Nat.ble`.
pub fn nat_ble_name() -> Name {
    const S: [u32; 3] = [98, 108, 101];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:440 natDivName
/// `Nat.div`.
pub fn nat_div_name() -> Name {
    const S: [u32; 3] = [100, 105, 118];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:441 natModName
/// `Nat.mod`.
pub fn nat_mod_name() -> Name {
    const S: [u32; 3] = [109, 111, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:442 natGcdName
/// `Nat.gcd`.
pub fn nat_gcd_name() -> Name {
    const S: [u32; 3] = [103, 99, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:443 natLandName
/// `Nat.land`.
pub fn nat_land_name() -> Name {
    const S: [u32; 4] = [108, 97, 110, 100];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:444 natLorName
/// `Nat.lor`.
pub fn nat_lor_name() -> Name {
    const S: [u32; 3] = [108, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:445 natXorName
/// `Nat.xor`.
pub fn nat_xor_name() -> Name {
    const S: [u32; 3] = [120, 111, 114];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:446 natShiftLeftName
/// `Nat.shiftLeft`.
pub fn nat_shift_left_name() -> Name {
    const S: [u32; 9] = [115, 104, 105, 102, 116, 76, 101, 102, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:447 natShiftRightName
/// `Nat.shiftRight`.
pub fn nat_shift_right_name() -> Name {
    const S: [u32; 10] = [115, 104, 105, 102, 116, 82, 105, 103, 104, 116];
    name::mk_str(basis_names::nat_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:448 boolName
/// `Bool`.
pub fn bool_name() -> Name {
    const S: [u32; 4] = [66, 111, 111, 108];
    name::mk_str(name::anonymous(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:449 boolTrueName
/// `Bool.true`.
pub fn bool_true_name() -> Name {
    const S: [u32; 4] = [116, 114, 117, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:450 boolFalseName
/// `Bool.false`.
pub fn bool_false_name() -> Name {
    const S: [u32; 5] = [102, 97, 108, 115, 101];
    name::mk_str(bool_name(), core_types::code_points(&S))
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:452-457 Expr.isBoolTrue
/// Is `e` the constant `Bool.true` — the name, no universe levels?
pub fn is_bool_true(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Const(c, us) => {
            if us.len() == 0 {
                name::beq(c, &bool_true_name())
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// The pairs official's `quick_is_def_eq` decides by itself: two sorts, two
/// literals, two `∀`s, two `λ`s.  Charon expands the cited wildcard arm, as
/// in `expr::beq_go` (task #11's note).
pub fn quick_pair(a: &Expr, b: &Expr) -> bool {
    match expr::view(&a) {
        ExprView::Sort(_) => is_sort(b),
        ExprView::Lit(_) => is_lit(b),
        ExprView::ForallE(_, _, _) => is_forall(b),
        ExprView::Lam(_, _, _) => is_lam_k(b),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// The four one-constructor tests `quick_pair`'s second slot needs; Rust has
/// no `.sort _` pattern outside a `match`, so each is a named function
/// (`expr_ops::is_lam` is the `Expr.isLam` of `ExprOps.lean`, a different
/// declaration).
pub fn is_sort(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Sort(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// See `is_sort`.
pub fn is_lit(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Lit(_) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// See `is_sort`.
pub fn is_forall(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::ForallE(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:459-471 Expr.quickPair
/// See `is_sort`.
pub fn is_lam_k(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Lam(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:473-481 natOpNames
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:483-498 natDivModNames
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:500-523 natOpDeps
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// The `s : Expr → Expr` local of the cited `let`-block: `Nat.succ ·`.
/// §3.4 forbids closures, so the three spine builders are named functions.
pub fn nat_eq_s(a: Expr) -> Expr {
    expr::app(expr::mk_const(basis_names::nat_succ_name(), Vec::new()), a)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// The `ap1 : Name → Expr → Expr` local.
pub fn nat_eq_ap1(n: &Name, a: Expr) -> Expr {
    expr::app(expr::mk_const(name::dup(n), Vec::new()), a)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
/// The `ap2 : Name → Expr → Expr → Expr` local.
pub fn nat_eq_ap2(n: &Name, a: Expr, b: Expr) -> Expr {
    expr::app(expr::app(expr::mk_const(name::dup(n), Vec::new()), a), b)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:525-554 natOpEquations
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:556-582 natOpResult
/// The reduct of op `c` on literal arguments (`pred` ignores the second
/// slot).  The arithmetic is `ron::Nat`'s (DESIGN.md §3.3).
///
/// One deviation, in the direction of declining: the cited `b > 16777216`
/// guard on `pow` is the audit's S2 bound; the port compares bignums and
/// then narrows the exponent to `u64` for `nat::pow`, which takes a machine
/// exponent (the bound makes that safe).
///
/// `shiftLeft`/`shiftRight` take the bignum amount unbounded (task
/// #98-SHIFT; tasks #61/#67 had a `Native` failure beyond `u64`): a left
/// shift too large for memory fails like any other allocation, as Lean's
/// would.
pub fn nat_op_result(c: &Name, a: &Nat, b: &Nat) -> CheckM<Option<Expr>> {
    if name::beq(c, &nat_pred_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::pred(a)))))
    } else if name::beq(c, &nat_add_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::add(a, b)))))
    } else if name::beq(c, &nat_sub_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::sub(a, b)))))
    } else if name::beq(c, &nat_mul_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::mul(a, b)))))
    } else if name::beq(c, &nat_pow_name()) {
        if nat::blt(&nat::from_u64(16777216), b) {
            Ok(None)
        } else {
            match nat::to_u64(b) {
                Some(e) => Ok(Some(expr::lit(expr::literal_nat(nat::pow(a, e))))),
                None => Ok(None),
            }
        }
    } else if name::beq(c, &nat_div_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::div(a, b)))))
    } else if name::beq(c, &nat_mod_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::modulo(a, b)))))
    } else if name::beq(c, &nat_gcd_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::gcd(a, b)))))
    } else if name::beq(c, &nat_land_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::land(a, b)))))
    } else if name::beq(c, &nat_lor_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::lor(a, b)))))
    } else if name::beq(c, &nat_xor_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::xor(a, b)))))
    } else if name::beq(c, &nat_shift_left_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::shift_left_nat(a, b)))))
    } else if name::beq(c, &nat_shift_right_name()) {
        Ok(Some(expr::lit(expr::literal_nat(nat::shift_right_nat(a, b)))))
    } else if name::beq(c, &nat_beq_name()) {
        let n = if nat::beq(a, b) {
            bool_true_name()
        } else {
            bool_false_name()
        };
        Ok(Some(expr::mk_const(n, Vec::new())))
    } else if name::beq(c, &nat_ble_name()) {
        let n = if nat::ble(a, b) {
            bool_true_name()
        } else {
            bool_false_name()
        };
        Ok(Some(expr::mk_const(n, Vec::new())))
    } else {
        Ok(None)
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:584-600 natOpGuard
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:602-612 natOpWfNames
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:614-620 Expr.substConst0
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:622-638 Expr.substConstAll
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:640-650 natOpCod
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:652-667 natOpTyPinned
/// con-leche: ConLeche/Kernel/DeclCheck.lean:219-231 natOpTyPinnedF
/// The pinned type of a certified `Nat` operation: `Nat → Nat` for the unary
/// `pred`, `Nat → Nat → Nat` for the arithmetic operations, `Nat → Nat →
/// Bool` for the comparisons.
pub fn nat_op_ty_pinned(fe: &FEnv, c: &Name, ty: &Expr) -> bool {
    let nat_ty = expr::mk_const(basis_names::nat_name(), Vec::new());
    if name::beq(c, &nat_pred_name()) {
        match expr::view(&ty) {
            ExprView::ForallE(dom, body, _) => {
                if expr::beq(dom, &nat_ty) {
                    nat_op_cod(fe, c, body)
                } else {
                    false
                }
            }
            _ => false,
        }
    } else {
        match expr::view(&ty) {
            ExprView::ForallE(dom, inner, _) => match expr::view(&inner) {
                ExprView::ForallE(dom2, body, _) => {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:669-675 natOpStoredOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:677-700 natOpStored
/// con-leche: ConLeche/Kernel/FEnv.lean:147-151 natOpStoredF
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

/// con-leche: ConLeche/Kernel/Core.lean:156-208 reduceNat
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

// ---------------------------------------------------------------------------
// Telescope certificates and proof irrelevance (`Core.lean:848-981`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:702-707 piResidual
/// Peel a `∀`-telescope along an argument list (the residual type of a fully
/// applied telescope).  The `i = 0` wrapper of the index recursion below.
pub fn pi_residual(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    pi_residual_from(e, args, 0)
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:702-707 piResidual
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:726-736 etaProjs
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

/// con-leche: ConLeche/Kernel/Core.lean:376-448 structEtaCertWith
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:738-749 etaCtorShape
/// con-leche: ConLeche/Cached/StateC.lean:105-112 etaCtorShapeC
/// The constructor shape official's `try_eta_struct_core` tests before
/// inferring anything: the candidate's head is a stored constructor applied
/// to exactly its parameters and fields.
pub fn eta_ctor_shape(fe: &FEnv, a: &Expr) -> bool {
    let f = expr_ops::get_app_fn(a);
    match expr::view(&f) {
        ExprView::Const(c, _) => match fenv::find(fe, c) {
            Some(ConstantInfo::CtorInfo(_, cn_p, cn_f)) => {
                (expr_ops::get_app_args(a).len() as u64) == *cn_p + *cn_f
            }
            Some(_) => false,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:475-503 structUnitCert
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:751-759 etaFabArgs
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:761-766 etaFabArgsE
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:768-794 ProjEntry.fireOk
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
/// con-leche: ConLeche/Kernel/CoreDefs.lean:811-813 andRescueSlots
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:796-809 andRescueSlotsOf
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

/// con-leche: ConLeche/Kernel/Core.lean:544-726 majorToCtor
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

// ---------------------------------------------------------------------------
// The install-time rule bits (`Core.lean:1494-1621`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:815-830 recRuleKOf
/// **The K bit at install** (`RecRule.k`): the rule's constructor has no
/// fields and belongs to an inductive stored with the K capability.  Together
/// with a singleton rule list this is the official kernel's
/// `recursor_val::is_k()`.
pub fn rec_rule_k_of(fe: &FEnv, ctor: &Name) -> bool {
    match ctor_probe(fe, ctor) {
        Some((cvj, _, cn_f)) => {
            let res = expr_ops::pi_result(&cvj.ty);
            let head = expr_ops::get_app_fn(&res);
            match expr::view(&head) {
                ExprView::Const(t, _) => match ind_probe(fe, t) {
                    Some((_, caps)) => caps.rule_k && cn_f == 0,
                    None => false,
                },
                _ => false,
            }
        }
        None => false,
    }
}

/// con-leche: ConLeche/Kernel/CoreDefs.lean:832-858 recRuleEtaOf
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
            match expr::view(&head) {
                ExprView::Const(t, _) => match ind_probe(fe, t) {
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:860-870 recRuleBits
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:909-921 projFnRule
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:939-946 recRuleK
/// Is a recursor K-flagged?  The stored bit of its single rule.
pub fn rec_rule_k(rules: &Vec<RecRule>) -> bool {
    if rules.len() == 1 {
        rules[0].k
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Iota (`Core.lean:1695-1800`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// `args.getD i (.bvar 0)` — Lean's out-of-range default is
/// `Inhabited Expr`'s `.bvar 0` (`env::default_expr`).
pub fn get_d_expr(args: &Vec<Expr>, i: u64) -> Expr {
    if i < args.len() as u64 {
        expr::dup(&args[i as usize])
    } else {
        env::default_expr()
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
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

/// con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire
/// con-leche: ConLeche/Kernel/Core.lean:797-910 iotaRec
/// The cited `rl.fire = .inert` test; Rust has no equality on the enum
/// (§3.4 keeps `derive` off the core types), so it is a one-arm match.
pub fn fire_is_inert(f: &RecRuleFire) -> bool {
    match f {
        RecRuleFire::Inert => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Projections (`Core.lean:1803-1888`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt
/// con-leche: ConLeche/Cached/ExprOpsC.lean:839-858 ProjEntry.typeAtI
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:970-979 ProjEntry.typeAt
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:981-1013 betaGateFires
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

/// con-leche: ConLeche/Kernel/Core.lean:963-1052 whnfCoreBody
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

/// con-leche: ConLeche/Kernel/Core.lean:1054-1062 whnfCoreLoopFuel
/// Step budget of the `whnfCore` head-normalization loop (con-leche's task
/// #106).  Nothing in this module reads it — the *interned* `whnfCoreLoopI`
/// does (`Cached/CoreC.lean`, task #19) — but it is ported so the provenance
/// gate stays in step with its source.
pub fn whnf_core_loop_fuel() -> u64 {
    1000000
}

/// con-leche: ConLeche/Kernel/Core.lean:1064-1071 whnfLoopFuel
/// Step budget of the `whnf` reduction loop (lean4lean's `FuelConfig.whnf`,
/// same value).  Literal-acceleration and delta steps are *iteration*, not
/// recursion.
pub fn whnf_loop_fuel() -> u64 {
    100000
}

// ---------------------------------------------------------------------------
// Inference (`Core.lean:2042-2337`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
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

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
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

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
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

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
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

/// con-leche: ConLeche/Kernel/Core.lean:1109-1274 inferBody
/// con-leche: ConLeche/Kernel/Core.lean:1276-1404 inferBodyIO
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
    match expr::view(&f) {
        ExprView::Const(t, us) => match fenv::find_proj(fe, t, i) {
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

// ---------------------------------------------------------------------------
// Definitional equality (`Core.lean:2346-2660`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// The cited `match nn, f with | k + 1, .const c [] => if c = natSuccName …`
/// of the packed-literal-against-`Nat.succ` arms: the predecessor, when the
/// literal is positive and the function part is the bare `Nat.succ`.
pub fn succ_of(nn: &Nat, f: &Expr) -> Option<Nat> {
    if nat::is_zero(nn) {
        None
    } else {
        match expr::view(&f) {
            ExprView::Const(c, us) => {
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

/// con-leche: ConLeche/Kernel/Core.lean:1441-1701 defeqStep
/// The cited `cO = stringOfListName ∧ usO = [] ∧ strLitSupported env` guard
/// of the string-literal expansion arms — the reference kernels'
/// `tryStringLitExpansion`, which fires exactly when the other side's
/// function part is the bare `String.ofList` constant.
pub fn str_expansion_fires(fe: &FEnv, f: &Expr) -> bool {
    match expr::view(&f) {
        ExprView::Const(c, us) => {
            if us.len() == 0 && name::beq(c, &basis_names::string_of_list_name()) {
                str_lit_supported(fe)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1710-1714 defeqLoopFuel
/// Step budget of the lazy-delta loop (lean4lean's `FuelConfig.lazyDelta`,
/// generously sized here because this loop also absorbs the
/// literal-acceleration re-entries).  Exhaustion is an internal error, never
/// a verdict.
pub fn defeq_loop_fuel() -> u64 {
    100000
}

// ---------------------------------------------------------------------------
// The annotation pass (`Core.lean:2677-2858`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/CoreDefs.lean:1015-1016 pwWritten
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

/// con-leche: ConLeche/Kernel/CoreDefs.lean:1018-1024 annotBinderMeta
/// con-leche: ConLeche/Cached/CoreC.lean:1643-1647 annotBinderMetaI
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
                expr::binder_meta(p)
            }
        }
        None => expr::binder_meta_dup(mb),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:1795-1915 annotateBody
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

/// con-leche: ConLeche/Kernel/Core.lean:1960-1963 checkFuel
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
