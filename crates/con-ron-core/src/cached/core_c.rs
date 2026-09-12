//! **The cached checker core** — `ConLeche/Cached/CoreC.lean` in full: the
//! interned bodies (`whnfCoreBodyI`, `whnfBodyI`, `inferBodyI`,
//! `inferBodyIOI`, `defeqBodyI`, `annotateBodyI`) with their telescope and
//! spine loops, and the memoizing knot that ties them (`memoEI` `:1871-1889`,
//! `memoBI` `:1891-1904`, `coreKnotI` `:1906-1976`).
//!
//! This is the executed checker core.  `crate::kernel::core_k` is
//! `Kernel/Core.lean`: its *syntactic readers* and pinned tables are what the
//! bodies here call, and its own bodies — the pure counterparts of the ones
//! here — are gone from the crate, because nothing executes them (task #23;
//! see "The reconciliation" below).
//!
//! ## The knot, and what it ties (DESIGN.md §3.1, "bodies over wrappers")
//!
//! ```text
//! coreKnotI mode fe 0       →  every slot throws `.internal "fuel exhausted: …"`
//! coreKnotI mode fe (n + 1) →  memoEI <map> (fun d e => <body>I mode (prev ()) fe d e)
//! ```
//!
//! and `memoEI get' set' f = fun d e => do match (get' (← get))[e]? with |
//! some r => pure r | none => let r ← f d e; modify (… insert e r); pure r`.
//! So `whnf_core(mode, fuel, st, fe, d, e)` is `(coreKnotI mode fe
//! fuel).whnfCore d e` run at state `st`: `fuel = 0` is the zero arm, and
//! otherwise the probe, the body at `fuel - 1`, and the insert.  The `fuel -
//! 1` is what makes the Rust's `fuel` the same number as the Lean's knot
//! level; a body writes `core_c::whnf(mode, fuel, …)` where the Lean writes
//! `r.whnf d x`, the *wrapper*, by name.  No record, no trait, no closure.
//!
//! ## The reconciliation (task #23; task #18 left it owed)
//!
//! Task #18 tied the wrappers to `Kernel/Core.lean`'s bodies, which use the
//! *unmemoized* level operations and the *unmemoized* stored-constant reads.
//! That was the port's one memo-policy deviation from the executed Lean, and
//! §3.1 forbids it: the Rust's sequence of probes and inserts, per map, must
//! be exactly `coreKnotI`'s.  It is now, because the bodies here are
//! `CoreC.lean`'s own, which means, per map:
//!
//! | map | written by |
//! |---|---|
//! | `whnfCoreC` `whnfC` `inferC` `inferIOC` `annotC` `defeqC` | the six wrappers at the bottom of this file (`memoEI`, `memoBI`) |
//! | `lsimpC` `lnzC` `eqvC` | `state_c::is_equiv_l_m` / `simplify_l_m` / `is_non_zero_l_m`, reached from every `isEquivLM`/`isEquivListLM` site here |
//! | `instC` | `state_c::inst_list_m`, reached from `iota_certs_i_aux` and `beta_peel_i`; the telescope loops use `instListRevM`, which the Lean leaves unmemoized on purpose |
//! | `ienv` `constTyAt` `constValAt` `ruleRhsAt` | `state_c::const_ty_at_m` / `const_val_at_m` / `rule_rhs_at_m`, reached from every stored-constant read here |
//!
//! Two `Level.isEquiv` sites are **deliberately unmemoized**, because the
//! Lean's are: `inferBodyI`'s `.proj` clause reads `Level.isEquiv` directly
//! (`CoreC.lean:1370-1377`), and so does `ProjEntry.fireOk` through
//! `core_k::proj_entry_fire_ok`.  Keeping them off `eqvC` is the memo policy,
//! not an omission.
//!
//! ## Where the cached bodies differ from `Kernel/Core.lean`'s
//!
//! Beyond the operation swaps above, `CoreC.lean` is a different *algorithm*
//! in five places, and the port follows it rather than `Core.lean`:
//!
//! 1. **Bulk beta** (`whnfAppI`/`betaPeelI`, con-leche's task #50): the
//!    argument loop consumes the whole spine, batching consecutive λ binders
//!    into **one** `instListM` instead of a chained `instantiate1` per redex.
//! 2. **The head-normalization loop** (`whnfCoreStepI`/`whnfCoreLoopI`, task
//!    #106): every *reduction* step is iteration on the loop's own step
//!    budget (`core_k::whnf_core_loop_fuel`), so a chain no longer charges
//!    the shared recursion-depth budget one unit per step.  `Core.lean`'s
//!    `whnfCoreBody` recurses through the knot instead.
//! 3. **Bulk telescope consumption** (`inferSpineI`/`inferSpineIOI`, task
//!    #50): the Π-telescope is walked against the whole spine with deferred
//!    substitution.
//! 4. **Binder-telescope loops** (`inferLamsI`/`inferPisI`,
//!    `annotateLamsI`/`annotatePisI`, task #72): a whole binder chain is
//!    peeled with only the domains substituted on the way in, the leaf is
//!    inferred or annotated once on the bulk-opened body, and the chain is
//!    rebuilt with one `abstractRangeM` per domain.  The peel fuel
//!    (`state_c::peel_fuel`) is semantically transparent: on exhaustion the
//!    leaf phase hands the residual chain back to the knot, which is the
//!    chained body's next step.
//! 5. **`ensureSortI` returns the level**, and `iotaRecI` reads its rule's
//!    right-hand side through `ruleRhsAtM` rather than instantiating it.
//!
//! Everything else is the `Core.lean` body with the operations swapped, so
//! each item below carries **two** citations: the `CoreC.lean` block it is
//! and the `Core.lean` block it is the twin of.  Where `Core.lean` has no
//! counterpart (the loops above, `certAtI`, `pinArgsI`) there is one.
//!
//! ## The standing deviations (task #18's four, unchanged)
//!
//! 1. **`mode: &CheckMode` is threaded explicitly** — the Lean knot closes
//!    over the mode; the Rust wrappers are plain functions.
//! 2. **`st: &mut CState`** is the `StateT CState` of `CheckCM`, threaded
//!    through bodies that touch no memo themselves.
//! 3. **The environment is the index `FEnv`** (`fenv::find`/`find_proj`),
//!    which is what `CoreC.lean` reads too (`fe.find?`).
//! 4. **`CoreFnsI.ioView` is a call, not a record**: `inferBodyIOI` recurses
//!    through `r.infer`, which the knot binds to the io slot, so every
//!    `r.infer` *inside the io body and inside `inferSpineIOI`* is
//!    `core_c::infer_io` here.  That substitution is `ioView`.
//!
//! And three more that this task adds:
//!
//! 5. **`certAtI`/`certUnlessI` are spelled out at their sites.**  The Lean
//!    wrappers take the certificate as a `CheckCM Bool` *argument*, i.e. a
//!    closure, which §3.4 forbids; each site is therefore `if
//!    env::certs(mode) { <the certificate> } else { Ok(true) }`, which is the
//!    cited `@[inline] def` after inlining.  The complete list of such sites
//!    is what `.trusted` omits beyond group A, exactly as the Lean's
//!    docstring says — and the port's list is the `env::certs(mode)` reads in
//!    this file.
//! 6. **`annotateBindersOutI`'s `mk` parameter is a `bool`.**  The Lean
//!    passes the node constructor (`fun ty b mb => .forallE ty b mb`) as a
//!    function argument; the port passes `is_forall`, as task #18's
//!    `annotate_binder` already did for the same two clauses.
//! 7. **`List` accumulators are `Vec`s.**  `iotaCertsIAux`'s and
//!    `betaPeelI`'s `arg :: acc` is `expr_ops::cons_expr`, an `O(n)` copy
//!    where Lean's cons is `O(1)`; the *value* of the list — which is what
//!    the `instC` key is — is the cited one.  The `Array` accumulators
//!    (`inferSpineI`, the telescope loops) push, as in the Lean.

use crate::cached::expr_ops_c;
use crate::cached::state_c;
use crate::cached::state_c::CState;
use crate::kernel::basis_names;
use crate::kernel::core_k;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckM;
use crate::kernel::env;
use crate::kernel::env::{CheckMode, ConstantVal, IndCaps, ProjEntry, RecRule, RecRuleFire};
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

/// con-leche: ConLeche/Cached/CoreC.lean:1138-1140 InferLamEntry
/// Stack entry of `infer_lams_i`: the opened domain and the binder meta.
/// The cited `abbrev` is a type alias, erased before Charon sees anything.
pub type InferLamEntry = (Expr, BinderMeta);

/// con-leche: ConLeche/Cached/CoreC.lean:1639-1641 AnnotBinderEntry
/// Stack entry of the annotation binder-telescope loops: the annotated
/// opened domain and the binder meta.
pub type AnnotBinderEntry = (Expr, BinderMeta);

// ---------------------------------------------------------------------------
// The helper twins (`CoreC.lean:66-280`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:66-82 unfoldDefinitionI
/// The cited `some (.defnInfo cv _ _)` destructuring, as an owning probe of
/// the one field the guard reads — the level-parameter count.  The value is
/// deliberately *not* read here: `const_val_at_m` fetches it, through the
/// `constValAt` memo, only inside the branch that consumes it.
pub fn defn_lp_count(fe: &FEnv, n: &Name) -> Option<usize> {
    match fenv::find(fe, n) {
        Some(ci) => match ci {
            env::ConstantInfo::DefnInfo(cv, _, _) => Some(cv.level_params.len()),
            _ => None,
        },
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:66-82 unfoldDefinitionI
/// con-leche: ConLeche/Kernel/Core.lean:208-227 unfoldDefinition
/// **The δ step's materialization**, monadic: the unfolded value is read
/// through the `(name, levels)` cache (`constValAtM`) instead of being
/// level-instantiated afresh at every delta step.  Like the spec, a theorem
/// never unfolds (only `.defnInfo` matches).
///
/// `core_k::unfoldable_head` is the *decision* this function materializes,
/// and `unfoldableHead fe e = (unfoldDefinitionI fe e).isSome` still holds:
/// both read the same `.defnInfo` level-parameter count.
pub fn unfold_definition_i(
    st: &mut CState,
    fe: &FEnv,
    e: &Expr,
) -> CheckM<Option<Expr>> {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(n, us) => {
            let n = name::dup(n);
            let us = env::levels_copy(us);
            match defn_lp_count(fe, &n) {
                Some(k) => {
                    if us.len() == k {
                        match state_c::const_val_at_m(st, fe, &n, &us) {
                            Err(err) => Err(err),
                            Ok(v) => {
                                let args = expr_ops::get_app_args(e);
                                Ok(Some(state_c::mk_app_n_m(v, &args)))
                            }
                        }
                    } else {
                        Ok(None)
                    }
                }
                None => Ok(None),
            }
        }
        _ => Ok(None),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:92-152 reduceNatI
/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// Literal acceleration, run in the `whnf` loop *before* delta-unfolding:
/// pack `Nat.succ` applied to a literal back into a literal, and fold the
/// fourteen binary operations on literal arguments.
///
/// The argument order is load-bearing (the audit's D15): the **first**
/// argument is head-normalised and, unless it is a literal, the step fails
/// *without touching the second*.  The `.app (.app (.const c []) a) b`
/// pattern is read outermost-in, so the Rust's `b` is the cited `b` and the
/// inner application's argument is the cited `a`.
///
/// The twin reads `rawNatLitC?`/`natLitSupportedF`/`natOpStoredF`, which are
/// `core_k`'s own functions through the index (the module note's deviation
/// 3); nothing else changes, and it touches no memo of its own.
pub fn reduce_nat_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Option<Expr>> {
    const M: [u32; 34] = [
        110, 97, 116, 105, 118, 101, 32, 78, 97, 116, 32, 99, 111, 109, 112, 117, 116, 97, 116,
        105, 111, 110, 32, 111, 110, 32, 108, 105, 116, 101, 114, 97, 108, 115,
    ];
    match &e.0.kind {
        ExprKind::App(f, b) => match &f.0.kind {
            ExprKind::Const(c, us) => {
                if us.len() == 0
                    && name::beq(c, &basis_names::nat_succ_name())
                    && core_k::nat_lit_supported(fe)
                {
                    match whnf(mode, fuel, st, fe, depth, b) {
                        Err(err) => Err(err),
                        Ok(wa) => match core_k::raw_nat_lit(&wa) {
                            Some(n) => Ok(Some(expr::lit(expr::literal_nat(nat::add(
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
                    } else if core_k::is_nat_bin_op(c) && core_k::nat_op_stored(fe, c) {
                        reduce_nat_bin_i(mode, fuel, st, fe, depth, c, a, b)
                    } else if name::contains(&core_k::nat_op_wf_names(), c)
                        && core_k::nat_lit_supported(fe)
                    {
                        match reduce_nat_lits_i(mode, fuel, st, fe, depth, a, b) {
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

/// con-leche: ConLeche/Cached/CoreC.lean:92-152 reduceNatI
/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// The certified-operation arm of `reduce_nat_i`: both arguments read as
/// literals, first one then the other, and `core_k::nat_op_result` folds.
pub fn reduce_nat_bin_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    a: &Expr,
    b: &Expr,
) -> CheckM<Option<Expr>> {
    match reduce_nat_lits_i(mode, fuel, st, fe, depth, a, b) {
        Err(err) => Err(err),
        Ok(None) => Ok(None),
        Ok(Some(p)) => Ok(core_k::nat_op_result(c, &p.0, &p.1)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:92-152 reduceNatI
/// con-leche: ConLeche/Kernel/Core.lean:774-826 reduceNat
/// The two-literal read both binary arms share: head-normalise the first
/// argument and stop unless it is a literal, then the second.
pub fn reduce_nat_lits_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<Option<(Nat, Nat)>> {
    match whnf(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(wa) => match core_k::raw_nat_lit(&wa) {
            None => Ok(None),
            Some(n1) => match whnf(mode, fuel, st, fe, depth, b) {
                Err(err) => Err(err),
                Ok(wb) => match core_k::raw_nat_lit(&wb) {
                    None => Ok(None),
                    Some(n2) => Ok(Some((n1, n2))),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:154-193 iotaCertsIAux
/// con-leche: ConLeche/Kernel/Core.lean:828-860 iotaCerts
/// **The bulk telescope certificate** (con-leche's task #50): peel the raw
/// telescope while accumulating the certified arguments, substituting only
/// each binder's *domain* (small, and through the `instC` memo) instead of
/// copying the whole residual telescope per argument.  A raw `bvar` body —
/// whose substitution could expose further `∀`-binders, the fold semantics —
/// substitutes the accumulator and re-enters at the empty one.
///
/// `lic` is the ι-slot licence: at a licensed walk a `.never` binder's slot
/// is skipped outright (no domain instantiation, no inference, no defeq) and
/// the binder's argument joins the accumulator as if certified.  The datum
/// read is the level-instantiated one — the telescope came from
/// `constTyAtM`, which is where `Nat.rec.{u}`'s `.ifAllZero [u]` major binder
/// becomes `.never` at `u := succ _`.
///
/// Deviations: the cited `args` list is a `Vec` walked by index `i` (the
/// cited `arg :: rest` is `args[i]`), and `acc` is a `Vec` grown at the
/// *front* (`expr_ops::cons_expr`, an `O(n)` copy where Lean's cons is
/// `O(1)`) — the list's value, which is the `instC` key's second component,
/// is the cited one.  The cited `termination_by (args.length, acc.length)`
/// is the port's `i`/`acc.len()` pair; Aeneas asks for no termination proof.
pub fn iota_certs_i_aux(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    lic: bool,
    ty: &Expr,
    acc: &Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<bool> {
    if i >= args.len() {
        Ok(true)
    } else {
        match &ty.0.kind {
            ExprKind::ForallE(dom, body, mb) => {
                let dom = expr::dup(dom);
                let body = expr::dup(body);
                let acc2 = expr_ops::cons_expr(&args[i], acc);
                if lic && prop_when::is_never(&mb.pw) {
                    iota_certs_i_aux(
                        mode, fuel, st, fe, depth, lic, &body, &acc2, args, i + 1,
                    )
                } else {
                    let dom2 = state_c::inst_list_m(st, &dom, acc, 0);
                    match infer_io(mode, fuel, st, fe, depth, &args[i]) {
                        Err(err) => Err(err),
                        Ok(ta) => match defeq(mode, fuel, st, fe, depth, &ta, &dom2) {
                            Err(err) => Err(err),
                            Ok(true) => iota_certs_i_aux(
                                mode, fuel, st, fe, depth, lic, &body, &acc2, args, i + 1,
                            ),
                            Ok(false) => Ok(false),
                        },
                    }
                }
            }
            ExprKind::Bvar(_) => {
                if acc.len() == 0 {
                    Ok(false)
                } else {
                    let ty2 = state_c::inst_list_m(st, ty, acc, 0);
                    iota_certs_i_aux(
                        mode, fuel, st, fe, depth, lic, &ty2, &Vec::new(), args, i,
                    )
                }
            }
            _ => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:195-199 iotaCertsI
/// con-leche: ConLeche/Kernel/Core.lean:828-860 iotaCerts
/// Certify a spine against a recursor telescope: the accumulator loop at the
/// empty accumulator and the first argument.
pub fn iota_certs_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    lic: bool,
    ty: &Expr,
    args: &Vec<Expr>,
) -> CheckM<bool> {
    iota_certs_i_aux(mode, fuel, st, fe, depth, lic, ty, &Vec::new(), args, 0)
}

/// con-leche: ConLeche/Cached/CoreC.lean:201-209 defEqListI
/// con-leche: ConLeche/Kernel/Core.lean:869-878 defEqList
/// Pairwise definitional equality of two spines.  The `i = 0` wrapper of the
/// index recursion below.
pub fn def_eq_list_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    xs: &Vec<Expr>,
    ys: &Vec<Expr>,
) -> CheckM<bool> {
    def_eq_list_i_from(mode, fuel, st, fe, depth, xs, ys, 0)
}

/// con-leche: ConLeche/Cached/CoreC.lean:201-209 defEqListI
/// con-leche: ConLeche/Kernel/Core.lean:869-878 defEqList
/// The index recursion behind `def_eq_list_i`: the cited `[], []` arm is
/// "both exhausted", the cons arm is "both in range", and the wildcard is
/// the length mismatch.
pub fn def_eq_list_i_from(
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
        match defeq(mode, fuel, st, fe, depth, &xs[i], &ys[i]) {
            Err(err) => Err(err),
            Ok(true) => def_eq_list_i_from(mode, fuel, st, fe, depth, xs, ys, i + 1),
            Ok(false) => Ok(false),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:220-222 piResidualM
/// con-leche: ConLeche/Cached/ExprOpsC.lean:785-787 piResidual
/// con-leche: ConLeche/Kernel/Core.lean:862-867 piResidual
/// `piResidualM`, the tenth `*M` wrapper: `pure (ExprC.piResidual e args)`.
/// It lives here, at its one call site, rather than in `state_c`, for the
/// reason `state_c`'s module note gives.  The wrapped operation is
/// `Cached/ExprOpsC`'s **bulk** form (task #26): one memoised pass that
/// peels the whole argument list and substitutes once, where
/// `core_k::pi_residual` — the cited `Core.lean` original, still ported and
/// still the spec — peels and instantiates one binder at a time.  Body is
/// `pure e`, hence no state parameter (task #14's rule 9).
pub fn pi_residual_m(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    expr_ops_c::pi_residual(e, args)
}

/// con-leche: ConLeche/Cached/CoreC.lean:211-221 iotaIndexOkI
/// con-leche: ConLeche/Kernel/Core.lean:880-896 iotaIndexOk
/// The canonical-index comparison of a firing ι redex: where the recursor
/// has indices (`rP < mI`) the residual of the constructor's telescope along
/// the major's spine must agree, past the `cnP` parameters, with the
/// recursor's index arguments.  At `mI = rP` there is nothing to compare.
pub fn iota_index_ok_i(
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
        match pi_residual_m(ty_ctor, margs) {
            Some(residual) => {
                let args = expr_ops::get_app_args(&residual);
                let rest = core_k::drop_exprs(&args, cn_p as usize);
                def_eq_list_i(mode, fuel, st, fe, depth, &rest, idx)
            }
            None => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:223-238 defeqSpineI
/// con-leche: ConLeche/Kernel/Core.lean:2350-2369 defeqSpine
/// Levels-and-spine congruence for two applications of the same stored
/// constant — the lazy delta *same-head short-circuit*.  A `false` verdict is
/// never final (the caller falls back to unfolding), so an inconclusive
/// level comparison simply answers `false` here.  The comparison is
/// `isEquivListLM`, i.e. through `eqvC`.
pub fn defeq_spine_i(
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
                    match state_c::is_equiv_list_l_m(st, us, us2) {
                        Some(true) => {
                            def_eq_list_i(mode, fuel, st, fe, depth, &args_a, &args_b)
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

/// con-leche: ConLeche/Cached/CoreC.lean:240-280 proofIrrelI
/// con-leche: ConLeche/Kernel/Core.lean:898-929 proofIrrel
/// Proof irrelevance certification: both sides' types whnf to the basis unit
/// type, or both sides' types' *sorts* are `Prop`.  Every inference here is
/// at the io grade (official's `is_def_eq_proof_irrel` runs `infer_type`,
/// always `infer_only`).  `isUnitLikeTyC` is `core_k::is_unit_like_ty`
/// through the index.
pub fn proof_irrel_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match whnf(mode, fuel, st, fe, depth, &ta) {
            Err(err) => Err(err),
            Ok(wta) => {
                if core_k::is_unit_like_ty(fe, &wta) {
                    match infer_io(mode, fuel, st, fe, depth, b) {
                        Err(err) => Err(err),
                        Ok(tb) => match whnf(mode, fuel, st, fe, depth, &tb) {
                            Err(err) => Err(err),
                            Ok(wtb) => Ok(core_k::is_unit_like_ty(fe, &wtb)),
                        },
                    }
                } else {
                    prop_legs_i(mode, fuel, st, fe, depth, &ta, b)
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:240-280 proofIrrelI
/// con-leche: ConLeche/Cached/CoreC.lean:328-354 propIrrelI
/// The two `Prop` legs both irrelevance twins end in, verbatim in the Lean
/// and therefore one function here: the type of `ta` whnfs to a sort that is
/// `Prop`, and so does the type of the type of `b`.  `ta` is the caller's
/// already-computed `inferIO a`.  Both comparisons are `isEquivLM`, i.e.
/// through `eqvC` — the memo the pure legs did not use.
pub fn prop_legs_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ta: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match infer_io(mode, fuel, st, fe, depth, ta) {
        Err(err) => Err(err),
        Ok(tta) => match whnf(mode, fuel, st, fe, depth, &tta) {
            Err(err) => Err(err),
            Ok(wtta) => match &wtta.0.kind {
                ExprKind::Sort(u_t) => {
                    let eq_a = state_c::is_equiv_l_m(st, u_t, &level::zero());
                    match core_k::lift_fueled(eq_a) {
                        Err(err) => Err(err),
                        Ok(ok_a) => match infer_io(mode, fuel, st, fe, depth, b) {
                            Err(err) => Err(err),
                            Ok(tb) => match infer_io(mode, fuel, st, fe, depth, &tb) {
                                Err(err) => Err(err),
                                Ok(ttb) => {
                                    match whnf(mode, fuel, st, fe, depth, &ttb) {
                                        Err(err) => Err(err),
                                        Ok(wttb) => match &wttb.0.kind {
                                            ExprKind::Sort(v_t) => {
                                                let eq_b = state_c::is_equiv_l_m(
                                                    st,
                                                    v_t,
                                                    &level::zero(),
                                                );
                                                match core_k::lift_fueled(eq_b) {
                                                    Err(err) => Err(err),
                                                    Ok(ok_b) => Ok(ok_a && ok_b),
                                                }
                                            }
                                            _ => Ok(false),
                                        },
                                    }
                                }
                            },
                        },
                    }
                }
                _ => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:328-354 propIrrelI
/// con-leche: ConLeche/Kernel/Core.lean:931-973 propIrrel
/// **The hoisted proof-irrelevance test**: the `Prop` branch of
/// `proof_irrel_i` alone, with the two head-symbol fast arms in front — the
/// "not a proof" arm (`prop_read::not_proof_fast` on either side refuses the
/// shortcut) and the "yes" arm (`prop_read::is_proof_fast` on both sides
/// answers `true`, the squash-regime licence).  Both fire in both modes, so
/// the twin takes no `CheckMode` in the Lean either.
pub fn prop_irrel_i(
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
        match infer_io(mode, fuel, st, fe, depth, a) {
            Err(err) => Err(err),
            Ok(ta) => prop_legs_i(mode, fuel, st, fe, depth, &ta, b),
        }
    }
}

// ---------------------------------------------------------------------------
// Structure eta (`CoreC.lean:356-541`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:356-367 projAppsFnI
/// con-leche: ConLeche/Kernel/Core.lean:1017-1027 etaProjs
/// The projection-*function* spine `[proj_0 targs b, …]`, built through
/// `mkAppNM`.  The cited `List Nat` argument is always `List.range nF`, so
/// the port takes the count and walks `j = 0 … nF - 1`.
pub fn proj_apps_fn_i(
    t: &Name,
    us2: &Vec<Level>,
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
        let h = expr::mk_const(env::proj_fn_name(t, j), env::levels_copy(us2));
        let spine = core_k::append_exprs(env::exprs_copy(targs), &core_k::expr_singleton(b));
        out.push(state_c::mk_app_n_m(h, &spine));
        proj_apps_fn_i(t, us2, targs, b, n_f, j + 1, out)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:369-376 projNodesI
/// con-leche: ConLeche/Kernel/Core.lean:1017-1027 etaProjs
/// The `.proj T i b` spine — the tower spelling.
pub fn proj_nodes_i(t: &Name, b: &Expr, n_f: u64, j: u64, out: Vec<Expr>) -> Vec<Expr> {
    if j >= n_f {
        out
    } else {
        let mut out = out;
        out.push(expr::proj(name::dup(t), j, expr::dup(b)));
        proj_nodes_i(t, b, n_f, j + 1, out)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:378-386 projAppsI
/// con-leche: ConLeche/Kernel/Core.lean:1017-1027 etaProjs
/// The fabricated projections of a structure-eta spine: the tower spelling
/// at an all-tower slot family (`towerSlotsAllF` through the index), the
/// projection-function spelling otherwise.
///
/// Deviation: the cited `(Tn T : Name)` pair is one parameter here.  The two
/// are the same name at every call site (`let Tn ← pure T`) — the retired
/// arena's interned/raw split, which con-leche's task #198 collapsed but
/// left in the signatures.
pub fn proj_apps_i(
    fe: &FEnv,
    t: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
    b: &Expr,
    n_f: u64,
) -> Vec<Expr> {
    if fenv::tower_slots_all_f(fe, t, n_f) {
        proj_nodes_i(t, b, n_f, 0, Vec::new())
    } else {
        proj_apps_fn_i(t, us2, targs, b, n_f, 0, Vec::new())
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:388-405 structEtaProjCertsI
/// con-leche: ConLeche/Kernel/Core.lean:975-998 structEtaProjCerts
/// The per-projection telescope certificates of a structural eta
/// certification at a **projection-function** slot family: for every field
/// index the installed projection function's telescope — read through
/// `constTyAtM`, i.e. the `constTyAt` memo — is certified against the type's
/// arguments and the stuck side.  A tower-backed family has no per-field
/// telescope and needs no certificate (the caller decides).
pub fn struct_eta_proj_certs_i(
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
    struct_eta_proj_certs_i_from(mode, fuel, st, fe, depth, t, us2, targs, b, lps_t, n_f, 0)
}

/// con-leche: ConLeche/Cached/CoreC.lean:388-405 structEtaProjCertsI
/// con-leche: ConLeche/Kernel/Core.lean:975-998 structEtaProjCerts
/// The index recursion behind `struct_eta_proj_certs_i`.
pub fn struct_eta_proj_certs_i_from(
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
        match core_k::rec_probe(fe, &env::proj_fn_name(t, j)) {
            Some((cvp, _, _, _)) => {
                if prop_when::names_beq(&cvp.level_params, lps_t)
                    && expr_ops::strip_pis((targs.len() as u64) + 1, &cvp.ty).is_some()
                {
                    match state_c::const_ty_at_m(st, fe, &env::proj_fn_name(t, j), us2) {
                        Err(err) => Err(err),
                        Ok(pty) => {
                            let spine = core_k::append_exprs(
                                env::exprs_copy(targs),
                                &core_k::expr_singleton(b),
                            );
                            match iota_certs_i(mode, fuel, st, fe, depth, false, &pty, &spine)
                            {
                                Err(err) => Err(err),
                                Ok(true) => struct_eta_proj_certs_i_from(
                                    mode, fuel, st, fe, depth, t, us2, targs, b, lps_t, n_f,
                                    j + 1,
                                ),
                                Ok(false) => Ok(false),
                            }
                        }
                    }
                } else {
                    Ok(false)
                }
            }
            None => Ok(false),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:407-473 structEtaCertWithI
/// con-leche: ConLeche/Kernel/Core.lean:1029-1101 structEtaCertWith
/// The structure-eta certificate against a *given* weak-head-normal type of
/// the stuck side.  `a` is a fully applied constructor of an eta-capable
/// structure, `b` inhabits that structure type, the constructor's parameters
/// are the type's arguments, and every field is the corresponding installed
/// projection applied to `b`.
///
/// The syntactic conjunction block is `core_k::struct_eta_shape_ok` — the
/// twin's is character-for-character the spec's — so that the state-touching
/// steps below it read in sequence.
pub fn struct_eta_cert_with_i(
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
        ExprKind::Const(c, us) => match core_k::ctor_probe(fe, c) {
            Some((cvc, cn_p, cn_f)) => {
                let aargs = expr_ops::get_app_args(a);
                if aargs.len() as u64 != cn_p + cn_f {
                    Ok(false)
                } else {
                    let ftb = expr_ops::get_app_fn(wtb);
                    match &ftb.0.kind {
                        ExprKind::Const(t, us2) => match core_k::ind_probe(fe, t) {
                            Some((cvt, caps)) => {
                                let targs = expr_ops::get_app_args(wtb);
                                if core_k::struct_eta_shape_ok(
                                    fe, c, us2, &targs, &cvc, &cvt, &caps, t,
                                ) {
                                    struct_eta_cert_steps_i(
                                        mode, fuel, st, fe, depth, c, us, us2, &aargs,
                                        &targs, b, &cvc, &cvt, &caps, t,
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

/// con-leche: ConLeche/Cached/CoreC.lean:407-473 structEtaCertWithI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// The certificate's state-touching steps, in the cited order: the level
/// lists are equivalent (`isEquivListLM`, through `eqvC`), the type
/// application is certified against the type former's telescope (read
/// through `constTyAtM`), the per-slot certificates run at a
/// projection-function family (a tabled one has none), the constructor's
/// parameters are the type's arguments, the TT-lane synthetic-spine
/// certificate runs at `mode.ttChecks`, and the fields are the fabricated
/// projections.
///
/// **This is where the twin differs from the spec body beyond the swaps**:
/// the type-former telescope certificate and the per-slot ones are
/// *certificate families* — official's `try_eta_struct_core` runs neither —
/// so both sit under `certAtI mode`, spelled here as `env::certs(mode)` (the
/// module note's deviation 5).  `Core.lean`'s `structEtaCertWith` runs them
/// unconditionally.
pub fn struct_eta_cert_steps_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
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
    let eqv = state_c::is_equiv_list_l_m(st, us, us2);
    match core_k::lift_fueled(eqv) {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let tele = if env::certs(mode) {
                match state_c::const_ty_at_m(st, fe, t, us2) {
                    Err(err) => Err(err),
                    Ok(tty) => iota_certs_i(mode, fuel, st, fe, depth, false, &tty, targs),
                }
            } else {
                Ok(true)
            };
            match tele {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => {
                    let slots = if env::certs(mode) {
                        if fenv::tower_slots_all_f(fe, t, caps.eta_fields) {
                            Ok(true)
                        } else {
                            struct_eta_proj_certs_i(
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
                        }
                    } else {
                        Ok(true)
                    };
                    match slots {
                        Err(err) => Err(err),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            let params = expr_ops::take_exprs(aargs, caps.eta_params as usize);
                            match def_eq_list_i(mode, fuel, st, fe, depth, &params, targs) {
                                Err(err) => Err(err),
                                Ok(false) => Ok(false),
                                Ok(true) => struct_eta_cert_fields_i(
                                    mode, fuel, st, fe, depth, c, us, us2, aargs, targs, b,
                                    cvc, caps, t,
                                ),
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:407-473 structEtaCertWithI
/// The last two steps: the TT-lane synthetic-spine certification (con-leche's
/// task #137, skipped unless `mode.ttChecks` — a literal `false` at both
/// shipped cores, so this arm is dead but ported) and the field comparison
/// against `proj_apps_i`.  The constructor's own type is read through
/// `constTyAtM` inside the TT arm, which is where the Lean reads it.
pub fn struct_eta_cert_fields_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    us: &Vec<Level>,
    us2: &Vec<Level>,
    aargs: &Vec<Expr>,
    targs: &Vec<Expr>,
    b: &Expr,
    _cvc: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
) -> CheckM<bool> {
    let projs = proj_apps_i(fe, t, us2, targs, b, caps.eta_fields);
    let tt = if env::tt_checks(mode) {
        match state_c::const_ty_at_m(st, fe, c, us) {
            Err(err) => Err(err),
            Ok(cty) => {
                let spine = core_k::append_exprs(env::exprs_copy(targs), &projs);
                iota_certs_i(mode, fuel, st, fe, depth, false, &cty, &spine)
            }
        }
    } else {
        Ok(true)
    };
    match tt {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let fields = core_k::drop_exprs(aargs, caps.eta_params as usize);
            def_eq_list_i(mode, fuel, st, fe, depth, &fields, &projs)
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:475-484 structEtaCertI
/// con-leche: ConLeche/Kernel/Core.lean:1116-1139 structEtaCert
/// Structural eta certification for a stored eta-capable structure, with the
/// constructor-shape test **first** (the divergence audit's D13):
/// `etaCtorShapeC` reads `a`'s head and arity syntactically and nothing is
/// inferred unless they fit.
pub fn struct_eta_cert_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    if core_k::eta_ctor_shape(fe, a) {
        match infer_io(mode, fuel, st, fe, depth, b) {
            Err(err) => Err(err),
            Ok(tb) => match whnf(mode, fuel, st, fe, depth, &tb) {
                Err(err) => Err(err),
                Ok(wtb) => struct_eta_cert_with_i(mode, fuel, st, fe, depth, a, b, &wtb),
            },
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:486-512 structUnitCertI
/// con-leche: ConLeche/Kernel/Core.lean:1141-1169 structUnitCert
/// Unit-likeness certification: `a` and `b` inhabit the same stored
/// unit-like family (the types are definitionally equal and the type
/// application is certified against the family's telescope), so their values
/// coincide by the stored unit law.
pub fn struct_unit_cert_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match whnf(mode, fuel, st, fe, depth, &ta) {
            Err(err) => Err(err),
            Ok(wta) => {
                let f = expr_ops::get_app_fn(&wta);
                match &f.0.kind {
                    ExprKind::Const(t, us2) => match core_k::ind_probe(fe, t) {
                        Some((cvt, caps)) => {
                            let targs = expr_ops::get_app_args(&wta);
                            if core_k::unit_shape_ok(t, us2, &targs, &cvt, &caps) {
                                struct_unit_steps_i(
                                    mode, fuel, st, fe, depth, &wta, b, t, us2, &targs,
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

/// con-leche: ConLeche/Cached/CoreC.lean:486-512 structUnitCertI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// The state-touching tail: `b`'s reduced type is definitionally equal to
/// `a`'s, and then — **as a certificate family**, `certAtI mode` (official's
/// `is_def_eq_unit_like` stops at the defeq above) — the type application is
/// certified against the family's telescope, read through `constTyAtM`.
/// `Core.lean`'s `structUnitCert` runs that certificate unconditionally.
pub fn struct_unit_steps_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    wta: &Expr,
    b: &Expr,
    t: &Name,
    us2: &Vec<Level>,
    targs: &Vec<Expr>,
) -> CheckM<bool> {
    match infer_io(mode, fuel, st, fe, depth, b) {
        Err(err) => Err(err),
        Ok(tb) => match whnf(mode, fuel, st, fe, depth, &tb) {
            Err(err) => Err(err),
            Ok(wtb) => match defeq(mode, fuel, st, fe, depth, wta, &wtb) {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => {
                    if env::certs(mode) {
                        match state_c::const_ty_at_m(st, fe, t, us2) {
                            Err(err) => Err(err),
                            Ok(tty) => {
                                iota_certs_i(mode, fuel, st, fe, depth, false, &tty, targs)
                            }
                        }
                    } else {
                        Ok(true)
                    }
                }
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:514-533 etaCertI
/// con-leche: ConLeche/Kernel/Core.lean:1171-1196 etaCert
/// Eta certification for a one-sided λ against a stuck term `b`: `b`'s type
/// whnfs to a `∀` whose domain is defeq to the λ's, and the λ's body is
/// pointwise the application of `b`.  The prop-ness annotations are compared
/// **last** (con-leche's task #161), so a mismatch fires only on an otherwise
/// successful η certification.  The body is opened with `inst1M`.
pub fn eta_cert_i(
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
    match infer_io(mode, fuel, st, fe, depth, b) {
        Err(err) => Err(err),
        Ok(tb) => match whnf(mode, fuel, st, fe, depth, &tb) {
            Err(err) => Err(err),
            Ok(wtb) => match &wtb.0.kind {
                ExprKind::ForallE(ty2, _, m2) => {
                    let ty2 = expr::dup(ty2);
                    let pw2 = prop_when::dup(&m2.pw);
                    match defeq(mode, fuel, st, fe, depth, &ty2, ty1) {
                        Err(err) => Err(err),
                        Ok(false) => Ok(false),
                        Ok(true) => {
                            eta_cert_body_i(mode, fuel, st, fe, depth, ty1, body1, m1, b, &pw2)
                        }
                    }
                }
                _ => Ok(false),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:514-533 etaCertI
/// con-leche: ConLeche/Kernel/Core.lean:1171-1196 etaCert
/// The pointwise comparison and the annotation check of `eta_cert_i`, once
/// the domains have matched.
pub fn eta_cert_body_i(
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
    let lhs = state_c::inst1_m(body1, &v, 0);
    let rhs = expr::app(expr::dup(b), expr::dup(&v));
    match defeq(mode, fuel, st, fe, depth + 1, &lhs, &rhs) {
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

/// con-leche: ConLeche/Cached/CoreC.lean:535-541 stuckIrrelI
/// con-leche: ConLeche/Kernel/Core.lean:1198-1208 stuckIrrel
/// The fallback for structurally distinct stuck terms: structural eta in
/// either direction, unit-likeness, else proof irrelevance.
pub fn stuck_irrel_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match struct_eta_cert_i(mode, fuel, st, fe, depth, a, b) {
        Err(err) => Err(err),
        Ok(true) => Ok(true),
        Ok(false) => match struct_eta_cert_i(mode, fuel, st, fe, depth, b, a) {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => match struct_unit_cert_i(mode, fuel, st, fe, depth, a, b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => proof_irrel_i(mode, fuel, st, fe, depth, a, b),
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The stuck-major rescue and ι (`CoreC.lean:543-853`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Cached/ExprOpsC.lean:679 wscopedB
/// con-leche: ConLeche/Cached/ExprOpsC.lean:747-748 leafGuard
/// The **cached tier's** scope guard, run by all three rescue branches on
/// their fabrication: the cited
/// `ExprC.wscopedB depth fab && ExprC.looseBVarsBounded 0 fab &&
/// ExprC.leafGuard fab major`, in that order.
///
/// Every member here is `ExprOpsC`'s, i.e. the memoized twin:
/// `expr_ops_c::wscoped_b` is one memoized DAG walk where the pure
/// `expr_ops::wscoped_b` is a tree walk, and `expr_ops_c::leaf_guard` is the
/// cited `leafGuard` — `hasFvar`-short-circuited, the base leaves collected
/// through a `seen` map and the subset test itself memoized — where the pure
/// tier compares two `fvarLeaves` lists elementwise.
/// `looseBVarsBounded` is the `O(1)` `bvarB` read in both tiers, so the pure
/// spelling is the cited one.
///
/// Task #32: the three branches called `core_k::fab_scope_ok`, the **pure**
/// tier's guard (`Kernel/Core.lean`'s `majorToCtor`), which is a memo policy
/// the cited cached code does not have (DESIGN.md §3.1).  On the `core`
/// corpus that mistake was 26% of the run's instructions
/// (`core_k::fab_scope_ok` 13.5%, `expr_ops::fvar_leaves_go` 12.7%);
/// `core_k::fab_scope_ok` stays where it is as the pure tier's port.
pub fn fab_scope_ok_i(fab: &Expr, major: &Expr, depth: u64) -> bool {
    if !expr_ops_c::wscoped_b(depth, fab) {
        false
    } else if !expr_ops::loose_bvars_bounded(0, fab) {
        false
    } else {
        expr_ops_c::leaf_guard(fab, major)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure` in
/// the official kernel): a recursor's major premise that does not whnf to a
/// constructor application may still be *replaced* by one.  An uncertified
/// major stays put — sound, the reduction simply stays stuck.
///
/// This function is the cited cheap syntactic dispatch (a single-rule
/// recursor whose rule carries the matching install-time rescue bit); the
/// three branches are `major_to_ctor_k_i`, `major_to_ctor_eta_i` and
/// `major_to_ctor_and_i`, one per cited `if`.  `isCtorAppC` is
/// `core_k::is_ctor_app` through the index.
///
/// Deviation: the cited `_recName : Name` parameter is unused in the Lean
/// too (hence its underscore), so the port drops it and `prepare_major_i`
/// passes one argument fewer.
pub fn major_to_ctor_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rules: &Vec<RecRule>,
    major: &Expr,
) -> CheckM<Expr> {
    if core_k::is_ctor_app(fe, major) {
        Ok(expr::dup(major))
    } else if rules.len() != 1 {
        Ok(expr::dup(major))
    } else {
        let rl: &RecRule = &rules[0];
        match core_k::ctor_probe(fe, &rl.ctor) {
            Some((cvj, cn_p, _)) => {
                let res = expr_ops::pi_result(&cvj.ty);
                let head = expr_ops::get_app_fn(&res);
                match &head.0.kind {
                    ExprKind::Const(t, _) => match core_k::ind_probe(fe, t) {
                        Some((cvt, caps)) => {
                            if rl.k {
                                major_to_ctor_k_i(
                                    mode, fuel, st, fe, depth, rl, &cvj, cn_p, t, major,
                                )
                            } else if rl.eta {
                                major_to_ctor_eta_i(
                                    mode, fuel, st, fe, depth, rl, &cvt, &caps, t, major,
                                )
                            } else if name::beq(t, &basis_names::and_name()) {
                                major_to_ctor_and_i(
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

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// The **K branch**: for a K-flagged inductive proposition the
/// parameters-only application of the single constructor is fabricated from
/// the major's type and certified by the synthetic-spine telescope (a
/// certificate family, `certAtI mode`), the official type check (`tmaj ≡
/// infer fab`, which runs in *both* modes) and proof irrelevance (again a
/// family).  The constructor's type is read through `constTyAtM`.
pub fn major_to_ctor_k_i(
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
    match infer_io_whnf_i(mode, fuel, st, fe, depth, major) {
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
                        let h = expr::mk_const(name::dup(&rl.ctor), env::levels_copy(ust));
                        let fab = state_c::mk_app_n_m(h, &params);
                        if !fab_scope_ok_i(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cert = if env::certs(mode) {
                                match state_c::const_ty_at_m(st, fe, &rl.ctor, ust) {
                                    Err(err) => Err(err),
                                    Ok(cty) => iota_certs_i(
                                        mode, fuel, st, fe, depth, false, &cty, &params,
                                    ),
                                }
                            } else {
                                Ok(true)
                            };
                            match cert {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => k_type_and_irrel_i(
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

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// The K branch's last two certificates, shared with the `And` branch: the
/// fabrication's type against the major's (for `Eq` this is the endpoint
/// condition; it runs in both modes) and then proof irrelevance as the
/// soundness certificate — a certificate family, so `certAtI mode`.
pub fn k_type_and_irrel_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    tmaj: &Expr,
    fab: &Expr,
    major: &Expr,
) -> CheckM<Expr> {
    match infer_io(mode, fuel, st, fe, depth, fab) {
        Err(err) => Err(err),
        Ok(tfab) => match defeq(mode, fuel, st, fe, depth, tmaj, &tfab) {
            Err(err) => Err(err),
            Ok(false) => Ok(expr::dup(major)),
            Ok(true) => {
                let irrel = if env::certs(mode) {
                    proof_irrel_i(mode, fuel, st, fe, depth, fab, major)
                } else {
                    Ok(true)
                };
                match irrel {
                    Err(err) => Err(err),
                    Ok(true) => Ok(expr::dup(fab)),
                    Ok(false) => Ok(expr::dup(major)),
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// `r.whnf depth (← r.inferIO depth major)` — the major's reduced type,
/// which all three rescue branches open with.
pub fn infer_io_whnf_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match infer_io(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(t) => whnf(mode, fuel, st, fe, depth, &t),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// The **η branch**: for an eta-capable structure the constructor of the
/// major's projections is fabricated (`projAppsI`, through `mkAppNM`) and
/// certified by the structure-eta certificate.  The provably-nonzero test is
/// the *instantiated* one (con-leche's task #61).  The fabricated spine's
/// telescope certificate is a family (`certAtI mode`); the 0-field proof-
/// irrelevance rescue behind it is not, in the Lean or here.
pub fn major_to_ctor_eta_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rl: &RecRule,
    cvt: &ConstantVal,
    caps: &IndCaps,
    t: &Name,
    major: &Expr,
) -> CheckM<Expr> {
    match infer_io_whnf_i(mode, fuel, st, fe, depth, major) {
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
                    } else if !core_k::caps_never_zero(&cvt.level_params, ust, caps) {
                        Ok(expr::dup(major))
                    } else {
                        let projs =
                            proj_apps_i(fe, t, ust, &targs, major, caps.eta_fields);
                        let spine = core_k::append_exprs(env::exprs_copy(&targs), &projs);
                        let h =
                            expr::mk_const(name::dup(&caps.eta_ctor), env::levels_copy(ust));
                        let fab = state_c::mk_app_n_m(h, &spine);
                        if !fab_scope_ok_i(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cert = if env::certs(mode) {
                                match state_c::const_ty_at_m(st, fe, &rl.ctor, ust) {
                                    Err(err) => Err(err),
                                    Ok(cty) => iota_certs_i(
                                        mode, fuel, st, fe, depth, false, &cty, &spine,
                                    ),
                                }
                            } else {
                                Ok(true)
                            };
                            match cert {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => eta_rescue_certs_i(
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

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Kernel/Core.lean:1274-1456 majorToCtor
/// The η branch's certificate: the structure-eta certificate against the
/// major's own reduced type, with the **0-field rescue** for the pinned
/// basis `PUnit` behind it (the generic certificate excludes reserved names;
/// the fabrication is the bare constructor, certified by proof irrelevance's
/// unit-likeness branch).
pub fn eta_rescue_certs_i(
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
    match struct_eta_cert_with_i(mode, fuel, st, fe, depth, fab, major, tmaj) {
        Err(err) => Err(err),
        Ok(true) => Ok(expr::dup(fab)),
        Ok(false) => {
            if caps.eta_fields == 0 {
                match proof_irrel_i(mode, fuel, st, fe, depth, fab, major) {
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

/// con-leche: ConLeche/Cached/CoreC.lean:543-670 majorToCtorI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// **THE `And`-ONLY η RESCUE** (con-leche's user ruling: `And` and nothing
/// else).  `And.rec F h` at a stuck PROOF `h` fires through the fabrication
/// `And.intro a b (.proj And 0 h) (.proj And 1 h)` — the projections are
/// `projNodesI`'s tower nodes — certified the K branch's way.
pub fn major_to_ctor_and_i(
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
    match infer_io_whnf_i(mode, fuel, st, fe, depth, major) {
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
                    } else if !core_k::and_rescue_slots(fe, &rl.ctor, cn_p, ust) {
                        Ok(expr::dup(major))
                    } else {
                        let projs = proj_nodes_i(t, major, 2, 0, Vec::new());
                        let spine = core_k::append_exprs(env::exprs_copy(&targs), &projs);
                        let h = expr::mk_const(name::dup(&rl.ctor), env::levels_copy(ust));
                        let fab = state_c::mk_app_n_m(h, &spine);
                        if !fab_scope_ok_i(&fab, major, depth) {
                            Ok(expr::dup(major))
                        } else {
                            let cert = if env::certs(mode) {
                                match state_c::const_ty_at_m(st, fe, &rl.ctor, ust) {
                                    Err(err) => Err(err),
                                    Ok(cty) => iota_certs_i(
                                        mode, fuel, st, fe, depth, false, &cty, &spine,
                                    ),
                                }
                            } else {
                                Ok(true)
                            };
                            match cert {
                                Err(err) => Err(err),
                                Ok(false) => Ok(expr::dup(major)),
                                Ok(true) => k_type_and_irrel_i(
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

/// con-leche: ConLeche/Cached/CoreC.lean:672-681 litMajorToCtorI
/// con-leche: ConLeche/Kernel/Core.lean:1458-1470 litMajorToCtor
/// Convert a literal major premise to constructor form: a `Nat` literal one
/// layer (`litToCtorIfNatI`, which is `core_k::lit_to_ctor_if_nat` — the
/// twin's body is `pure` of the spec's); a `String` literal to its *reduced*
/// constructor form, because `String.ofList` is a definition.
pub fn lit_major_to_ctor_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match &e.0.kind {
        ExprKind::Lit(Literal::StrVal(s)) => {
            if core_k::str_lit_supported(fe) {
                let c = core_k::str_lit_to_constructor(s);
                whnf(mode, fuel, st, fe, depth, &c)
            } else {
                Ok(expr::dup(e))
            }
        }
        _ => Ok(core_k::lit_to_ctor_if_nat(fe, e)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:683-692 projLitToCtorI
/// con-leche: ConLeche/Kernel/Core.lean:1472-1486 projLitToCtor
/// Convert a string-literal projection scrutinee to its *reduced*
/// constructor form.  Only `String` literals; anything else passes through
/// unchanged (this is where it differs from `lit_major_to_ctor_i`, which
/// also packs a `Nat` literal).
pub fn proj_lit_to_ctor_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match &e.0.kind {
        ExprKind::Lit(Literal::StrVal(s)) => {
            if core_k::str_lit_supported(fe) {
                let c = core_k::str_lit_to_constructor(s);
                whnf(mode, fuel, st, fe, depth, &c)
            } else {
                Ok(expr::dup(e))
            }
        }
        _ => Ok(expr::dup(e)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:694-708 prepareMajorI
/// con-leche: ConLeche/Kernel/Core.lean:1621-1658 prepareMajor
/// The major premise's preparation in the official kernel's order: at a
/// K-flagged recursor the K rescue runs on the **raw** major (it reads only
/// the major's *type*) and only then is the major head-normalized and its
/// literal converted; elsewhere the major is head-normalized first, its
/// literal converted, and the structure-eta rescue tried on the reduct.
pub fn prepare_major_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    rules: &Vec<RecRule>,
    major: &Expr,
) -> CheckM<Expr> {
    if core_k::rec_rule_k(rules) {
        match major_to_ctor_i(mode, fuel, st, fe, depth, rules, major) {
            Err(err) => Err(err),
            Ok(major_k) => match whnf(mode, fuel, st, fe, depth, &major_k) {
                Err(err) => Err(err),
                Ok(major0) => lit_major_to_ctor_i(mode, fuel, st, fe, depth, &major0),
            },
        }
    } else {
        match whnf(mode, fuel, st, fe, depth, major) {
            Err(err) => Err(err),
            Ok(major0) => match lit_major_to_ctor_i(mode, fuel, st, fe, depth, &major0) {
                Err(err) => Err(err),
                Ok(major1) => major_to_ctor_i(mode, fuel, st, fe, depth, rules, &major1),
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:710-720 pinArgsI
/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The nested-rule pin instantiations: each stored pin is level-instantiated
/// (`instLevelParamsM`) and then substituted at the recursor's
/// leading-argument spine (`instSpineM`).  The cited `List Expr` argument is
/// walked by index.
pub fn pin_args_i(
    lps: &Vec<Name>,
    us: &Vec<Level>,
    args: &Vec<Expr>,
    t: u64,
    pins: &Vec<Expr>,
    i: usize,
    out: Vec<Expr>,
) -> Vec<Expr> {
    if i >= pins.len() {
        out
    } else {
        let mut out = out;
        let p = state_c::inst_level_params_m(lps, us, &pins[i]);
        out.push(state_c::inst_spine_m(args, t, &p));
        pin_args_i(lps, us, args, t, pins, i + 1, out)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// `cvjLps.map Level.param`, the level trees `substLevelTreesM` substitutes
/// in the canonical (`.plain`) arm.  §3.4 forbids closures, so the `map` is
/// this index recursion.
pub fn params_as_levels(ps: &Vec<Name>, i: usize, out: Vec<Level>) -> Vec<Level> {
    if i >= ps.len() {
        out
    } else {
        let mut out = out;
        out.push(level::param(name::dup(&ps[i])));
        params_as_levels(ps, i + 1, out)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:722-726 iotaNumArgs
/// The length of an application spine, without building its argument list.
pub fn iota_num_args(e: &Expr, n: u64) -> u64 {
    match &e.0.kind {
        ExprKind::App(f, _) => iota_num_args(f, n + 1),
        _ => n,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:728-741 iotaArityOk
/// The cited `some (.recInfo cv mI _ _)` destructuring, as an owning probe of
/// the two numbers the guard reads: the major's index and the recursor's
/// level-parameter count.  `core_k::rec_probe` would copy the rule list,
/// which this guard never looks at.
pub fn rec_arity_probe(fe: &FEnv, c: &Name) -> Option<(u64, usize)> {
    match fenv::find(fe, c) {
        Some(ci) => match ci {
            env::ConstantInfo::RecInfo(cv, m_i, _, _) => Some((*m_i, cv.level_params.len())),
            _ => None,
        },
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:728-741 iotaArityOk
/// **The arity pre-check of the ι step**: `iota_rec_i` returns `None` unless
/// the head is a stored recursor applied to exactly `majorIdx + 1` arguments
/// with the recursor's own number of levels.  The whnf spine loop asks this
/// before every ι attempt, which is allocation-free where the ι step's own
/// guard would first materialise the argument list.  No `Core.lean`
/// counterpart — the pure `whnfCoreBody` has no spine loop to ask.
pub fn iota_arity_ok(fe: &FEnv, e: &Expr) -> bool {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(c, us) => match rec_arity_probe(fe, c) {
            Some(p) => iota_num_args(e, 0) == p.0 + 1 && us.len() == p.1,
            None => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// One iota step: the expression is a stored recursor applied to exactly its
/// telescope, the major premise whnfs to a fully applied constructor with a
/// matching rule, and the spine is certified against the recursor's own
/// (pinned, annotated) type.  Over-application is handled by the outer app
/// loop (`whnf_app_i`).
///
/// This function is the cited head/arity dispatch; `iota_rec_rule_i` matches
/// the prepared major against a rule and `iota_rec_checks_i` runs the
/// cascade.
pub fn iota_rec_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Option<Expr>> {
    let f = expr_ops::get_app_fn(e);
    match &f.0.kind {
        ExprKind::Const(c, us) => match core_k::rec_probe(fe, c) {
            Some((cv, m_i, r_p, rules)) => {
                let args = expr_ops::get_app_args(e);
                if (args.len() as u64) == m_i + 1 && us.len() == cv.level_params.len() {
                    let raw = core_k::get_d_expr(&args, m_i);
                    match prepare_major_i(mode, fuel, st, fe, depth, &rules, &raw) {
                        Err(err) => Err(err),
                        Ok(major) => iota_rec_rule_i(
                            mode, fuel, st, fe, depth, c, &cv, m_i, r_p, &rules, us, &args,
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

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The prepared major's head must be a stored constructor with a matching
/// rule at a matching spine length; a matched **inert** rule is a positive
/// detection of an unsupported feature and declines here (staying silently
/// stuck would surface as a spurious *reject* downstream).
pub fn iota_rec_rule_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
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
        114, 32, 97, 32, 110, 101, 115, 116, 101, 100, 32, 97, 117, 120, 105, 108, 105, 97, 114,
        121, 32, 114, 101, 99, 117, 114, 115, 111, 114, 32, 114, 117, 108, 101,
    ];
    let fj = expr_ops::get_app_fn(major);
    match &fj.0.kind {
        ExprKind::Const(cj, usj) => match core_k::ctor_probe(fe, cj) {
            Some((cvj, _, _)) => match core_k::rules_find(rules, cj, 0) {
                Some(k) => {
                    let rl = env::rec_rule_dup(&rules[k]);
                    let margs = expr_ops::get_app_args(major);
                    if (margs.len() as u64) != rl.ctor_params + rl.nfields {
                        Ok(None)
                    } else if core_k::fire_is_inert(&rl.fire) {
                        Err(core_types::not_implemented(core_types::code_points(&M)))
                    } else {
                        iota_rec_checks_i(
                            mode, fuel, st, fe, depth, c, cj, cv, &cvj, m_i, r_p, &rl, us,
                            usj, args, &margs, major,
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

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The comparand levels of a firing rule: for a canonical (`.plain`) rule
/// the constructor's level parameters, linked to the recursor's by name; for
/// a certified nested rule the stored level trees.  Both go through
/// `substLevelTreesM`, which is where `Core.lean`'s `recFireComparands`
/// spells its own `map`.
pub fn iota_cmp_levels_i(
    rl: &RecRule,
    lps: &Vec<Name>,
    us: &Vec<Level>,
    cvj_lps: &Vec<Name>,
) -> Vec<Level> {
    match &rl.fire {
        RecRuleFire::Nested(lvls, _) => state_c::subst_level_trees(lps, us, lvls),
        _ => {
            let ps = params_as_levels(cvj_lps, 0, Vec::new());
            state_c::subst_level_trees(lps, us, &ps)
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1660-1680 recFireComparands
/// The comparand parameters: the recursor's leading arguments for a
/// canonical rule, the `pinArgsI` instantiations for a nested one.
pub fn iota_cmp_args_i(
    rl: &RecRule,
    lps: &Vec<Name>,
    us: &Vec<Level>,
    args: &Vec<Expr>,
    r_p: u64,
) -> Vec<Expr> {
    match &rl.fire {
        RecRuleFire::Nested(_, pins) => {
            let pargs = expr_ops::take_exprs(args, r_p as usize);
            pin_args_i(
                lps,
                us,
                &pargs,
                expr_ops::sub_nat(r_p, 1),
                pins,
                0,
                Vec::new(),
            )
        }
        _ => expr_ops::take_exprs(args, rl.ctor_params as usize),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Cached/CoreC.lean:302-308 certUnlessI
/// The firing cascade's first two steps: the constructor's levels against
/// the rule's comparands (`isEquivListLM`, through `eqvC`), then the
/// parameter comparison — not run at all for a `.plain` rule the installing
/// route marked `paramsBlind`, and where it is run, `certUnlessI mode keep`
/// with `keep` true for a nested rule (the comparands ARE the pins) and for
/// a projection-function rule, a certificate family otherwise.
pub fn iota_rec_checks_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    cj: &Name,
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
    // both comparand lists are built before the level comparison, as the
    // cited `let cmpLvls ← …; let cmpArgs ← …` does; neither touches a memo
    // (`substLevelTreesM`, `instLevelParamsM` and `instSpineM` are all
    // state-free), so the order is unobservable and faithfulness is free.
    let cmp_lvls = iota_cmp_levels_i(rl, &cv.level_params, us, &cvj.level_params);
    let cmp_args = iota_cmp_args_i(rl, &cv.level_params, us, args, r_p);
    let eqv = state_c::is_equiv_list_l_m(st, usj, &cmp_lvls);
    match core_k::lift_fueled(eqv) {
        Err(err) => Err(err),
        Ok(false) => Ok(None),
        Ok(true) => {
            let pcmp = if env::rec_rule_compare_params(rl) {
                let keep = iota_params_keep_i(rl, c);
                if env::certs(mode) || keep {
                    let params = expr_ops::take_exprs(margs, rl.ctor_params as usize);
                    def_eq_list_i(mode, fuel, st, fe, depth, &params, &cmp_args)
                } else {
                    Ok(true)
                }
            } else {
                Ok(true)
            };
            match pcmp {
                Err(err) => Err(err),
                Ok(false) => Ok(None),
                Ok(true) => iota_rec_telescopes_i(
                    mode, fuel, st, fe, depth, c, cj, m_i, r_p, rl, us, usj, args, margs,
                    major,
                ),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// The `keep` argument of the parameter comparison's `certUnlessI`: a nested
/// rule, or a projection-function recursor.  Verdict-relevant in both cases,
/// so the comparison runs at every mode.
pub fn iota_params_keep_i(rl: &RecRule, c: &Name) -> bool {
    match &rl.fire {
        RecRuleFire::Nested(_, _) => true,
        _ => level::name_is_proj_fn_shape(c),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Cached/CoreC.lean:297-300 certAtI
/// **ONE certificate family**: the two instantiated types (read through
/// `constTyAtM`), the two *licensed* telescope runs and the canonical-index
/// comparison, all under `certAtI mode` — nothing here is read outside the
/// family, so the whole block is what `.trusted` omits and the types are
/// looked up only where a certificate consumes them.  Behind it the rule's
/// right-hand side comes from `ruleRhsAtM`, i.e. the `ruleRhsAt` memo, and
/// the reduct is built with `mkAppNM`.
pub fn iota_rec_telescopes_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    cj: &Name,
    m_i: u64,
    r_p: u64,
    rl: &RecRule,
    us: &Vec<Level>,
    usj: &Vec<Level>,
    args: &Vec<Expr>,
    margs: &Vec<Expr>,
    major: &Expr,
) -> CheckM<Option<Expr>> {
    let fam = if env::certs(mode) {
        iota_rec_family_i(
            mode, fuel, st, fe, depth, c, cj, m_i, r_p, rl, us, usj, args, margs, major,
        )
    } else {
        Ok(true)
    };
    match fam {
        Err(err) => Err(err),
        Ok(false) => Ok(None),
        Ok(true) => match state_c::rule_rhs_at_m(st, fe, c, cj, us) {
            Err(err) => Err(err),
            Ok(rhs) => {
                let fields = core_k::drop_exprs(margs, rl.ctor_params as usize);
                let spine =
                    core_k::append_exprs(expr_ops::take_exprs(args, r_p as usize), &fields);
                Ok(Some(state_c::mk_app_n_m(rhs, &spine)))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:743-838 iotaRecI
/// con-leche: ConLeche/Kernel/Core.lean:1682-1795 iotaRec
/// The certificate family itself: the recursor's telescope against the
/// non-major prefix plus the prepared major, the constructor's telescope
/// against the major's spine, and the canonical-index comparison (which
/// exists only where indices do).  Both telescope runs are *licensed* off
/// `mode.betaGate` — the same function the β site reads.
pub fn iota_rec_family_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    c: &Name,
    cj: &Name,
    m_i: u64,
    r_p: u64,
    rl: &RecRule,
    us: &Vec<Level>,
    usj: &Vec<Level>,
    args: &Vec<Expr>,
    margs: &Vec<Expr>,
    major: &Expr,
) -> CheckM<bool> {
    let lic = env::beta_gate(mode);
    let pre = expr_ops::take_exprs(args, m_i as usize);
    match state_c::const_ty_at_m(st, fe, c, us) {
        Err(err) => Err(err),
        Ok(rty) => {
            let rspine =
                core_k::append_exprs(env::exprs_copy(&pre), &core_k::expr_singleton(major));
            match iota_certs_i(mode, fuel, st, fe, depth, lic, &rty, &rspine) {
                Err(err) => Err(err),
                Ok(false) => Ok(false),
                Ok(true) => match state_c::const_ty_at_m(st, fe, cj, usj) {
                    Err(err) => Err(err),
                    Ok(cty) => {
                        match iota_certs_i(mode, fuel, st, fe, depth, lic, &cty, margs) {
                            Err(err) => Err(err),
                            Ok(false) => Ok(false),
                            Ok(true) => {
                                let idx = core_k::drop_exprs(&pre, r_p as usize);
                                iota_index_ok_i(
                                    mode,
                                    fuel,
                                    st,
                                    fe,
                                    depth,
                                    m_i,
                                    r_p,
                                    rl.ctor_params,
                                    &cty,
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

/// con-leche: ConLeche/Cached/CoreC.lean:840-848 projCertI
/// The cited `some (.ctorInfo _ _ _)` test, as its **own function** — task
/// #14's rule, and one of task #23's four Aeneas errors: a borrow taken from
/// the index, consumed into a scalar and then joined with a branch that
/// touches the state does not typecheck in Aeneas's model (*"Internal error,
/// please file an issue"*).  Inside a callee the borrow dies at the call
/// boundary.
pub fn is_ctor_stored_i(fe: &FEnv, c: &Name) -> bool {
    match fenv::find(fe, c) {
        Some(ci) => core_k::is_ctor_info(ci),
        None => false,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:840-848 projCertI
/// con-leche: ConLeche/Kernel/Core.lean:1808-1843 projCert
/// **The structural projection's certificate**: the redex `proj_i (C p⃗ x⃗)`
/// fires only after its constructor spine is certified against `C`'s stored
/// type (through `constTyAtM`) at the redex's own levels.  The spine is a
/// subterm of the subject, so the certificate is *licensed* like the ι slot's.
pub fn proj_cert_i(
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
    if is_ctor_stored_i(fe, c) {
        match state_c::const_ty_at_m(st, fe, c, us) {
            Err(err) => Err(err),
            Ok(cty) => iota_certs_i(mode, fuel, st, fe, depth, lic, &cty, args),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:850-853 projCertAtI
/// con-leche: ConLeche/Kernel/Core.lean:1845-1857 projCertAt
/// **The fire certificate as the mode runs it**: the verified core certifies
/// the constructor spine; the trusted core is the official kernel's
/// (`reduce_proj` reduces every constructor redex with no certificate), so
/// at `verified = false` the rule fires unconditionally.
pub fn proj_cert_at_i(
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
        proj_cert_i(mode, fuel, st, fe, depth, lic, c, us, args)
    } else {
        Ok(true)
    }
}

// ---------------------------------------------------------------------------
// Bulk beta and the head-normalization loop (`CoreC.lean:857-1009`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:857-900 whnfAppI
/// **Bulk-beta argument loop** (con-leche's task #50): consume the whole
/// application spine against the whnf'd head `v`.  A lambda head enters the
/// peel loop (first binder inline, which keeps the argument count
/// decreasing); other heads try ι with one more argument and otherwise
/// accumulate a stuck application — exactly the per-level `whnfCoreBody` app
/// clauses, but with the chained per-argument `instantiate1` of the beta path
/// replaced by **one bulk substitution per peeled group**.
///
/// Deviations: the cited `List ExprC` of remaining arguments is `args[i..]`
/// (`a` is `args[i]`, `rest` is `args[i + 1 ..]`, materialised by
/// `core_k::drop_exprs` only where the Lean materialises it too — the stuck
/// `mkAppNM` arms); and the head-normalization loop's continuation `k` is its
/// *step budget* `n`, so `k x` is `whnf_core_loop_i(…, n, x)` (task #18's
/// pattern 2, which is what `whnfCoreLoopI (n + 1)` passes).  No `Core.lean`
/// counterpart: the pure `whnfCoreBody` has no spine loop.
pub fn whnf_app_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    v: &Expr,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<Expr> {
    if i >= args.len() {
        Ok(expr::dup(v))
    } else {
        match &v.0.kind {
            ExprKind::Lam(ty, body, mb) => {
                let ty = expr::dup(ty);
                let body = expr::dup(body);
                if env::beta_skip(mode, &mb.pw) {
                    let acc = core_k::expr_singleton(&args[i]);
                    beta_peel_i(
                        mode, fuel, st, fe, depth, n, &body, &acc, args, i + 1,
                    )
                } else {
                    match infer_io(mode, fuel, st, fe, depth, &args[i]) {
                        Err(err) => Err(err),
                        Ok(ta) => match defeq(mode, fuel, st, fe, depth, &ta, &ty) {
                            Err(err) => Err(err),
                            Ok(true) => {
                                let acc = core_k::expr_singleton(&args[i]);
                                beta_peel_i(
                                    mode, fuel, st, fe, depth, n, &body, &acc, args, i + 1,
                                )
                            }
                            Ok(false) => {
                                let fa = expr::app(expr::dup(v), expr::dup(&args[i]));
                                let rest = core_k::drop_exprs(args, i + 1);
                                Ok(state_c::mk_app_n_m(fa, &rest))
                            }
                        },
                    }
                }
            }
            _ => {
                let fa = expr::app(expr::dup(v), expr::dup(&args[i]));
                let step = if iota_arity_ok(fe, &fa) {
                    iota_rec_i(mode, fuel, st, fe, depth, &fa)
                } else {
                    Ok(None)
                };
                match step {
                    Err(err) => Err(err),
                    Ok(Some(e2)) => {
                        match whnf_core_loop_i(mode, fuel, st, fe, depth, n, &e2) {
                            Err(err) => Err(err),
                            Ok(v2) => whnf_app_i(
                                mode, fuel, st, fe, depth, n, &v2, args, i + 1,
                            ),
                        }
                    }
                    Ok(None) => {
                        whnf_app_i(mode, fuel, st, fe, depth, n, &fa, args, i + 1)
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:902-938 betaPeelI
/// **Peel loop of `whnf_app_i`**: `t` is the raw (unsubstituted) lambda body
/// after the binders consumed so far, `acc` their arguments (innermost
/// first).  Each binder's argument certificate substitutes only the
/// *domain*; the body is substituted once, when peeling stops — and both
/// substitutions go through `instListM`, i.e. the `instC` memo.
///
/// Deviation: `acc` is a `Vec` grown at the front (`expr_ops::cons_expr`),
/// see the module note's point 7.
pub fn beta_peel_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    t: &Expr,
    acc: &Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<Expr> {
    if i >= args.len() {
        let e2 = state_c::inst_list_m(st, t, acc, 0);
        whnf_core_loop_i(mode, fuel, st, fe, depth, n, &e2)
    } else {
        match &t.0.kind {
            ExprKind::Lam(ty, body, mb) => {
                let ty = expr::dup(ty);
                let body = expr::dup(body);
                if env::beta_skip(mode, &mb.pw) {
                    let acc2 = expr_ops::cons_expr(&args[i], acc);
                    beta_peel_i(
                        mode, fuel, st, fe, depth, n, &body, &acc2, args, i + 1,
                    )
                } else {
                    let ty2 = state_c::inst_list_m(st, &ty, acc, 0);
                    match infer_io(mode, fuel, st, fe, depth, &args[i]) {
                        Err(err) => Err(err),
                        Ok(ta) => match defeq(mode, fuel, st, fe, depth, &ta, &ty2) {
                            Err(err) => Err(err),
                            Ok(true) => {
                                let acc2 = expr_ops::cons_expr(&args[i], acc);
                                beta_peel_i(
                                    mode, fuel, st, fe, depth, n, &body, &acc2, args, i + 1,
                                )
                            }
                            Ok(false) => {
                                let f2 = state_c::inst_list_m(st, t, acc, 0);
                                let fa = expr::app(f2, expr::dup(&args[i]));
                                let rest = core_k::drop_exprs(args, i + 1);
                                Ok(state_c::mk_app_n_m(fa, &rest))
                            }
                        },
                    }
                }
            }
            _ => {
                let e2 = state_c::inst_list_m(st, t, acc, 0);
                match whnf_core_loop_i(mode, fuel, st, fe, depth, n, &e2) {
                    Err(err) => Err(err),
                    Ok(v) => whnf_app_i(mode, fuel, st, fe, depth, n, &v, args, i),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:942-996 whnfCoreStepI
/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// **One head-normalization step** (beta, iota, projection) with the loop's
/// continuation abstracted.  Only the spine head's normalization stays a
/// knot call (genuine nesting, bounded by the term's depth); every
/// *reduction* step is iteration, so a chain no longer charges the shared
/// recursion-depth budget one unit per step (con-leche's task #106 — that is
/// what made the `Nat.brecOn` grind of `Std.Time…toDays._proof_1` exhaust
/// `checkFuel`).
///
/// Deviations: the identity arms hand back a `P` bump (`expr::dup`) where
/// the Lean rebuilds the node; the `.letE`/`.bvar` arms are the cited throws
/// with their messages as `const` code points; and the continuation is the
/// budget `n` (see `whnf_app_i`).  The `.proj` arm's five-conjunct fire
/// guard is `core_k::proj_fire_shape_ok`, which is the cited conjunction.
pub fn whnf_core_step_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M_LET: [u32; 42] = [
        119, 104, 110, 102, 67, 111, 114, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105, 110, 32,
        97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112, 114, 101,
        115, 115, 105, 111, 110,
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
        ExprKind::App(_, _) => {
            let h = expr_ops::get_app_fn(e);
            let args = expr_ops::get_app_args(e);
            match whnf_core(mode, fuel, st, fe, depth, &h) {
                Err(err) => Err(err),
                Ok(v) => whnf_app_i(mode, fuel, st, fe, depth, n, &v, &args, 0),
            }
        }
        ExprKind::Proj(sn, i, pe) => {
            let sn = name::dup(sn);
            let i = *i;
            match whnf(mode, fuel, st, fe, depth, pe) {
                Err(err) => Err(err),
                Ok(w) => match proj_lit_to_ctor_i(mode, fuel, st, fe, depth, &w) {
                    Err(err) => Err(err),
                    Ok(e2) => whnf_core_proj_i(mode, fuel, st, fe, depth, n, &sn, i, &e2),
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

/// con-leche: ConLeche/Cached/CoreC.lean:942-996 whnfCoreStepI
/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// The `.proj` arm's continuation, on the reduced (and string-literal
/// expanded) scrutinee: the structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`,
/// driven by the projection table, behind the table's own counts and its
/// possibly-`Prop` level guard, and behind `projCertAtI`.  The fired field
/// goes to the loop's continuation, not back through the knot.
pub fn whnf_core_proj_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
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
                    if core_k::proj_fire_shape_ok(&entry, c, i, us, &args) {
                        let arg = core_k::get_d_expr(&args, entry.num_params + i);
                        match proj_cert_at_i(
                            mode,
                            fuel,
                            st,
                            fe,
                            depth,
                            env::verified_checks(mode),
                            env::beta_gate(mode),
                            c,
                            us,
                            &args,
                        ) {
                            Err(err) => Err(err),
                            Ok(true) => {
                                whnf_core_loop_i(mode, fuel, st, fe, depth, n, &arg)
                            }
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

/// con-leche: ConLeche/Cached/CoreC.lean:998-1004 whnfCoreLoopI
/// Iterate `whnf_core_step_i` on its own step budget.  No `Core.lean`
/// counterpart — `whnfCoreBody` recurses through the knot instead, which is
/// exactly what task #106 replaced.
pub fn whnf_core_loop_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 29] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102, 67, 111, 114, 101, 32, 108, 111, 111, 112,
    ];
    if n == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        whnf_core_step_i(mode, fuel, st, fe, depth, n - 1, e)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1006-1009 whnfCoreBodyI
/// con-leche: ConLeche/Kernel/Core.lean:1893-1982 whnfCoreBody
/// **The head-normalization body**: the loop at its own step budget
/// (`core_k::whnf_core_loop_fuel`, con-leche's `whnfCoreLoopFuel`).  Beta
/// (with the per-redex argument certificate), iota (with the stuck-major
/// machinery) and the structural projection rule — but **no delta**;
/// unfolding happens in the `whnf` loop.
pub fn whnf_core_body_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    whnf_core_loop_i(
        mode,
        fuel,
        st,
        fe,
        depth,
        core_k::whnf_core_loop_fuel(),
        e,
    )
}

/// con-leche: ConLeche/Cached/CoreC.lean:1093-1102 whnfStepI
/// con-leche: ConLeche/Kernel/Core.lean:2003-2018 whnfStep
/// One iteration of the reduction loop (the official kernel's `whnf` body):
/// head-normalize, try literal acceleration, unfold one definition — and
/// hand the reduct to the loop's continuation.  As in `whnf_app_i` the
/// continuation is its step budget `n`.
pub fn whnf_step_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match whnf_core(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(e1) => match reduce_nat_i(mode, fuel, st, fe, depth, &e1) {
            Err(err) => Err(err),
            Ok(Some(e2)) => whnf_loop_i(mode, fuel, st, fe, depth, n, &e2),
            Ok(None) => match unfold_definition_i(st, fe, &e1) {
                Err(err) => Err(err),
                Ok(Some(e2)) => whnf_loop_i(mode, fuel, st, fe, depth, n, &e2),
                Ok(None) => Ok(e1),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1104-1108 whnfLoopI
/// con-leche: ConLeche/Kernel/Core.lean:2020-2025 whnfLoop
/// The reduction loop: iterate `whnf_step_i` on its own step budget, so the
/// whole chain costs one knot level however many steps it takes.
pub fn whnf_loop_i(
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
        whnf_step_i(mode, fuel, st, fe, depth, n - 1, e)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1110-1112 whnfBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2027-2029 whnfBody
/// The reduction body: `whnf_loop_i` at its own step budget.  It reads no
/// mode function at all — the whole δ/ι/β content sits in `whnfCore`, which
/// this reaches through the knot — which is why `CoreC.lean` instantiates no
/// named `whnf` core (its own finding, `:2020-2024`).
pub fn whnf_body_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    whnf_loop_i(mode, fuel, st, fe, depth, core_k::whnf_loop_fuel(), e)
}

/// con-leche: ConLeche/Cached/CoreC.lean:1114-1119 ensureSortI
/// con-leche: ConLeche/Kernel/Core.lean:2031-2037 ensureSort
/// Ensure `e` (the type of some expression) is a sort, **returning its
/// level** — no readback needed, which is the twin's one difference from the
/// spec's.
pub fn ensure_sort_i(
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
    match whnf(mode, fuel, st, fe, depth, e) {
        Err(err) => Err(err),
        Ok(w) => match &w.0.kind {
            ExprKind::Sort(u) => Ok(level::dup(u)),
            _ => Err(core_types::invalid(core_types::code_points(&M))),
        },
    }
}

// ---------------------------------------------------------------------------
// Inference: the spine walks and the binder-telescope loops
// (`CoreC.lean:1011-1091`, `:1142-1290`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:43-58 CoreFnsI
/// con-leche: ConLeche/Cached/CoreC.lean:60-64 CoreFnsI.ioView
/// con-leche: ConLeche/Kernel/Core.lean:61-87 CoreFns
/// con-leche: ConLeche/Kernel/Core.lean:89-95 CoreFns.ioView
/// The knot slot a body's `r.infer` call resolves to: the full-grade `infer`
/// wrapper under the `infer` slot, the io-grade one under `inferIO` (whose
/// record is `CoreFnsI.ioView`).  This function *is* the `ioView`
/// substitution in the port — §3.1 ties the knot with plain functions, so
/// there is no record whose `infer` field can be rebound.
pub fn infer_at_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
    io: bool,
) -> CheckM<Expr> {
    if io {
        infer_io(mode, fuel, st, fe, depth, e)
    } else {
        infer(mode, fuel, st, fe, depth, e)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1011-1042 inferSpineI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **Application-inference spine loop** (con-leche's task #50): walk the raw
/// Π-telescope against the arguments with *deferred* substitution — each
/// argument's certificate substitutes only its own domain
/// (`instListRevM`), and the codomain is substituted once per peeled group.
/// A non-syntactic telescope step substitutes and normalizes, exactly like
/// the chained `inferBody` recursion.  The per-argument re-check runs
/// unconditionally (con-leche's task #100 de-gating).
///
/// Deviations: the cited remaining-argument list is `args[i..]`, and the
/// `Array` accumulator is a `Vec` taken by value and pushed (task #6's
/// accumulator rule).
pub fn infer_spine_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    acc: Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<Expr> {
    const M_MISMATCH: [u32; 25] = [
        97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 109,
        105, 115, 109, 97, 116, 99, 104,
    ];
    const M_FN: [u32; 17] = [
        102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100,
    ];
    if i >= args.len() {
        Ok(state_c::inst_list_rev_m(ty, &acc, 0))
    } else {
        match &ty.0.kind {
            ExprKind::ForallE(dom, body, _) => {
                let body = expr::dup(body);
                let dom2 = state_c::inst_list_rev_m(dom, &acc, 0);
                match infer(mode, fuel, st, fe, depth, &args[i]) {
                    Err(err) => Err(err),
                    Ok(ta) => match defeq(mode, fuel, st, fe, depth, &ta, &dom2) {
                        Err(err) => Err(err),
                        Ok(false) => Err(core_types::invalid(core_types::code_points(
                            &M_MISMATCH,
                        ))),
                        Ok(true) => {
                            let mut acc = acc;
                            acc.push(expr::dup(&args[i]));
                            infer_spine_i(
                                mode, fuel, st, fe, depth, &body, acc, args, i + 1,
                            )
                        }
                    },
                }
            }
            _ => {
                let ty2 = state_c::inst_list_rev_m(ty, &acc, 0);
                match whnf(mode, fuel, st, fe, depth, &ty2) {
                    Err(err) => Err(err),
                    Ok(w) => match &w.0.kind {
                        ExprKind::ForallE(dom, body, _) => {
                            let dom = expr::dup(dom);
                            let body = expr::dup(body);
                            match infer(mode, fuel, st, fe, depth, &args[i]) {
                                Err(err) => Err(err),
                                Ok(ta) => {
                                    match defeq(mode, fuel, st, fe, depth, &ta, &dom) {
                                        Err(err) => Err(err),
                                        Ok(false) => Err(core_types::invalid(
                                            core_types::code_points(&M_MISMATCH),
                                        )),
                                        Ok(true) => {
                                            let acc2 =
                                                core_k::expr_singleton(&args[i]);
                                            infer_spine_i(
                                                mode, fuel, st, fe, depth, &body, acc2,
                                                args, i + 1,
                                            )
                                        }
                                    }
                                }
                            }
                        }
                        _ => Err(core_types::invalid(core_types::code_points(&M_FN))),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1044-1091 inferSpineIOI
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// **The io-grade spine walk**: `infer_spine_i` with the per-argument
/// certificate gated — the ONE io-graded check, in bulk telescope form.  At
/// a ∀ step whose annotation datum licenses it the argument's inference and
/// the domain comparison are skipped; the returned type is the same
/// telescope walk either way, so the lane is annotation-blind in its
/// results.
///
/// **The licence is `mode.ioSkip mt.pw` and nothing else** (con-leche's
/// ruling of 2026-09-06): at `.verified` that is `mt.pw.isNever`, the datum
/// alone; at `.trusted` it is `true` — the per-argument certificate at an
/// internal inference is a certificate family, skipped wholesale.
///
/// Every `r.infer` here is the **io** slot: the knot ties this body's record
/// to `CoreFnsI.ioView` (the module note's deviation 4).
pub fn infer_spine_io_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    acc: Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
) -> CheckM<Expr> {
    const M_FN: [u32; 17] = [
        102, 117, 110, 99, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116, 101, 100,
    ];
    if i >= args.len() {
        Ok(state_c::inst_list_rev_m(ty, &acc, 0))
    } else {
        match &ty.0.kind {
            ExprKind::ForallE(dom, body, mt) => {
                let body = expr::dup(body);
                // Task #18's rule: a gated certificate whose arms rejoin
                // must be two tail calls, not a joined `CheckM<()>`.  The
                // skip arm continues the walk directly (and never builds
                // `dom'`, which is the *point* of the licence); the
                // certifying arm continues it behind the certificate.
                if env::io_skip(mode, &mt.pw) {
                    let mut acc = acc;
                    acc.push(expr::dup(&args[i]));
                    infer_spine_io_i(mode, fuel, st, fe, depth, &body, acc, args, i + 1)
                } else {
                    let dom2 = state_c::inst_list_rev_m(dom, &acc, 0);
                    match infer_spine_io_cert_i(mode, fuel, st, fe, depth, &args[i], &dom2)
                    {
                        Err(err) => Err(err),
                        Ok(()) => {
                            let mut acc = acc;
                            acc.push(expr::dup(&args[i]));
                            infer_spine_io_i(
                                mode, fuel, st, fe, depth, &body, acc, args, i + 1,
                            )
                        }
                    }
                }
            }
            _ => {
                let ty2 = state_c::inst_list_rev_m(ty, &acc, 0);
                match whnf(mode, fuel, st, fe, depth, &ty2) {
                    Err(err) => Err(err),
                    Ok(w) => match &w.0.kind {
                        ExprKind::ForallE(dom, body, mt) => {
                            let dom = expr::dup(dom);
                            let body = expr::dup(body);
                            let pw = prop_when::dup(&mt.pw);
                            // Task #18's rule, met again here: a gated
                            // certificate whose arms rejoin must be two tail
                            // calls, not a joined `CheckM<()>` — as in the
                            // syntactic arm above.
                            if env::io_skip(mode, &pw) {
                                let acc2 = core_k::expr_singleton(&args[i]);
                                infer_spine_io_i(
                                    mode, fuel, st, fe, depth, &body, acc2, args, i + 1,
                                )
                            } else {
                                match infer_spine_io_cert_i(
                                    mode, fuel, st, fe, depth, &args[i], &dom,
                                ) {
                                    Err(err) => Err(err),
                                    Ok(()) => {
                                        let acc2 = core_k::expr_singleton(&args[i]);
                                        infer_spine_io_i(
                                            mode, fuel, st, fe, depth, &body, acc2,
                                            args, i + 1,
                                        )
                                    }
                                }
                            }
                        }
                        _ => Err(core_types::invalid(core_types::code_points(&M_FN))),
                    },
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1044-1091 inferSpineIOI
/// The cited `unless mode.ioSkip mt.pw do let ta ← r.infer depth a; unless ←
/// r.defeq depth ta dom' do throw` — the gated certificate as its own
/// `CheckM<()>`, so the gate's two arms carry the same borrow context and
/// join on nothing (task #18's Aeneas finding: *a gated certificate whose
/// arms rejoin must be split*; here the join is on `()`, which carries no
/// borrow, and the walk continues after it in both arms).
pub fn infer_spine_io_cert_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    dom: &Expr,
) -> CheckM<()> {
    const M_MISMATCH: [u32; 25] = [
        97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 116, 121, 112, 101, 32, 109,
        105, 115, 109, 97, 116, 99, 104,
    ];
    match infer_io(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(ta) => match defeq(mode, fuel, st, fe, depth, &ta, dom) {
            Err(err) => Err(err),
            Ok(false) => Err(core_types::invalid(core_types::code_points(&M_MISMATCH))),
            Ok(true) => Ok(()),
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1142-1160 inferLamsOutI
/// **Rebuild loop of `infer_lams_i`**: fold the stack (innermost binder
/// first, `j` its binder level relative to the ambient depth `d`), one
/// `∀`-node per entry with one `abstractRangeM` per domain.  The
/// intermediate `∀`-node inferences of the chained body are value-determined
/// by the peel phase's domain sorts and the leaf phase's body-type sort and
/// cannot fail.
///
/// Task #161's chain rule: a node's prop-ness annotation must agree with its
/// inner neighbour's (the innermost step compares the entry with itself —
/// vacuously true).
///
/// Deviation: the cited `List` stack is a `Vec` whose *last* element is the
/// innermost binder, walked downwards by `p` (the number of entries still to
/// fold).  `cur` is taken by value, as the fold's accumulator.
pub fn infer_lams_out_i(
    mode: &CheckMode,
    d: u64,
    stk: &Vec<InferLamEntry>,
    p: usize,
    j: u64,
    cur: Expr,
    prev_pw: &PropWhen,
) -> CheckM<Expr> {
    const M: [u32; 40] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 99, 104, 97,
        105, 110, 41,
    ];
    if p == 0 || p > stk.len() {
        Ok(cur)
    } else {
        let ent: &InferLamEntry = &stk[p - 1];
        if env::verified_checks(mode) && !prop_when::beq(&ent.1.pw, prev_pw) {
            Err(core_types::not_implemented(core_types::code_points(&M)))
        } else {
            let ty_abs = state_c::abstract_range_m(&ent.0, d, j);
            let node = expr::forall_e(ty_abs, cur, expr::binder_meta_dup(&ent.1));
            let pw = prop_when::dup(&ent.1.pw);
            infer_lams_out_i(mode, d, stk, p - 1, expr_ops::sub_nat(j, 1), node, &pw)
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **Leaf phase of `infer_lams_i`**: bulk-open the residual body, infer it,
/// then rebuild outward.  At the verified modes the chain's body type is
/// sort-checked here — the spec's codomain check, which fires at the
/// innermost binder of a λ-chain, i.e. exactly when the peel stops on a
/// non-λ residual — and the innermost binder's prop-ness annotation is
/// validated against the chain's body-type sort.
///
/// The fold's initial neighbour: a λ residual (the fuel-exhausted path)
/// supplies its own annotation, so the head entry's chain check compares
/// against it exactly as the spec's per-node clause does; a non-λ residual
/// makes the head entry's step vacuous (its codomain fact is the leaf check).
pub fn infer_lams_leaf_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    t: &Expr,
    k: u64,
    fvs: &Vec<Expr>,
    stk: &Vec<InferLamEntry>,
) -> CheckM<Expr> {
    let ob = state_c::inst_list_rev_m(t, fvs, 0);
    match infer(mode, fuel, st, fe, d + k, &ob) {
        Err(err) => Err(err),
        Ok(bt) => {
            let chk = if expr_ops::is_lam(t) {
                Ok(())
            } else if env::verified_checks(mode) {
                infer_lams_leaf_sort_i(mode, fuel, st, fe, d + k, &bt, stk)
            } else {
                Ok(())
            };
            match chk {
                Err(err) => Err(err),
                Ok(()) => {
                    let cur = state_c::abstract_range_m(&bt, d, k);
                    let prev_pw = infer_lams_prev_pw_i(t, stk);
                    infer_lams_out_i(
                        mode,
                        d,
                        stk,
                        stk.len(),
                        expr_ops::sub_nat(k, 1),
                        cur,
                        &prev_pw,
                    )
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI
/// The cited verified-mode block of the leaf phase: the body type's own
/// sort, and the innermost binder's annotation validated against its
/// zero-ness (the leaf half of the spec's `.lam` clause check).  An empty
/// stack cannot occur — the caller peels at least one binder — and answers
/// `()` as the Lean's `| [] => pure ()` does.
pub fn infer_lams_leaf_sort_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    dk: u64,
    bt: &Expr,
    stk: &Vec<InferLamEntry>,
) -> CheckM<()> {
    const M: [u32; 39] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 108, 97, 109, 45, 99, 111, 100, 45, 108, 101, 97,
        102, 41,
    ];
    const M_SORT: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    match infer_io(mode, fuel, st, fe, dk, bt) {
        Err(err) => Err(err),
        Ok(btt) => match whnf(mode, fuel, st, fe, dk, &btt) {
            Err(err) => Err(err),
            Ok(wbtt) => match &wbtt.0.kind {
                ExprKind::Sort(vb) => {
                    if stk.len() == 0 {
                        Ok(())
                    } else {
                        let pv = level::zeroness_of(vb);
                        if prop_when::beq(&pv, &stk[stk.len() - 1].1.pw) {
                            Ok(())
                        } else {
                            Err(core_types::not_implemented(core_types::code_points(&M)))
                        }
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M_SORT))),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1162-1206 inferLamsLeafI
/// The cited `prevPw` the rebuild fold starts from: a λ residual's own
/// datum, else the innermost stack entry's (which makes the head entry's
/// chain check vacuous), else `.never` on an empty stack.
pub fn infer_lams_prev_pw_i(t: &Expr, stk: &Vec<InferLamEntry>) -> PropWhen {
    match expr_ops::lam_pw(t) {
        Some(pw) => pw,
        None => {
            if stk.len() == 0 {
                prop_when::never()
            } else {
                prop_when::dup(&stk[stk.len() - 1].1.pw)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1208-1228 inferLamsI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **λ-telescope inference loop** (con-leche's task #72): peel the raw
/// λ-chain, checking each opened domain to be a type on the way in.  `k`
/// counts the opened binders (`≥ 1`: the caller peels the first binder
/// inline), `fvs` their free variables innermost-*last* (the cited `Array`
/// is pushed, so `instListRevM` indexes it from the end).
pub fn infer_lams_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    peel: u64,
    t: &Expr,
    k: u64,
    fvs: Vec<Expr>,
    stk: Vec<InferLamEntry>,
) -> CheckM<Expr> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    if peel == 0 {
        infer_lams_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk)
    } else {
        match &t.0.kind {
            ExprKind::Lam(ty, body, mb) => {
                let body = expr::dup(body);
                let mb = expr::binder_meta_dup(mb);
                let tyo = state_c::inst_list_rev_m(ty, &fvs, 0);
                match infer(mode, fuel, st, fe, d + k, &tyo) {
                    Err(err) => Err(err),
                    Ok(tty) => match whnf(mode, fuel, st, fe, d + k, &tty) {
                        Err(err) => Err(err),
                        Ok(wtty) => {
                            if core_k::is_sort(&wtty) {
                                let fv = expr::fvar(d + k, expr::dup(&tyo));
                                let mut fvs = fvs;
                                fvs.push(fv);
                                let mut stk = stk;
                                stk.push((tyo, mb));
                                infer_lams_i(
                                    mode,
                                    fuel,
                                    st,
                                    fe,
                                    d,
                                    peel - 1,
                                    &body,
                                    k + 1,
                                    fvs,
                                    stk,
                                )
                            } else {
                                Err(core_types::invalid(core_types::code_points(&M)))
                            }
                        }
                    },
                }
            }
            _ => infer_lams_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1230-1254 inferPisOutI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **Rebuild loop of `infer_pis_i`**: fold the accumulated domain sorts by
/// `imax`, innermost binder first — exactly the chained `∀`-rule's result
/// value — validating each node's prop-ness annotation against its inferred
/// codomain sort.
///
/// con-leche's task #272 (its GitHub issue #9): the codomain sort's
/// zero-ness datum is **threaded, not recomputed**.  `zeronessOf (imax u v)
/// = zeronessOf v` holds definitionally, so every node of a ∀ telescope
/// shares the leaf's datum; the fold used to read it out of a `Level`-keyed
/// memo that missed at every step and then walked `zeronessOf` down the
/// growing right spine — `O(k²)` in the telescope depth.
pub fn infer_pis_out_i(
    mode: &CheckMode,
    stk: &Vec<(Level, PropWhen)>,
    p: usize,
    v: Level,
    pv: &PropWhen,
) -> CheckM<Level> {
    const M: [u32; 37] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 102, 111, 114, 97, 108, 108, 45, 99, 111, 100, 41,
    ];
    if p == 0 || p > stk.len() {
        Ok(v)
    } else {
        let ent: &(Level, PropWhen) = &stk[p - 1];
        if env::verified_checks(mode) && !prop_when::beq(pv, &ent.1) {
            Err(core_types::not_implemented(core_types::code_points(&M)))
        } else {
            let v2 = level::imax(level::dup(&ent.0), v);
            infer_pis_out_i(mode, stk, p - 1, v2, pv)
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1256-1267 inferPisLeafI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// Leaf phase of `infer_pis_i`: bulk-open the residual body, infer its sort,
/// then fold the domain sorts outward.
pub fn infer_pis_leaf_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    t: &Expr,
    k: u64,
    fvs: &Vec<Expr>,
    stk: &Vec<(Level, PropWhen)>,
) -> CheckM<Expr> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    let ob = state_c::inst_list_rev_m(t, fvs, 0);
    match infer(mode, fuel, st, fe, d + k, &ob) {
        Err(err) => Err(err),
        Ok(bt) => match whnf(mode, fuel, st, fe, d + k, &bt) {
            Err(err) => Err(err),
            Ok(wbt) => match &wbt.0.kind {
                ExprKind::Sort(v) => {
                    let pv = level::zeroness_of(v);
                    match infer_pis_out_i(mode, stk, stk.len(), level::dup(v), &pv) {
                        Err(err) => Err(err),
                        Ok(iv) => Ok(expr::sort(iv)),
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M))),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1269-1290 inferPisI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **∀-telescope inference loop**: peel the raw ∀-chain, checking each
/// opened domain to be a type on the way in and accumulating its sort, infer
/// the bulk-opened leaf's sort once, and fold `imax` outward.  The `∀`-rule
/// infers its codomain sort — the stored annotation is not read (con-leche's
/// task #100 stage 6), only validated in the fold.
pub fn infer_pis_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    peel: u64,
    t: &Expr,
    k: u64,
    fvs: Vec<Expr>,
    stk: Vec<(Level, PropWhen)>,
) -> CheckM<Expr> {
    const M: [u32; 15] = [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 111, 114, 116,
    ];
    if peel == 0 {
        infer_pis_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk)
    } else {
        match &t.0.kind {
            ExprKind::ForallE(ty, body, mb) => {
                let body = expr::dup(body);
                let pw = prop_when::dup(&mb.pw);
                let tyo = state_c::inst_list_rev_m(ty, &fvs, 0);
                match infer(mode, fuel, st, fe, d + k, &tyo) {
                    Err(err) => Err(err),
                    Ok(tty) => match whnf(mode, fuel, st, fe, d + k, &tty) {
                        Err(err) => Err(err),
                        Ok(wtty) => match &wtty.0.kind {
                            ExprKind::Sort(u) => {
                                let u = level::dup(u);
                                let fv = expr::fvar(d + k, expr::dup(&tyo));
                                let mut fvs = fvs;
                                fvs.push(fv);
                                let mut stk = stk;
                                stk.push((u, pw));
                                infer_pis_i(
                                    mode,
                                    fuel,
                                    st,
                                    fe,
                                    d,
                                    peel - 1,
                                    &body,
                                    k + 1,
                                    fvs,
                                    stk,
                                )
                            }
                            _ => Err(core_types::invalid(core_types::code_points(&M))),
                        },
                    },
                }
            }
            _ => infer_pis_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk),
        }
    }
}

// ---------------------------------------------------------------------------
// The two inference bodies (`CoreC.lean:1292-1448`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// The two facts the `.const` clause's guards read off the stored
/// declaration — is it a projection-table entry, and how many level
/// parameters does it carry — as an owning probe, so the index's borrow dies
/// at the call boundary (task #14's rule; one of task #23's four Aeneas
/// errors).
pub fn const_shape_probe_i(fe: &FEnv, n: &Name) -> Option<(bool, usize)> {
    match fenv::find(fe, n) {
        None => None,
        Some(ci) => Some((
            env::is_tower_entry(ci),
            env::to_constant_val(ci).level_params.len(),
        )),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The `.const` clause: the constant is stored, is not a projection table,
/// carries the right number of universe levels — and its type comes from
/// `constTyAtM`, i.e. the `constTyAt` memo over the `ienv` conversion.  That
/// read is this clause's whole difference from the spec's.
pub fn infer_const_i(
    st: &mut CState,
    fe: &FEnv,
    n: &Name,
    us: &Vec<Level>,
) -> CheckM<Expr> {
    const M_UNKNOWN: [u32; 16] = [
        117, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116,
    ];
    const M_TOWER: [u32; 41] = [
        112, 114, 111, 106, 101, 99, 116, 105, 111, 110, 32, 116, 97, 98, 108, 101, 32, 101,
        110, 116, 114, 121, 32, 117, 115, 101, 100, 32, 97, 115, 32, 97, 32, 99, 111, 110, 115,
        116, 97, 110, 116,
    ];
    const M_LEVELS: [u32; 35] = [
        105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111,
        102, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 108, 101, 118, 101, 108, 115,
    ];
    match const_shape_probe_i(fe, n) {
        None => Err(core_types::invalid(core_types::code_points(&M_UNKNOWN))),
        Some(p) => {
            if p.0 {
                Err(core_types::invalid(core_types::code_points(&M_TOWER)))
            } else if us.len() != p.1 {
                Err(core_types::invalid(core_types::code_points(&M_LEVELS)))
            } else {
                state_c::const_ty_at_m(st, fe, n, us)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// **The inference body.**  The `∀` and `λ` clauses peel their whole binder
/// telescope (`infer_pis_i` / `infer_lams_i`) after checking the first
/// binder's domain inline; the `.app` clause infers the spine head once and
/// walks its Π-telescope against the whole spine (`infer_spine_i`); the
/// `.const` clause reads `constTyAtM`; the `.proj` clause types the node by
/// its table entry through `ProjEntry.typeAtI`.
///
/// `io` is the grade of the recursive calls in the clauses the io body does
/// **not** override — only `.proj` makes any (the module note's deviation
/// 4).  The three clauses the io body does override (`∀`, `λ`, `.app`) are
/// unreachable at `io = true` and call the full-grade wrappers directly.
pub fn infer_body_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
    io: bool,
) -> CheckM<Expr> {
    const M_LET: [u32; 43] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 58, 32, 96, 108, 101, 116, 96, 32, 105, 110,
        32, 97, 110, 32, 97, 110, 110, 111, 116, 97, 116, 101, 100, 32, 101, 120, 112, 114, 101,
        115, 115, 105, 111, 110,
    ];
    const M_BVAR: [u32; 39] = [
        105, 110, 102, 101, 114, 84, 121, 112, 101, 32, 98, 101, 121, 111, 110, 100, 32, 116,
        104, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 102, 114, 97, 103, 109,
        101, 110, 116,
    ];
    match &e.0.kind {
        ExprKind::Sort(u) => Ok(expr::sort(level::succ(level::dup(u)))),
        ExprKind::Fvar(idx, ty) => core_k::infer_fvar(*idx, ty, depth),
        ExprKind::Const(n, us) => infer_const_i(st, fe, n, us),
        ExprKind::Lit(Literal::NatVal(_)) => core_k::infer_lit_nat(fe),
        ExprKind::Lit(Literal::StrVal(_)) => core_k::infer_lit_str(fe),
        ExprKind::ForallE(ty, body, mb) => {
            infer_forall_i(mode, fuel, st, fe, depth, ty, body, mb)
        }
        ExprKind::Lam(ty, body, mb) => {
            infer_lam_i(mode, fuel, st, fe, depth, ty, body, mb)
        }
        ExprKind::App(_, _) => {
            let h = expr_ops::get_app_fn(e);
            let args = expr_ops::get_app_args(e);
            match infer(mode, fuel, st, fe, depth, &h) {
                Err(err) => Err(err),
                Ok(tf) => {
                    infer_spine_i(mode, fuel, st, fe, depth, &tf, Vec::new(), &args, 0)
                }
            }
        }
        ExprKind::Proj(sn, i, pe) => {
            infer_proj_i(mode, fuel, st, fe, depth, sn, *i, pe, io)
        }
        ExprKind::LetE(_, _, _) => {
            Err(core_types::internal(core_types::code_points(&M_LET)))
        }
        ExprKind::Bvar(_) => Err(core_types::not_implemented(core_types::code_points(
            &M_BVAR,
        ))),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// The `∀` clause: the first binder's domain is checked to be a type inline,
/// and the rest of the chain goes to the telescope loop at the peel fuel.
pub fn infer_forall_i(
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
    match infer(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(tty) => match whnf(mode, fuel, st, fe, depth, &tty) {
            Err(err) => Err(err),
            Ok(wtty) => match &wtty.0.kind {
                ExprKind::Sort(u) => {
                    let u = level::dup(u);
                    let fv = expr::fvar(depth, expr::dup(ty));
                    let mut fvs: Vec<Expr> = Vec::new();
                    fvs.push(fv);
                    let mut stk: Vec<(Level, PropWhen)> = Vec::new();
                    stk.push((u, prop_when::dup(&mb.pw)));
                    infer_pis_i(
                        mode,
                        fuel,
                        st,
                        fe,
                        depth,
                        state_c::peel_fuel(),
                        body,
                        1,
                        fvs,
                        stk,
                    )
                }
                _ => Err(core_types::invalid(core_types::code_points(&M))),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// The `λ` clause: the first binder's domain is checked to be a type inline
/// (the io body skips that run — official's `infer_lambda` at `infer_only`),
/// and the rest of the chain goes to the telescope loop.
pub fn infer_lam_i(
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
    match infer(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(tty) => match whnf(mode, fuel, st, fe, depth, &tty) {
            Err(err) => Err(err),
            Ok(wtty) => {
                if core_k::is_sort(&wtty) {
                    let fv = expr::fvar(depth, expr::dup(ty));
                    let mut fvs: Vec<Expr> = Vec::new();
                    fvs.push(fv);
                    let mut stk: Vec<InferLamEntry> = Vec::new();
                    stk.push((expr::dup(ty), expr::binder_meta_dup(mb)));
                    infer_lams_i(
                        mode,
                        fuel,
                        st,
                        fe,
                        depth,
                        state_c::peel_fuel(),
                        body,
                        1,
                        fvs,
                        stk,
                    )
                } else {
                    Err(core_types::invalid(core_types::code_points(&M)))
                }
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Cached/ExprOpsC.lean:623-642 ProjEntry.typeAtI
/// The table lookup and the checks of the cached `.proj` clause, on the
/// already reduced type of the subject: `core_k::infer_proj_at`'s twin with
/// the ONE difference the cached lane prescribes — the field type comes from
/// `expr_ops_c::proj_entry_type_at_i`, i.e. `ProjEntry.typeAtI`, and not
/// from the `Expr`-level `ProjEntry.typeAt`.
///
/// **This is task #26's owed reconciliation, closed by task #28's
/// differential run.**  The two formulas are the same value, but
/// `ProjEntry.typeAt`'s `bvar` arm re-traverses the replacement (the spec
/// `expr_ops::instantiate_list`, which `instantiate_list_go` defers to at a
/// `.bvar`, exactly as `ExprOps.lean` does), so a subject or parameter that
/// is a DAG comes back as a fresh *tree* copy — con-leche's own "affine
/// frontier" out-of-memory, and the reason its executed clause calls
/// `typeAtI`.  The fixture `tests/e2e/proj_share.ndjson` does not finish
/// without this (it projects out of a 27-node DAG with a 2^27-node tree);
/// con-leche accepts it in milliseconds.  The alternative — retargeting
/// `core_k::infer_proj_at` — is what task #26 ruled out, because
/// `kernel::core_k` must not depend on `crate::cached`; so the cached lane
/// gets its own twin here, beside the body that calls it, which is where the
/// Lean has it (`inferBodyI` inlines the lookup).
pub fn infer_proj_at_i(
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
                proj_type_at_checked_i(&entry, sn, t, us, &targs, pe)
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

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// con-leche: ConLeche/Cached/ExprOpsC.lean:623-642 ProjEntry.typeAtI
/// `core_k::proj_type_at_checked`'s cached twin: the same three guards and
/// the same propositional-structure restriction (`ProjEntry.fireOk`, which
/// is `core_k`'s — it reads levels only), with `ProjEntry.typeAtI` as the
/// type.  See `infer_proj_at_i`.
pub fn proj_type_at_checked_i(
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
    } else if !core_k::proj_entry_fire_ok(entry, us) {
        Err(core_types::invalid(core_types::code_points(&M_PROP)))
    } else {
        Ok(expr_ops_c::proj_entry_type_at_i(entry, us, targs, pe))
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1292-1389 inferBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2039-2204 inferBody
/// The `.proj` clause: a `.proj` node is typed by its projection-table
/// entry, through `ProjEntry.typeAtI` — which is `infer_proj_at_i` above.
/// The propositional-structure restriction reads `Level.isEquiv`
/// **directly**, as the Lean does: this site stays off `eqvC` by policy (the
/// module note's table).  `io` is the grade of the subject's inference.
pub fn infer_proj_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    sn: &Name,
    i: u64,
    pe: &Expr,
    io: bool,
) -> CheckM<Expr> {
    match infer_at_i(mode, fuel, st, fe, depth, pe, io) {
        Err(err) => Err(err),
        Ok(tpe) => match whnf(mode, fuel, st, fe, depth, &tpe) {
            Err(err) => Err(err),
            Ok(te) => infer_proj_at_i(fe, sn, i, pe, &te),
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1391-1448 inferBodyIOI
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// **The io-grade inference body**: `infer_body_i` with exactly three clauses
/// changed — the application spine walk is the gated `infer_spine_io_i` (the
/// ONE io-graded check), and the `∀`/`λ` clauses are the **chained** pure io
/// clauses, deliberately not the task-#72 telescope loops (looping the io
/// lane would owe the whole loop-identification walk family a second,
/// io-graded instance for a lane whose subjects are internal
/// re-inferences).  Every other view dispatches to `infer_body_i` at `io =
/// true`, so there is no textual clone to drift.
pub fn infer_body_io_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    e: &Expr,
) -> CheckM<Expr> {
    match &e.0.kind {
        ExprKind::App(_, _) => {
            let h = expr_ops::get_app_fn(e);
            let args = expr_ops::get_app_args(e);
            match infer_io(mode, fuel, st, fe, depth, &h) {
                Err(err) => Err(err),
                Ok(tf) => {
                    infer_spine_io_i(mode, fuel, st, fe, depth, &tf, Vec::new(), &args, 0)
                }
            }
        }
        ExprKind::ForallE(ty, body, mb) => {
            infer_forall_io_i(mode, fuel, st, fe, depth, ty, body, mb)
        }
        ExprKind::Lam(ty, body, mb) => {
            infer_lam_io_i(mode, fuel, st, fe, depth, ty, body, mb)
        }
        _ => infer_body_i(mode, fuel, st, fe, depth, e, true),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1391-1448 inferBodyIOI
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The io `∀` clause, chained: the domain's sort, the body opened with
/// `inst1M` at the io grade, `ensureSortI` on its type, the annotation
/// validation at the verified modes, and `.sort (.imax u v)`.
pub fn infer_forall_io_i(
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
    const M_COD: [u32; 37] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 102, 111, 114, 97, 108, 108, 45, 99, 111, 100, 41,
    ];
    match infer_io(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(tty) => match whnf(mode, fuel, st, fe, depth, &tty) {
            Err(err) => Err(err),
            Ok(wtty) => match &wtty.0.kind {
                ExprKind::Sort(u) => {
                    let u = level::dup(u);
                    let fv = expr::fvar(depth, expr::dup(ty));
                    let ob = state_c::inst1_m(body, &fv, 0);
                    match infer_io(mode, fuel, st, fe, depth + 1, &ob) {
                        Err(err) => Err(err),
                        Ok(bt) => {
                            match ensure_sort_i(mode, fuel, st, fe, depth + 1, &bt) {
                                Err(err) => Err(err),
                                Ok(v) => {
                                    if env::verified_checks(mode)
                                        && !prop_when::beq(
                                            &level::zeroness_of(&v),
                                            &mb.pw,
                                        )
                                    {
                                        Err(core_types::not_implemented(
                                            core_types::code_points(&M_COD),
                                        ))
                                    } else {
                                        Ok(expr::sort(level::imax(u, v)))
                                    }
                                }
                            }
                        }
                    }
                }
                _ => Err(core_types::invalid(core_types::code_points(&M))),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1391-1448 inferBodyIOI
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The io `λ` clause, chained and with **no domain-sort run** (con-leche's
/// task #168 stage 2, as in the spec): the body opened with `inst1M` at the
/// io grade, the codomain validation at the verified modes (the chain rule
/// through `lamPw`, else one leaf computation), and `∀ ty (abstract1M bt
/// depth) mb`.
pub fn infer_lam_io_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    let fv = expr::fvar(depth, expr::dup(ty));
    let ob = state_c::inst1_m(body, &fv, 0);
    match infer_io(mode, fuel, st, fe, depth + 1, &ob) {
        Err(err) => Err(err),
        Ok(bt) => {
            let chk = if env::verified_checks(mode) {
                infer_lam_cod_io_i(mode, fuel, st, fe, depth, body, mb, &bt)
            } else {
                Ok(())
            };
            match chk {
                Err(err) => Err(err),
                Ok(()) => Ok(expr::forall_e(
                    expr::dup(ty),
                    state_c::abstract1_m(&bt, depth),
                    expr::binder_meta_dup(mb),
                )),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1391-1448 inferBodyIOI
/// con-leche: ConLeche/Kernel/Core.lean:2206-2334 inferBodyIO
/// The io λ clause's codomain-sort validation: **the chain rule** at an
/// outer binder (an outer λ's codomain is the inner λ's own ∀-type, whose
/// sort's zero-ness is the inner codomain's — datum equality with the
/// neighbour, no inference), and the leaf computation at the innermost
/// binder.
pub fn infer_lam_cod_io_i(
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
        None => match infer_io(mode, fuel, st, fe, depth + 1, bt) {
            Err(err) => Err(err),
            Ok(btt) => match ensure_sort_i(mode, fuel, st, fe, depth + 1, &btt) {
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
        },
    }
}

// ---------------------------------------------------------------------------
// Definitional equality (`CoreC.lean:1450-1634`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:1450-1453 boolTrueShortcutI
/// con-leche: ConLeche/Kernel/Core.lean:2336-2348 boolTrueShortcut
/// **The eq-true shortcut** (the divergence audit's E2): the left side is
/// fully head-normalised and the verdict is `true` iff the reduct is
/// `Bool.true`.  Only the reduction is here; the guard is `defeq_step_i`'s.
pub fn bool_true_shortcut_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
) -> CheckM<bool> {
    match whnf(mode, fuel, st, fe, depth, a) {
        Err(err) => Err(err),
        Ok(w) => Ok(core_k::is_bool_true(&w)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// The definitional-equality body's one iteration: the syntactic fast path,
/// the eq-true shortcut, head normalization of both sides (**no delta** —
/// `whnfCore`), the hoisted proof irrelevance, then lazy delta, then
/// structural congruence with the stuck fallbacks.
///
/// Deviations: as in `whnf_step_i`, the cited continuation `k : Bool → Expr
/// → Expr → CheckCM Bool` is the loop's step budget `n` — `k pi x y` is
/// `defeq_loop_i(…, n, pi, x, y)`, which is what `defeqLoopI` passes.  The
/// body's stages are separate functions so every cited `else` arm stays a
/// tail position rather than a twenty-deep nest.
pub fn defeq_step_i(
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
        let sc = if pi && core_k::is_bool_true(b) && !expr_ops::has_fvar(a) {
            bool_true_shortcut_i(mode, fuel, st, fe, depth, a)
        } else {
            Ok(false)
        };
        match sc {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => match whnf_core(mode, fuel, st, fe, depth, a) {
                Err(err) => Err(err),
                Ok(a2) => match whnf_core(mode, fuel, st, fe, depth, b) {
                    Err(err) => Err(err),
                    Ok(b2) => {
                        if expr::beq(&a2, &b2) {
                            Ok(true)
                        } else {
                            defeq_after_whnf_i(mode, fuel, st, fe, depth, n, pi, &a2, &b2)
                        }
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// The hoisted proof-irrelevance probe, run **once per entry** (the audit's
/// D3, hence the `pi` flag) and never on a pair official's
/// `quick_is_def_eq` decides itself (D4, hence `quickPair`).
pub fn defeq_after_whnf_i(
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
    let pir = if pi && !core_k::quick_pair(a2, b2) {
        prop_irrel_i(mode, fuel, st, fe, depth, a2, b2)
    } else {
        Ok(false)
    };
    match pir {
        Err(err) => Err(err),
        Ok(true) => Ok(true),
        Ok(false) => defeq_lits_i(mode, fuel, st, fe, depth, n, a2, b2),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// Literal acceleration, guarded on *both* sides being free of free
/// variables, mirroring the official kernel: unguarded folding is a
/// forbidden strategy superset.  A fold re-enters the loop at `pi = true`.
///
/// Deviation: the cited `!a'.hasFvar && !b'.hasFvar` guard is an `if` nest
/// rather than a `&&` of two negations — task #18's one Lean-side error (a
/// `let`-bound `!b` comes out of Aeneas as the *propositional* `¬ b`, whose
/// `if` then wants a `Decidable` instance the elaborator does not find).
pub fn defeq_lits_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let closed = if expr_ops::has_fvar(a2) {
        false
    } else if expr_ops::has_fvar(b2) {
        false
    } else {
        true
    };
    let ra = if closed {
        reduce_nat_i(mode, fuel, st, fe, depth, a2)
    } else {
        Ok(None)
    };
    match ra {
        Err(err) => Err(err),
        Ok(Some(a3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, true, &a3, b2),
        Ok(None) => {
            let rb = if closed {
                reduce_nat_i(mode, fuel, st, fe, depth, b2)
            } else {
                Ok(None)
            };
            match rb {
                Err(err) => Err(err),
                Ok(Some(b3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, true, a2, &b3),
                Ok(None) => defeq_delta_i(mode, fuel, st, fe, depth, n, a2, b2),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// Lazy delta, **decision before materialization**: the two heads
/// (`unfoldableHeadC`) and their hints decide which side to unfold, and
/// `unfoldDefinitionI` — which is the only place the `constValAt` memo is
/// read on this path — runs only inside the branch that consumes it.  The
/// `pure false` fallbacks are unreachable and sound.
pub fn defeq_delta_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let ua = core_k::unfoldable_head(fe, a2);
    let ub = core_k::unfoldable_head(fe, b2);
    if ua && !ub {
        match unfold_definition_i(st, fe, a2) {
            Err(err) => Err(err),
            Ok(Some(a3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, false, &a3, b2),
            Ok(None) => Ok(false),
        }
    } else if !ua && ub {
        match unfold_definition_i(st, fe, b2) {
            Err(err) => Err(err),
            Ok(Some(b3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, false, a2, &b3),
            Ok(None) => Ok(false),
        }
    } else if ua && ub {
        defeq_delta_both_i(mode, fuel, st, fe, depth, n, a2, b2)
    } else {
        defeq_struct_i(mode, fuel, st, fe, depth, a2, b2)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// Both heads unfoldable: unfold only the side with the greater hint
/// (`headHintC`); at equal *regular* hints try the same-head congruence
/// short-circuit first (`sameConstHeadsC` + `defeqSpineI`); otherwise unfold
/// both.
pub fn defeq_delta_both_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    let ha = core_k::head_hint(fe, a2);
    let hb = core_k::head_hint(fe, b2);
    if env::reducibility_hint_lt(&hb, &ha) {
        match unfold_definition_i(st, fe, a2) {
            Err(err) => Err(err),
            Ok(Some(a3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, false, &a3, b2),
            Ok(None) => Ok(false),
        }
    } else if env::reducibility_hint_lt(&ha, &hb) {
        match unfold_definition_i(st, fe, b2) {
            Err(err) => Err(err),
            Ok(Some(b3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, false, a2, &b3),
            Ok(None) => Ok(false),
        }
    } else if env::reducibility_hint_same_regular(&ha, &hb)
        && core_k::same_const_heads(a2, b2)
    {
        match defeq_spine_i(mode, fuel, st, fe, depth, a2, b2) {
            Err(err) => Err(err),
            Ok(true) => Ok(true),
            Ok(false) => defeq_unfold_both_i(mode, fuel, st, fe, depth, n, a2, b2),
        }
    } else {
        defeq_unfold_both_i(mode, fuel, st, fe, depth, n, a2, b2)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// `match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with | some
/// a₂, some b₂ => k false a₂ b₂ | _, _ => pure false`, the tail both
/// equal-hint arms share.
pub fn defeq_unfold_both_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    n: u64,
    a2: &Expr,
    b2: &Expr,
) -> CheckM<bool> {
    match unfold_definition_i(st, fe, a2) {
        Err(err) => Err(err),
        Ok(None) => Ok(false),
        Ok(Some(a3)) => match unfold_definition_i(st, fe, b2) {
            Err(err) => Err(err),
            Ok(None) => Ok(false),
            Ok(Some(b3)) => defeq_loop_i(mode, fuel, st, fe, depth, n, false, &a3, &b3),
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Neither head unfolds: structural congruence with the stuck fallbacks, in
/// the cited arm order (which is load-bearing — the literal/constructor-form
/// arms come before the general stuck ones, and the one-sided λ η arms come
/// after the binder congruences).  Spelled as one `match` on the pair of
/// constructors, as `expr::beq_go` is.  The sort and level-list comparisons
/// are `isEquivLM`/`isEquivListLM`, i.e. through `eqvC`.
pub fn defeq_struct_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    match (&a.0.kind, &b.0.kind) {
        (ExprKind::Sort(u), ExprKind::Sort(v)) => {
            let eq = state_c::is_equiv_l_m(st, u, v);
            core_k::lift_fueled(eq)
        }
        (ExprKind::Lit(l1), ExprKind::Lit(l2)) => Ok(expr::literal_beq(l1, l2)),
        (ExprKind::Lit(Literal::NatVal(nn)), ExprKind::Const(c, us)) => {
            if us.len() == 0 && name::beq(c, &basis_names::nat_zero_name()) {
                Ok(nat::is_zero(nn))
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Const(c, us), ExprKind::Lit(Literal::NatVal(nn))) => {
            if us.len() == 0 && name::beq(c, &basis_names::nat_zero_name()) {
                Ok(nat::is_zero(nn))
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Lit(Literal::NatVal(nn)), ExprKind::App(f, x)) => {
            match core_k::succ_of(nn, f) {
                Some(k) => {
                    let lk = expr::lit(expr::literal_nat(k));
                    defeq(mode, fuel, st, fe, depth, &lk, x)
                }
                None => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            }
        }
        (ExprKind::App(f, x), ExprKind::Lit(Literal::NatVal(nn))) => {
            match core_k::succ_of(nn, f) {
                Some(k) => {
                    let lk = expr::lit(expr::literal_nat(k));
                    defeq(mode, fuel, st, fe, depth, x, &lk)
                }
                None => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            }
        }
        (ExprKind::Lit(Literal::StrVal(s)), ExprKind::App(f, _)) => {
            if core_k::str_expansion_fires(fe, f) {
                let c = core_k::str_lit_to_constructor(s);
                defeq(mode, fuel, st, fe, depth, &c, b)
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::App(f, _), ExprKind::Lit(Literal::StrVal(s))) => {
            if core_k::str_expansion_fires(fe, f) {
                let c = core_k::str_lit_to_constructor(s);
                defeq(mode, fuel, st, fe, depth, a, &c)
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Fvar(i, _), ExprKind::Fvar(j, _)) => {
            if *i == *j {
                Ok(true)
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Const(n1, us1), ExprKind::Const(n2, us2)) => {
            if name::beq(n1, n2) {
                let eq = state_c::is_equiv_list_l_m(st, us1, us2);
                match core_k::lift_fueled(eq) {
                    Err(err) => Err(err),
                    Ok(true) => Ok(true),
                    Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
                }
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::ForallE(t1, b1, m1), ExprKind::ForallE(t2, b2, m2)) => {
            defeq_binders_i(mode, fuel, st, fe, depth, t1, b1, m1, t2, b2, m2, true)
        }
        (ExprKind::Lam(t1, b1, m1), ExprKind::Lam(t2, b2, m2)) => {
            defeq_binders_i(mode, fuel, st, fe, depth, t1, b1, m1, t2, b2, m2, false)
        }
        (ExprKind::App(_, _), ExprKind::App(_, _)) => {
            defeq_apps_i(mode, fuel, st, fe, depth, a, b)
        }
        (ExprKind::Proj(s1, i1, e1), ExprKind::Proj(s2, i2, e2)) => {
            if name::beq(s1, s2) && *i1 == *i2 {
                let e1 = expr::dup(e1);
                let e2 = expr::dup(e2);
                match defeq(mode, fuel, st, fe, depth, &e1, &e2) {
                    Err(err) => Err(err),
                    Ok(true) => Ok(true),
                    Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
                }
            } else {
                stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
            }
        }
        (ExprKind::Lam(t1, b1, m1), _) => {
            let t1 = expr::dup(t1);
            let b1 = expr::dup(b1);
            let m1 = expr::binder_meta_dup(m1);
            match eta_cert_i(mode, fuel, st, fe, depth, &t1, &b1, &m1, b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            }
        }
        (_, ExprKind::Lam(t2, b2, m2)) => {
            let t2 = expr::dup(t2);
            let b2 = expr::dup(b2);
            let m2 = expr::binder_meta_dup(m2);
            match eta_cert_i(mode, fuel, st, fe, depth, &t2, &b2, &m2, a) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            }
        }
        _ => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Binder congruence, the ∀ and λ arms together (they are byte-identical
/// apart from the message tag): the domains, then the bodies at a fresh
/// variable of the *right* side's domain — opened with `inst1M` — and
/// **last** the two prop-ness annotations at the verified modes.
pub fn defeq_binders_i(
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
        115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 102, 111, 114, 97, 108,
        108, 41,
    ];
    const M_LAM: [u32; 36] = [
        115, 111, 114, 116, 45, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 32, 109, 105,
        115, 109, 97, 116, 99, 104, 32, 40, 100, 101, 102, 101, 113, 45, 108, 97, 109, 41,
    ];
    match defeq(mode, fuel, st, fe, depth, t1, t2) {
        Err(err) => Err(err),
        Ok(false) => Ok(false),
        Ok(true) => {
            let v = expr::fvar(depth, expr::dup(t2));
            let o1 = state_c::inst1_m(b1, &v, 0);
            let o2 = state_c::inst1_m(b2, &v, 0);
            match defeq(mode, fuel, st, fe, depth + 1, &o1, &o2) {
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

/// con-leche: ConLeche/Cached/CoreC.lean:1455-1614 defeqStepI
/// con-leche: ConLeche/Kernel/Core.lean:2371-2631 defeqStep
/// Stuck applications: **spine-wise** congruence (the official kernel's
/// `is_def_eq_app`) — equal spine lengths, one head comparison, then the
/// argument lists pairwise, then the stuck fallbacks.
pub fn defeq_apps_i(
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
        stuck_irrel_i(mode, fuel, st, fe, depth, a, b)
    } else {
        let fa = expr_ops::get_app_fn(a);
        let fb = expr_ops::get_app_fn(b);
        match defeq(mode, fuel, st, fe, depth, &fa, &fb) {
            Err(err) => Err(err),
            Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            Ok(true) => match def_eq_list_i(mode, fuel, st, fe, depth, &args_a, &args_b) {
                Err(err) => Err(err),
                Ok(true) => Ok(true),
                Ok(false) => stuck_irrel_i(mode, fuel, st, fe, depth, a, b),
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1616-1621 defeqLoopI
/// con-leche: ConLeche/Kernel/Core.lean:2633-2638 defeqLoop
/// The lazy-delta loop: iterate `defeq_step_i` on its own step budget.
pub fn defeq_loop_i(
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
        defeq_step_i(mode, fuel, st, fe, depth, n - 1, pi, a, b)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1623-1625 defeqBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2646-2649 defeqBody
/// The definitional-equality body: the lazy-delta loop at its own step
/// budget (`core_k::defeq_loop_fuel`), entered at `pi = true`.
pub fn defeq_body_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    defeq_loop_i(
        mode,
        fuel,
        st,
        fe,
        depth,
        core_k::defeq_loop_fuel(),
        true,
        a,
        b,
    )
}

/// con-leche: ConLeche/Cached/CoreC.lean:1627-1634 isPropTypeI
/// con-leche: ConLeche/Kernel/Core.lean:2651-2660 isPropType
/// Check that a (raw) type is a `Prop` by annotating it and inferring its
/// sort.  The inference is at the io grade: `ty'` is the pass's own output,
/// already annotated — the bottom-up circularity guard.  The comparison is
/// `isEquivLM`, through `eqvC`.
pub fn is_prop_type_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
) -> CheckM<bool> {
    match annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => match infer_io(mode, fuel, st, fe, depth, &ty2) {
            Err(err) => Err(err),
            Ok(t) => match ensure_sort_i(mode, fuel, st, fe, depth, &t) {
                Err(err) => Err(err),
                Ok(s) => {
                    let eq = state_c::is_equiv_l_m(st, &s, &level::zero());
                    core_k::lift_fueled(eq)
                }
            },
        },
    }
}

// ---------------------------------------------------------------------------
// The annotation pass and its telescope loops (`CoreC.lean:1643-1867`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI
/// **Rebuild loop of the annotation binder-telescope loops**: fold the stack
/// (innermost binder first, `j` its binder level), rebuilding one binder
/// node per entry with one `abstractRangeM` per domain.
///
/// con-leche's task #161 P5, the untrusted write: `pw?` is the datum written
/// just below, **threaded outward** (`zeronessOf (imax u v) = zeronessOf v`
/// makes every ∀ node's codomain-sort zero-ness its inner neighbour's, and
/// the λ chain rule says the same of λ nodes — so the telescope pays one
/// computation, in the leaf phase, and every node above reads).  `None` = no
/// write.  A node whose input datum is a real annotation (`pwWritten`) is
/// left alone — validation judges it, and it is that datum that travels on.
///
/// Deviations: the cited `mk` node constructor is the `is_forall` flag (the
/// module note's point 6), the `List` stack is a `Vec` walked downwards by
/// `p`, and `pw?.map (fun _ => …)` is a `match` (§3.4 forbids closures).
pub fn annotate_binders_out_i(
    is_forall: bool,
    d: u64,
    pw: Option<PropWhen>,
    stk: &Vec<AnnotBinderEntry>,
    p: usize,
    j: u64,
    cur: Expr,
) -> Expr {
    if p == 0 || p > stk.len() {
        cur
    } else {
        let ent: &AnnotBinderEntry = &stk[p - 1];
        let ty_abs = state_c::abstract_range_m(&ent.0, d, j);
        let mb = core_k::annot_binder_meta(annot_pw_dup_i(&pw), &ent.1);
        let next = annot_pw_thread_i(&pw, &mb);
        let node = annot_node_i(is_forall, ty_abs, cur, mb);
        annotate_binders_out_i(
            is_forall,
            d,
            next,
            stk,
            p - 1,
            expr_ops::sub_nat(j, 1),
            node,
        )
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI
/// The cited `mk tyAbs cur (annotBinderMetaI pw? mb)`: the node constructor
/// the Lean passes as a function argument, as the `is_forall` flag (the
/// module note's point 6) — and as its **own function**, because written
/// inline the flag's two arms consume the same three owned values and join,
/// which Aeneas answered with *"Could not match the contexts"* (one of task
/// #23's four errors).  Inside a callee the join is on a value with no
/// borrows in it.
pub fn annot_node_i(is_forall: bool, ty: Expr, body: Expr, mb: BinderMeta) -> Expr {
    if is_forall {
        expr::forall_e(ty, body, mb)
    } else {
        expr::lam(ty, body, mb)
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI
/// The cited `pw?.map fun _ => (annotBinderMetaI pw? mb).pw` — the datum
/// *just written*, threaded outward, as its own function: written inline it
/// is a `match` on a borrow of the parameter joining on an `Option`, which
/// Aeneas answered with *"Could not match the contexts"* (one of task #23's
/// four errors; task #14's rule again).
pub fn annot_pw_thread_i(pw: &Option<PropWhen>, mb: &BinderMeta) -> Option<PropWhen> {
    match pw {
        Some(_) => Some(prop_when::dup(&mb.pw)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1649-1676 annotateBindersOutI
/// `Option.map PropWhen.dup` — the threaded datum is read twice per entry
/// (once by `annotBinderMetaI`, once by the fold's own `map`) and `PropWhen`
/// is not `Copy`, so the port copies it (Lean's value semantics is free).
pub fn annot_pw_dup_i(pw: &Option<PropWhen>) -> Option<PropWhen> {
    match pw {
        Some(p) => Some(prop_when::dup(p)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1678-1691 annotPwPiI
/// con-leche: ConLeche/Kernel/Core.lean:2687-2718 annotPwPi
/// **The ∀ telescope's datum**, computed once: the leaf codomain sort's
/// zero-ness — shared by every node of the telescope because `zeronessOf
/// (imax u v) = zeronessOf v`.  The head-symbol reader comes first
/// (con-leche's task #168 stage 2): it subsumes the chain read and answers
/// most leaves without inference.
pub fn annot_pw_pi_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    body2: &Expr,
) -> CheckM<PropWhen> {
    match prop_read::type_sort_pw(fe, body2) {
        Some(pw) => Ok(pw),
        None => match infer_io(mode, fuel, st, fe, depth, body2) {
            Err(err) => Err(err),
            Ok(bt) => match ensure_sort_i(mode, fuel, st, fe, depth, &bt) {
                Err(err) => Err(err),
                Ok(v) => Ok(level::zeroness_of(&v)),
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1693-1702 annotatePisPwI
/// The telescope loop's write.  **Ungated** since con-leche's ruling of
/// 2026-09-06: writing the datum is part of the real checker's algorithm
/// (the readers and the licences consume it); only *validating* it is
/// certification-only work, so the trusted mode annotates exactly as the
/// verified mode does.  The `Option` shape is kept —
/// `core_k::annot_binder_meta` still leaves an already-written annotation
/// alone.
pub fn annotate_pis_pw_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    k: u64,
    leaf2: &Expr,
) -> CheckM<Option<PropWhen>> {
    match annot_pw_pi_i(mode, fuel, st, fe, d + k, leaf2) {
        Err(err) => Err(err),
        Ok(p) => Ok(Some(p)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1704-1713 annotatePisLeafI
/// Leaf phase of `annotate_pis_i`: bulk-open and annotate the residual body,
/// compute the telescope's datum, then rebuild outward.
pub fn annotate_pis_leaf_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    t: &Expr,
    k: u64,
    fvs: &Vec<Expr>,
    stk: &Vec<AnnotBinderEntry>,
) -> CheckM<Expr> {
    let to = state_c::inst_list_rev_m(t, fvs, 0);
    match annotate(mode, fuel, st, fe, d + k, &to) {
        Err(err) => Err(err),
        Ok(leaf2) => match annotate_pis_pw_i(mode, fuel, st, fe, d, k, &leaf2) {
            Err(err) => Err(err),
            Ok(pw) => {
                let cur = state_c::abstract_range_m(&leaf2, d, k);
                Ok(annotate_binders_out_i(
                    true,
                    d,
                    pw,
                    stk,
                    stk.len(),
                    expr_ops::sub_nat(k, 1),
                    cur,
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1715-1730 annotatePisI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// **∀-telescope annotation loop** (con-leche's task #72): peel the raw
/// ∀-chain, annotating each opened domain on the way in.  `k ≥ 1` counts the
/// opened binders (the caller peels the first inline), `fvs` their free
/// variables.
pub fn annotate_pis_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    peel: u64,
    t: &Expr,
    k: u64,
    fvs: Vec<Expr>,
    stk: Vec<AnnotBinderEntry>,
) -> CheckM<Expr> {
    if peel == 0 {
        annotate_pis_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk)
    } else {
        match &t.0.kind {
            ExprKind::ForallE(ty, body, mb) => {
                let body = expr::dup(body);
                let mb = expr::binder_meta_dup(mb);
                let tyo = state_c::inst_list_rev_m(ty, &fvs, 0);
                match annotate(mode, fuel, st, fe, d + k, &tyo) {
                    Err(err) => Err(err),
                    Ok(ty2) => {
                        let fv = expr::fvar(d + k, expr::dup(&ty2));
                        let mut fvs = fvs;
                        fvs.push(fv);
                        let mut stk = stk;
                        stk.push((ty2, mb));
                        annotate_pis_i(
                            mode,
                            fuel,
                            st,
                            fe,
                            d,
                            peel - 1,
                            &body,
                            k + 1,
                            fvs,
                            stk,
                        )
                    }
                }
            }
            _ => annotate_pis_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1732-1745 annotPwLamI
/// con-leche: ConLeche/Kernel/Core.lean:2720-2734 annotPwLam
/// **The λ chain's datum**: the zero-ness of the sort of the innermost
/// body's TYPE; every λ node of the chain shares it (the
/// `(lam-cod-chain)` rule).  The reader comes first, as in the spec.
pub fn annot_pw_lam_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    body2: &Expr,
) -> CheckM<PropWhen> {
    match prop_read::proof_pw(fe, body2) {
        Some(pw) => Ok(pw),
        None => match infer_io(mode, fuel, st, fe, depth, body2) {
            Err(err) => Err(err),
            Ok(bt) => match infer_io(mode, fuel, st, fe, depth, &bt) {
                Err(err) => Err(err),
                Ok(btt) => match ensure_sort_i(mode, fuel, st, fe, depth, &btt) {
                    Err(err) => Err(err),
                    Ok(vb) => Ok(level::zeroness_of(&vb)),
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1747-1751 annotateLamsPwI
/// The λ twin of `annotate_pis_pw_i`, ungated with it.
pub fn annotate_lams_pw_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    k: u64,
    leaf2: &Expr,
) -> CheckM<Option<PropWhen>> {
    match annot_pw_lam_i(mode, fuel, st, fe, d + k, leaf2) {
        Err(err) => Err(err),
        Ok(p) => Ok(Some(p)),
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1753-1762 annotateLamsLeafI
/// Leaf phase of `annotate_lams_i` (as `annotate_pis_leaf_i`, rebuilding
/// λ-nodes).
pub fn annotate_lams_leaf_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    t: &Expr,
    k: u64,
    fvs: &Vec<Expr>,
    stk: &Vec<AnnotBinderEntry>,
) -> CheckM<Expr> {
    let to = state_c::inst_list_rev_m(t, fvs, 0);
    match annotate(mode, fuel, st, fe, d + k, &to) {
        Err(err) => Err(err),
        Ok(leaf2) => match annotate_lams_pw_i(mode, fuel, st, fe, d, k, &leaf2) {
            Err(err) => Err(err),
            Ok(pw) => {
                let cur = state_c::abstract_range_m(&leaf2, d, k);
                Ok(annotate_binders_out_i(
                    false,
                    d,
                    pw,
                    stk,
                    stk.len(),
                    expr_ops::sub_nat(k, 1),
                    cur,
                ))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1764-1777 annotateLamsI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// **λ-telescope annotation loop** (con-leche's task #72).
pub fn annotate_lams_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    peel: u64,
    t: &Expr,
    k: u64,
    fvs: Vec<Expr>,
    stk: Vec<AnnotBinderEntry>,
) -> CheckM<Expr> {
    if peel == 0 {
        annotate_lams_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk)
    } else {
        match &t.0.kind {
            ExprKind::Lam(ty, body, mb) => {
                let body = expr::dup(body);
                let mb = expr::binder_meta_dup(mb);
                let tyo = state_c::inst_list_rev_m(ty, &fvs, 0);
                match annotate(mode, fuel, st, fe, d + k, &tyo) {
                    Err(err) => Err(err),
                    Ok(ty2) => {
                        let fv = expr::fvar(d + k, expr::dup(&ty2));
                        let mut fvs = fvs;
                        fvs.push(fv);
                        let mut stk = stk;
                        stk.push((ty2, mb));
                        annotate_lams_i(
                            mode,
                            fuel,
                            st,
                            fe,
                            d,
                            peel - 1,
                            &body,
                            k + 1,
                            fvs,
                            stk,
                        )
                    }
                }
            }
            _ => annotate_lams_leaf_i(mode, fuel, st, fe, d, t, k, &fvs, &stk),
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// **The annotation body**: compute the codomain-sort annotations of every
/// binder, bottom-up, by real inference on the opened (already annotated)
/// body.  The `.app` clause is structural — the application rule is not
/// checked here; the inference sweep that follows re-checks every
/// application and every binder body and validates each annotation against
/// its own result.  The `∀` and `λ` chains go to the telescope loops.
///
/// The body reads no mode function at all, which is why `CoreC.lean` gives
/// the annotation pass **one** named core for both modes; `mode` is here
/// only to reach the wrappers (the module note's deviation 1).
pub fn annotate_body_i(
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
            if core_k::nat_lit_supported(fe) {
                Ok(expr::dup(e))
            } else {
                Err(core_types::invalid(core_types::code_points(&M_NAT)))
            }
        }
        ExprKind::Lit(Literal::StrVal(_)) => {
            if core_k::str_lit_supported(fe) {
                Ok(expr::dup(e))
            } else {
                Err(core_types::not_implemented(core_types::code_points(&M_STR)))
            }
        }
        ExprKind::App(f, a) => match annotate(mode, fuel, st, fe, depth, f) {
            Err(err) => Err(err),
            Ok(f2) => match annotate(mode, fuel, st, fe, depth, a) {
                Err(err) => Err(err),
                Ok(a2) => Ok(expr::app(f2, a2)),
            },
        },
        ExprKind::ForallE(ty, body, mb) => {
            annotate_forall_i(mode, fuel, st, fe, depth, ty, body, mb)
        }
        ExprKind::Lam(ty, body, mb) => {
            if state_c::bvar_bound_m(e) == 0 {
                annotate_lam_loop_i(mode, fuel, st, fe, depth, ty, body, mb)
            } else {
                annotate_lam_chain_i(mode, fuel, st, fe, depth, ty, body, mb)
            }
        }
        ExprKind::LetE(ty, v, b) => annotate_let_i(mode, fuel, st, fe, depth, ty, v, b),
        ExprKind::Proj(sn, i, pe) => {
            annotate_proj_i(mode, fuel, st, fe, depth, sn, *i, pe)
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// The `∀` clause: annotate the first domain inline, then peel the whole
/// chain with `annotate_pis_i`.
pub fn annotate_forall_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    match annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => {
            let fv = expr::fvar(depth, expr::dup(&ty2));
            let mut fvs: Vec<Expr> = Vec::new();
            fvs.push(fv);
            let mut stk: Vec<AnnotBinderEntry> = Vec::new();
            stk.push((ty2, expr::binder_meta_dup(mb)));
            annotate_pis_i(
                mode,
                fuel,
                st,
                fe,
                depth,
                state_c::peel_fuel(),
                body,
                1,
                fvs,
                stk,
            )
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// The `λ` clause's **loop** arm: taken only when the node is bvar-closed
/// (`bvarBoundM e = 0`, an `O(1)` read of the cached bound), because the
/// λ-loop is chain-identical only there — the chained tails re-open exactly
/// what they closed.  Disciplined inputs always are.
pub fn annotate_lam_loop_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    match annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => {
            let fv = expr::fvar(depth, expr::dup(&ty2));
            let mut fvs: Vec<Expr> = Vec::new();
            fvs.push(fv);
            let mut stk: Vec<AnnotBinderEntry> = Vec::new();
            stk.push((ty2, expr::binder_meta_dup(mb)));
            annotate_lams_i(
                mode,
                fuel,
                st,
                fe,
                depth,
                state_c::peel_fuel(),
                body,
                1,
                fvs,
                stk,
            )
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The `λ` clause's **chained** arm (a node with loose bvars): the spec
/// body's own clause — annotate the domain, annotate the body opened at a
/// variable of the *annotated* domain, and write the datum unless the input
/// carries a real one (con-leche's task #161 P5: the single-binder write, the
/// λ-loop's rule at a chain of length one).
pub fn annotate_lam_chain_i(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    depth: u64,
    ty: &Expr,
    body: &Expr,
    mb: &BinderMeta,
) -> CheckM<Expr> {
    match annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => {
            let fv = expr::fvar(depth, expr::dup(&ty2));
            let ob = state_c::inst1_m(body, &fv, 0);
            match annotate(mode, fuel, st, fe, depth + 1, &ob) {
                Err(err) => Err(err),
                Ok(body2) => {
                    let b_abs = state_c::abstract1_m(&body2, depth);
                    let pw = if !core_k::pw_written(&mb.pw) {
                        annot_pw_lam_i(mode, fuel, st, fe, depth + 1, &body2)
                    } else {
                        Ok(prop_when::dup(&mb.pw))
                    };
                    match pw {
                        Err(err) => Err(err),
                        Ok(p) => Ok(expr::lam(ty2, b_abs, expr::binder_meta(p))),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The `.letE` clause: the official `infer_let` triple —
/// `ensureSortI(infer(type))`, `infer(val)`, `defeq(val_type, type)` — runs
/// HERE, on the annotated annotation and the annotated value, before the ζ
/// reduct is taken (con-leche's task #217).  The body is annotated *with the
/// value transparent*, i.e. as its ζ reduct, and the reduct substitutes the
/// **raw** `v`, not the annotated `v'` — the Lean's own spelling.
pub fn annotate_let_i(
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
    match annotate(mode, fuel, st, fe, depth, ty) {
        Err(err) => Err(err),
        Ok(ty2) => match infer(mode, fuel, st, fe, depth, &ty2) {
            Err(err) => Err(err),
            Ok(tty) => match ensure_sort_i(mode, fuel, st, fe, depth, &tty) {
                Err(err) => Err(err),
                Ok(_) => match annotate(mode, fuel, st, fe, depth, v) {
                    Err(err) => Err(err),
                    Ok(v2) => match infer(mode, fuel, st, fe, depth, &v2) {
                        Err(err) => Err(err),
                        Ok(tv) => match defeq(mode, fuel, st, fe, depth, &tv, &ty2) {
                            Err(err) => Err(err),
                            Ok(false) => {
                                Err(core_types::invalid(core_types::code_points(&M)))
                            }
                            Ok(true) => {
                                let red = state_c::inst1_m(b, v, 0);
                                annotate(mode, fuel, st, fe, depth, &red)
                            }
                        },
                    },
                },
            },
        },
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1779-1867 annotateBodyI
/// con-leche: ConLeche/Kernel/Core.lean:2736-2856 annotateBody
/// The `.proj` clause: run the projection rule (the one place it is
/// checked).  A table entry types the node directly, and the display name is
/// normalized to the type's head so reduction's table lookup is complete on
/// annotated terms — but the node's OWN structure name is official's
/// `infer_proj` premise and is checked HERE (con-leche's task #271).  The
/// table lookup and its three verdicts are `core_k::annotate_proj_entry`,
/// which the twin spells identically.
pub fn annotate_proj_i(
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
    match annotate(mode, fuel, st, fe, depth, pe) {
        Err(err) => Err(err),
        Ok(e2) => match infer_io_whnf_i(mode, fuel, st, fe, depth, &e2) {
            Err(err) => Err(err),
            Ok(te) => {
                let f = expr_ops::get_app_fn(&te);
                match &f.0.kind {
                    ExprKind::Const(t, _) => {
                        let targs = expr_ops::get_app_args(&te);
                        core_k::annotate_proj_entry(fe, sn, t, i, &e2, &targs)
                    }
                    _ => Err(core_types::not_implemented(core_types::code_points(
                        &M_NONSTRUCT,
                    ))),
                }
            }
        },
    }
}

// ---------------------------------------------------------------------------
// The memoized knot (`CoreC.lean:1871-1976`)
// ---------------------------------------------------------------------------
//
// **No generic `memoEI`.**  The Lean's getter/setter pair is two closures,
// which §3.4 forbids; each wrapper therefore spells its own `CState` field
// out, and the probe is a function over a *shared* state borrow (task #14's
// rule: never hold a container's borrow across a branch that touches the
// container).  `@[inline]` on `memoEI` says the Lean does the same thing
// after inlining.
//
// **con-leche's linear-update dance is dropped**, as task #14 recorded: `let
// mp := get' st; let st := set' st ∅; set' st (mp.insert e r)` detaches the
// map so Lean's runtime sees a unique reference; `st.<map>.insert(…)` on a
// `&mut CState` *is* that in-place update.

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `(get' (← get))[e]?` probe of `memoEI` at `CState.whnfCoreC`, over a
/// *shared* state borrow so the map's borrow ends before the miss branch
/// writes.
pub fn whnf_core_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.whnf_core_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `whnfC` probe (see `whnf_core_probe`).
pub fn whnf_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.whnf_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `inferC` probe (see `whnf_core_probe`).
pub fn infer_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.infer_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `inferIOC` probe (see `whnf_core_probe`).
pub fn infer_io_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.infer_io_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// The `annotC` probe (see `whnf_core_probe`).
pub fn annot_probe(st: &CState, e: &Expr) -> Option<Expr> {
    match st.annot_c.get(e) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1891-1904 memoBI
/// The `(← get).defeqC[(a, b)]?` probe of `memoBI` (see `whnf_core_probe`).
pub fn defeq_probe(st: &CState, key: &(Expr, Expr)) -> Option<bool> {
    match st.defeq_c.get(key) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1871-1889 memoEI
/// `(coreKnotI mode fe fuel).whnfCore d e`: the fuel-zero throw, the
/// `whnfCoreC` probe, `whnf_core_body_i` at `fuel - 1`, and the memo insert.
pub fn whnf_core(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 24] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102, 67, 111, 114, 101,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match whnf_core_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_core_body_i(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.whnf_core_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI mode fe fuel).whnf d e`, memoized in `whnfC`.
pub fn whnf(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 20] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 119, 104,
        110, 102,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match whnf_probe(st, e) {
            Some(r) => Ok(r),
            None => match whnf_body_i(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.whnf_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI mode fe fuel).infer d e`, memoized in `inferC`.  The body is
/// tied at the **full** grade (`io = false`), which is the knot's `prev ()`
/// rather than `(prev ()).ioView`.
pub fn infer(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110,
        102, 101, 114,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body_i(mode, fuel - 1, st, fe, d, e, false) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// **The io slot**, selected once per knot level: at `mode.ioGate` the io
/// body under its OWN memo (`inferIOC` — con-leche's task-#170 memo ruling:
/// a hit in the io memo never serves a full-infer query), tied to the
/// io-grade view of the previous level; at `ioGate = false` the full
/// inference body, verbatim, under `inferC`, because the two grades are the
/// same function there.  `CheckMode.ioGate` is `true` at both modes, so the
/// second arm is currently dead — and ported anyway, as in the Lean.
pub fn infer_io(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 105, 110,
        102, 101, 114,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else if env::io_gate(mode) {
        match infer_io_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body_io_i(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_io_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    } else {
        match infer_probe(st, e) {
            Some(r) => Ok(r),
            None => match infer_body_i(mode, fuel - 1, st, fe, d, e, false) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.infer_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// con-leche: ConLeche/Cached/CoreC.lean:1891-1904 memoBI
/// `(coreKnotI mode fe fuel).defeq d a b`, memoized in `defeqC` under the
/// **pair** key `(a, b)` (`memoBI`).  The key is built before the probe, as
/// the Lean's tuple is, and moved into the map on a miss.
pub fn defeq(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    a: &Expr,
    b: &Expr,
) -> CheckM<bool> {
    const M: [u32; 21] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 100, 101,
        102, 101, 113,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        let key = (expr::dup(a), expr::dup(b));
        match defeq_probe(st, &key) {
            Some(r) => Ok(r),
            None => match defeq_body_i(mode, fuel - 1, st, fe, d, a, b) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.defeq_c.insert(key, r);
                    Ok(r)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Cached/CoreC.lean:1906-1976 coreKnotI
/// con-leche: ConLeche/Kernel/Core.lean:2860-2899 coreKnot
/// `(coreKnotI mode fe fuel).annotate d e`, memoized in `annotC`.
pub fn annotate(
    mode: &CheckMode,
    fuel: u64,
    st: &mut CState,
    fe: &FEnv,
    d: u64,
    e: &Expr,
) -> CheckM<Expr> {
    const M: [u32; 24] = [
        102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 97, 110,
        110, 111, 116, 97, 116, 101,
    ];
    if fuel == 0 {
        Err(core_types::internal(core_types::code_points(&M)))
    } else {
        match annot_probe(st, e) {
            Some(r) => Ok(r),
            None => match annotate_body_i(mode, fuel - 1, st, fe, d, e) {
                Err(err) => Err(err),
                Ok(r) => {
                    st.annot_c.insert(expr::dup(e), expr::dup(&r));
                    Ok(r)
                }
            },
        }
    }
}

/* Not ported from `Cached/CoreC.lean` (DESIGN.md §3.1), and why:

   * `structure CoreFnsI` (`:43-58`) and `CoreFnsI.ioView` (`:60-64`) —
     cited, not ported as a type: §3.1 ties the knot with a mutually
     recursive block of plain functions, so there is no record whose `infer`
     field can be rebound.  `ioView` is `infer_at_i`'s `io` flag, and both
     declarations are cited there.
   * `certAtI` (`:297-300`) and `certUnlessI` (`:302-308`) — `@[inline]`
     wrappers taking the certificate as a `CheckCM Bool` *argument*, i.e. a
     closure (§3.4).  Every site spells the wrapper out as `if
     env::certs(mode) { … } else { Ok(true) }` (resp. `if env::certs(mode) ||
     keep`), which is the cited definition after inlining, and each such site
     carries the citation.
   * the four `@[simp] theorem`s about them (`:310-325`) — the wrappers'
     `rfl` identities at the two modes, i.e. the *spec* the simulation tower
     sees them through, not part of the implementation.
   * the seven named concrete cores `whnfCoreBodyPC`/`inferBodyPC`/
     `defeqBodyPC`/`annotateBodyPC` (`:2032-2056`) and `whnfCoreBodyTC`/
     `inferBodyTC`/`defeqBodyTC` (`:2068-2089`) — *definitions, not clones*:
     each is one of the bodies above instantiated at a literal mode.  The
     port's mode is a runtime `&CheckMode` parameter (the module note's
     deviation 1), so `whnf_core_body_i(&CheckMode::Verified, …)` **is**
     `whnfCoreBodyPC` and `whnf_core_body_i(&CheckMode::Trusted, …)` is
     `whnfCoreBodyTC`; a Rust alias per mode would be seven dead functions
     with no content.  `annotateBodyPC` has no `TC` sibling because
     `annotateBodyI` reads no mode — which the port's `annotate_body_i`
     records in its own doc comment.

   Everything else in the file is above.  The `Kernel/Core.lean` bodies these
   twins supersede are **no longer in the crate** (task #23): they threaded
   the same knot, so keeping them would have doubled the mutual block in the
   generated Lean for functions nothing executes.  Their citations are the
   second `con-leche:` line on the twin here. */

#[cfg(test)]
mod tests {
    use crate::cached::core_c;
    use crate::cached::state_c;
    use crate::cached::state_c::CState;
    use crate::kernel::core_k;
    use crate::kernel::env::{CheckMode, ConstantInfo, ConstantVal};
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};
    use crate::kernel::fenv;
    use crate::kernel::fenv::FEnv;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;
    use std::vec::Vec;

    /// A one-character name.
    fn nm(c: u32) -> Name {
        name::mk_str(name::anonymous(), vec![c])
    }

    fn never_meta() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn prop_meta() -> BinderMeta {
        expr::binder_meta(prop_when::if_all_zero(Vec::new()))
    }

    fn ax(n: Name, ty: Expr) -> ConstantInfo {
        ConstantInfo::AxiomInfo(ConstantVal {
            name: n,
            level_params: Vec::new(),
            ty,
        })
    }

    fn a_ty() -> Expr {
        expr::mk_const(nm(65), Vec::new())
    }

    /// `A : Sort 1`, `a : A`, `f : ∀ (_ : A), A` — the same hand-built
    /// environment `core_k`'s tests use (axioms and `Sort`/Π/λ/app terms
    /// only; a `Nat`-like inductive is far too big for a unit test).
    fn env_afa() -> FEnv {
        let ty = a_ty();
        let mut consts: Vec<ConstantInfo> = Vec::new();
        consts.push(ax(
            nm(102),
            expr::forall_e(expr::dup(&ty), expr::dup(&ty), never_meta()),
        ));
        consts.push(ax(nm(97), expr::dup(&ty)));
        consts.push(ax(nm(65), expr::sort(level::succ(level::zero()))));
        fenv::mk_fenv(crate::kernel::env::env_of(&consts))
    }

    fn lp(c: u32) -> Level {
        level::param(nm(c))
    }

    /// **`lsimpC` and `eqvC` — the reconciliation's headline.**  Until task
    /// #23 the core compared levels with `Level.isEquiv` and the two level
    /// memos stayed empty however much work the checker did; `defeqStepI`'s
    /// sort arm is `isEquivLM`, so both maps now fill, and the *second*
    /// comparison of the same pair is a hit that writes nothing.
    #[test]
    fn the_level_memos_are_written_by_the_core() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        // `Sort (max u u)` and `Sort u` are equivalent but not syntactically
        // equal, so the comparison runs the simplifier and the cascade.
        let l = expr::sort(level::max(lp(117), lp(117)));
        let r = expr::sort(lp(117));
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st, &fe, 0, &l, &r) {
            Ok(b) => assert!(b, "`max u u ≡ u`"),
            Err(_) => panic!("defeq failed"),
        }
        assert!(st.eqv_c.len() > 0, "`eqvC` carries the decided comparison");
        assert!(st.lsimp_c.len() > 0, "`lsimpC` carries the simplifications");
        let eqv_n = st.eqv_c.len();
        let lsimp_n = st.lsimp_c.len();
        // the same pair again: a hit in both maps, no new entries
        let again = state_c::is_equiv_l_m(&mut st, &level::max(lp(117), lp(117)), &lp(117));
        assert!(again == Some(true));
        assert!(st.eqv_c.len() == eqv_n, "`eqvC` hit");
        assert!(st.lsimp_c.len() == lsimp_n, "`lsimpC` hit");
        // and the whole `defeq` is a hit in `defeqC` too
        let defeq_n = st.defeq_c.len();
        match core_c::defeq(&mode, core_k::check_fuel(), &mut st, &fe, 0, &l, &r) {
            Ok(b) => assert!(b),
            Err(_) => panic!("defeq failed"),
        }
        assert!(st.defeq_c.len() == defeq_n, "`defeqC` hit");
        assert!(st.eqv_c.len() == eqv_n, "and nothing new below it");
    }

    /// **`instC` — the bulk-instantiation memo.**  `betaPeelI` substitutes
    /// the peeled body with `instListM`, so a β step writes `instC`; a
    /// second step on the same (body, arguments, cursor) triple hits it.
    #[test]
    fn the_bulk_instantiation_memo_is_written_by_beta() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        // `(λ (x : A). f x) a`: the peeled body `f (bvar 0)` has a loose
        // bvar, so the substitution is memoized (a bare `bvar 0` body would
        // be too — `bvarB = 1 > 0`).
        let f = expr::mk_const(nm(102), Vec::new());
        let body = expr::app(f, expr::bvar(0));
        let id = expr::lam(a_ty(), body, never_meta());
        let redex = expr::app(id, expr::dup(&a));
        match core_c::whnf_core(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(_) => (),
            Err(_) => panic!("β reduction failed"),
        }
        assert!(st.inst_c.len() > 0, "`instC` carries the bulk substitution");
        let n = st.inst_c.len();
        // the same triple again, straight through `instListM`: a hit
        let t = expr::app(expr::mk_const(nm(102), Vec::new()), expr::bvar(0));
        let mut vs: Vec<Expr> = Vec::new();
        vs.push(expr::dup(&a));
        let r = state_c::inst_list_m(&mut st, &t, &vs, 0);
        assert!(st.inst_c.len() == n, "`instC` hit — no new entry");
        assert!(expr::beq(
            &r,
            &expr::app(expr::mk_const(nm(102), Vec::new()), expr::dup(&a))
        ));
    }

    /// **The `instC` entry bound.**  `instCCapC` is 32 000 000, so the reset
    /// is tested through `inst_list_m_reset_at`, the cited decision *at the
    /// bound as a parameter* — below the bound the map survives, at it the
    /// map is dropped whole and the next insert starts it over.
    #[test]
    fn the_inst_c_cap_drops_the_whole_memo() {
        let mut st: CState = state_c::cstate_new();
        let mut vs: Vec<Expr> = Vec::new();
        vs.push(expr::sort(level::zero()));
        // three entries, at three distinct subjects
        let _ = state_c::inst_list_m(&mut st, &expr::bvar(0), &vs, 0);
        let _ = state_c::inst_list_m(&mut st, &expr::bvar(1), &vs, 0);
        let _ = state_c::inst_list_m(
            &mut st,
            &expr::app(expr::bvar(0), expr::bvar(0)),
            &vs,
            0,
        );
        assert!(st.inst_c.len() == 3);
        // below the bound: nothing happens
        state_c::inst_list_m_reset_at(&mut st, 4);
        assert!(st.inst_c.len() == 3, "under the cap the memo survives");
        // at the bound: the whole map goes
        state_c::inst_list_m_reset_at(&mut st, 3);
        assert!(st.inst_c.len() == 0, "at the cap the memo is dropped whole");
        // and the production bound is `instCCapC`, which three entries are
        // nowhere near
        let _ = state_c::inst_list_m(&mut st, &expr::bvar(0), &vs, 0);
        state_c::inst_list_m_reset(&mut st);
        assert!(st.inst_c.len() == 1);
        assert!(state_c::inst_c_cap_c() == 32000000);
    }

    /// **`constTyAt` — the level-instantiated stored type.**  `inferBodyI`'s
    /// `.const` clause reads `constTyAtM`, so inferring a constant fills the
    /// map, and inferring it again (past the `inferC` memo, straight through
    /// `constTyAtM`) hits it.
    #[test]
    fn the_stored_type_memo_is_written_by_infer() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        match core_c::infer(&mode, core_k::check_fuel(), &mut st, &fe, 0, &a) {
            Ok(t) => assert!(expr::beq(&t, &a_ty()), "`a : A`"),
            Err(_) => panic!("infer failed"),
        }
        assert!(st.const_ty_at.len() == 1, "`constTyAt` carries `(a, [])`");
        match state_c::const_ty_at_m(&mut st, &fe, &nm(97), &Vec::new()) {
            Ok(t) => assert!(expr::beq(&t, &a_ty())),
            Err(_) => panic!("constTyAtM failed"),
        }
        assert!(st.const_ty_at.len() == 1, "`constTyAt` hit — no new entry");
        // an unknown constant is the cited `.internal` throw, and writes
        // nothing
        match state_c::const_ty_at_m(&mut st, &fe, &nm(122), &Vec::new()) {
            Ok(_) => panic!("an unknown constant must not resolve"),
            Err(_) => (),
        }
        assert!(st.const_ty_at.len() == 1);
    }

    /// **`ienv` — the converted-constant cache, and its pointer-identity
    /// validation** (DESIGN.md §3.2).  `storedTyIdxM` answers with the
    /// cached conversion when the entry's `Expr` tag is the very object the
    /// environment holds, and with the environment's own term otherwise.
    /// The fast path is observable here because the test records a *marked*
    /// conversion under the right tag; the model of `ptr::ptr_eq` is `false`,
    /// so the model takes the slow path and gets the environment's term —
    /// which in the real program is the same value, since `ExprC = Expr` and
    /// the conversion is the identity.
    #[test]
    fn the_converted_constant_cache_is_validated_by_the_tag() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        // the very `Expr` the index holds for `A`'s type
        let stored = match fenv::find(&fe, &nm(65)) {
            Some(ci) => match ci {
                ConstantInfo::AxiomInfo(cv) => expr::dup(&cv.ty),
                _ => panic!("A is an axiom"),
            },
            None => panic!("A is stored"),
        };
        // a conversion that is deliberately *not* the stored term, recorded
        // under the stored term's own tag
        let marked = expr::sort(level::succ(level::succ(level::zero())));
        state_c::record_c_const(
            &mut st,
            nm(65),
            expr::dup(&stored),
            expr::dup(&marked),
            None,
        );
        assert!(st.ienv.len() == 1);
        // the tag validates, so the conversion is what comes back
        let hit = state_c::stored_ty_idx_m(&mut st, &nm(65), &stored);
        assert!(expr::beq(&hit, &marked), "the tag validated");
        // a *rebuilt* object of the same value validates too, because
        // `exprPtrBEq` is structural equality with a pointer shortcut (§3.2:
        // the shortcut is modeled `false`, so the model takes the `beq`
        // branch and gets the same answer)
        let rebuilt = expr::sort(level::succ(level::zero()));
        assert!(expr::beq(&rebuilt, &stored), "same value");
        let same = state_c::stored_ty_idx_m(&mut st, &nm(65), &rebuilt);
        assert!(expr::beq(&same, &marked), "the tag validated structurally");
        // a term of a *different* value does not validate, so the argument
        // comes back unchanged
        let other = expr::sort(level::zero());
        let miss = state_c::stored_ty_idx_m(&mut st, &nm(65), &other);
        assert!(expr::beq(&miss, &other), "the tag did not validate");
        // and a name with no entry at all answers with its argument
        let none = state_c::stored_ty_idx_m(&mut st, &nm(122), &rebuilt);
        assert!(expr::beq(&none, &rebuilt));
        // `constTyAtM` goes through it: `A`'s type is now the conversion
        match state_c::const_ty_at_m(&mut st, &fe, &nm(65), &Vec::new()) {
            Ok(t) => assert!(expr::beq(&t, &marked), "read through `ienv`"),
            Err(_) => panic!("constTyAtM failed"),
        }
    }

    /// **The knot's five expression memos still behave as task #18 pinned
    /// them**, now over the cached bodies: one `whnf` fills `whnfC` and
    /// `whnfCoreC`, a second answers the same term and writes nothing, and
    /// the `inferIOC` memo is kept apart from `inferC` (con-leche's task-#170
    /// ruling) — the io body's results never serve a full-infer query.
    #[test]
    fn the_knot_memos_hit_and_stay_apart() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        let id = expr::lam(a_ty(), expr::bvar(0), prop_meta());
        let redex = expr::app(id, expr::dup(&a));
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(r) => assert!(expr::beq(&r, &a)),
            Err(_) => panic!("whnf failed"),
        }
        assert!(st.whnf_c.len() > 0 && st.whnf_core_c.len() > 0);
        // the β certificate infers `a` at the io grade, so `inferIOC` is
        // written and `inferC` is not
        assert!(st.infer_io_c.len() > 0, "the io memo carries the certificate");
        assert!(st.infer_c.len() == 0, "and the full-infer memo is untouched");
        let sizes = (
            st.whnf_core_c.len(),
            st.whnf_c.len(),
            st.infer_c.len(),
            st.infer_io_c.len(),
            st.defeq_c.len(),
        );
        match core_c::whnf(&mode, core_k::check_fuel(), &mut st, &fe, 0, &redex) {
            Ok(r) => assert!(expr::beq(&r, &a)),
            Err(_) => panic!("whnf failed"),
        }
        assert!(
            sizes
                == (
                    st.whnf_core_c.len(),
                    st.whnf_c.len(),
                    st.infer_c.len(),
                    st.infer_io_c.len(),
                    st.defeq_c.len(),
                ),
            "a second `whnf` writes nothing"
        );
        // a full-grade `infer` of the same term now writes `inferC`, and
        // the io memo's entry is not what answers it
        match core_c::infer(&mode, core_k::check_fuel(), &mut st, &fe, 0, &a) {
            Ok(t) => assert!(expr::beq(&t, &a_ty())),
            Err(_) => panic!("infer failed"),
        }
        assert!(st.infer_c.len() > 0);
    }

    /// **The bodies are the cached ones, end to end**: at `fuel = 0` all six
    /// wrappers throw, and the head-normalization *loop* has its own budget,
    /// so a β chain no longer costs one knot level per step.  `whnfCore` of
    /// `(λ x. (λ y. y) x) a` reduces in one knot level, which the chained
    /// `Core.lean` body could not do.
    #[test]
    fn the_head_normalization_loop_has_its_own_budget() {
        let fe = env_afa();
        let mode = CheckMode::Verified;
        let a = expr::mk_const(nm(97), Vec::new());
        let inner = expr::lam(a_ty(), expr::bvar(0), never_meta());
        let outer = expr::lam(
            a_ty(),
            expr::app(inner, expr::bvar(0)),
            never_meta(),
        );
        let redex = expr::app(outer, expr::dup(&a));
        // one knot level: `fuel = 2` is enough for `whnfCore`'s own wrapper
        // plus the spine head's `whnfCore` call
        let mut st: CState = state_c::cstate_new();
        match core_c::whnf_core(&mode, 3, &mut st, &fe, 0, &redex) {
            Ok(r) => assert!(expr::beq(&r, &a), "the whole chain in one level"),
            Err(_) => panic!("the loop should not charge the knot per step"),
        }
        // and at `fuel = 0` every wrapper throws
        let mut st0: CState = state_c::cstate_new();
        assert!(core_c::whnf_core(&mode, 0, &mut st0, &fe, 0, &a).is_err());
        assert!(core_c::whnf(&mode, 0, &mut st0, &fe, 0, &a).is_err());
        assert!(core_c::infer(&mode, 0, &mut st0, &fe, 0, &a).is_err());
        assert!(core_c::infer_io(&mode, 0, &mut st0, &fe, 0, &a).is_err());
        assert!(core_c::annotate(&mode, 0, &mut st0, &fe, 0, &a).is_err());
        assert!(core_c::defeq(&mode, 0, &mut st0, &fe, 0, &a, &a).is_err());
        assert!(st0.whnf_c.len() == 0 && st0.defeq_c.len() == 0);
    }

    /// **The binder-telescope loops**: `inferBodyI`'s λ clause peels the
    /// whole chain and rebuilds it, so `λ (x : A). λ (y : A). y` types as
    /// `∀ (_ : A), ∀ (_ : A), A` with both binders' data validated, and
    /// `annotateBodyI`'s ∀ loop recomputes a placeholder datum.
    #[test]
    fn the_binder_telescope_loops_peel_and_rebuild() {
        let fe = env_afa();
        let mut st: CState = state_c::cstate_new();
        let mode = CheckMode::Verified;
        // `Sort 1`-valued binders validate to `.never`
        let inner = expr::lam(a_ty(), expr::bvar(0), never_meta());
        let outer = expr::lam(a_ty(), inner, never_meta());
        match core_c::infer(&mode, core_k::check_fuel(), &mut st, &fe, 0, &outer) {
            Ok(t) => {
                let want = expr::forall_e(
                    a_ty(),
                    expr::forall_e(a_ty(), a_ty(), never_meta()),
                    never_meta(),
                );
                assert!(expr::beq(&t, &want), "the rebuilt Π telescope");
            }
            Err(_) => panic!("the λ telescope loop failed"),
        }
        // the ∀ telescope: `∀ (_ : A), ∀ (_ : A), A` is a `Sort 1`, and the
        // annotation pass writes the chain's datum where the input carries
        // the placeholder
        let mut st2: CState = state_c::cstate_new();
        let raw = expr::forall_e(
            a_ty(),
            expr::forall_e(a_ty(), a_ty(), never_meta()),
            never_meta(),
        );
        match core_c::annotate(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &raw) {
            Ok(r) => {
                assert!(expr::beq(&r, &raw), "a validated chain is unchanged");
                match core_c::infer(&mode, core_k::check_fuel(), &mut st2, &fe, 0, &r) {
                    Ok(t) => match &t.0.kind {
                        crate::kernel::expr::ExprKind::Sort(_) => (),
                        _ => panic!("a ∀ types as a sort"),
                    },
                    Err(_) => panic!("infer of the annotated chain failed"),
                }
            }
            Err(_) => panic!("the ∀ annotation loop failed"),
        }
    }
}
