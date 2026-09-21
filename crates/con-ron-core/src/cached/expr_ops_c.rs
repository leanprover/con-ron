//! Port of `ConLeche/Cached/ExprOpsC.lean` — **the syntactic passes memoised
//! on the `ExprC` DAG**: the operations the *executed* checker runs on terms,
//! as opposed to `crate::kernel::expr_ops`' structural specifications.
//!
//! ## Why there are two of nearly every walk
//!
//! `ConLeche/Kernel/ExprOps.lean` is the tier the semantic verification
//! reasons about; this file is what `Cached/CoreC.lean`, `Cached/StateC.lean`,
//! `Cached/CheckerC.lean` and `Cached/ParsedC.lean` actually call, and
//! `ConLeche/Verify/Cached/OpsC.lean` proves each function here equal to its
//! `ConLeche.Expr` counterpart.  The differences are **not** cosmetic and
//! DESIGN.md §3.1 makes them binding, so they are reproduced exactly:
//!
//! 1. **A derived-field cutoff at the head of every walk.**  `bvarB ≤ d`
//!    (substitution), `fvarB ≤ d` / `fvarB == 0` (abstraction, scope),
//!    `!hasLP` (level instantiation) return the node **itself**, so the
//!    result shares memory with the input and a later `ptr_eq` on it is
//!    `O(1)`.  `expr_ops`' twins have no such cutoff (the cited header's
//!    "two structural consequences").
//! 2. **Memoise only what is shared** (con-leche's tasks #317 and #319 — ONE
//!    memo discipline for every traversal memo in the tree, `expr::beq_go`
//!    included).  Past the cutoff, a node is probed and recorded only if it is
//!    COMPOUND — a node with no children is answered on the spot, so an entry
//!    for it can never save a descent — and only if
//!    `ron::node::is_exclusive` reports it SHARED.  A node with one reference
//!    is reachable from one place, so the walk that is inside its only parent
//!    meets it once and an entry for it can never be read; skipping it saves
//!    the key, the hash, the bucket and the stored `dup`.  The official
//!    kernel's `replace_fn` caches on exactly that test
//!    (`!is_likely_unshared(e)`).
//!
//!    The two tests are the cited `enter*P` steps, and this port spends them
//!    through `expr_ops::memo1_probe`/`memo1_record` and their four siblings,
//!    which take the verdict and build the key themselves: a key built above
//!    the read would be a second share of the node and the read would answer
//!    `false` everywhere (con-leche's borrowed-parameter requirement,
//!    `ConLeche/Kernel/Exclusive.lean`).  For the four `Bool` walks the
//!    verdict is `memo_skip` below, which folds in the compound test; the
//!    substitution walks make it in their match, as they always did.
//!
//!    `fvar_leaves_go` is **the exception**, and con-leche's is the same one:
//!    its memo is a visited SET whose entries say something about the
//!    accumulator rather than about the node, so it has no self-proving entry
//!    to drop and keeps recording every node it meets (the cited
//!    `fvarLeavesGoC` docstring argues it at length).
//! 3. **The bulk key carries no live prefix.**  `instantiateListXP`'s and
//!    `instantiateRevXP`'s key is `(node, cursor)`, not `(node, cursor,
//!    prefix)`: `k` is invariant over the life of one table, and the `bvar`
//!    arm's re-entry — the one place it shrinks — runs under a **fresh**
//!    table (the cited `MemoNL` docstring).  So `instantiate_list_go` and
//!    `instantiate_rev_go` allocate a table in that arm and nowhere else.
//! 4. **Short-circuiting is memo policy.**  `wscopedBXP`, `leavesSubXP` and
//!    `allLevelParamsDefinedXP` stop at the first `false` and therefore write
//!    *fewer* entries than an unconditional `&&` would.  Task #24's
//!    `expr_ops::bool_and` fix is deliberately **not** applied to those
//!    conjunctions: it computes both operands, which would be a hit where the
//!    Lean misses.  The branching arms are lifted into one-line callees
//!    (`wscoped_b_pair` and friends) instead, so that every arm of a
//!    `&mut`-threaded match still ends in a call, which is the shape Aeneas
//!    accepts (task #24's rule) — same branch, same entries, one more stack
//!    frame.  Where the Lean has already computed both sides
//!    (`allLevelParamsDefinedXP`'s binder arms, `rb && m.pw.paramsDefined`),
//!    `bool_and` is used, as task #24 asks.
//!
//! ## `ExprC` is `Expr`, and `mk*` are the constructors
//!
//! `Cached/ExprC.lean` retired the second expression inductive (con-leche
//! task #172 B3a): `abbrev ExprC := ConLeche.Expr`, and its ten smart
//! constructors are `@[inline]` aliases for the plain ones, with `mkApp_eq`
//! and its nine siblings the `rfl` equations.  So `ExprC.mkApp` is
//! `expr::app` here, `ExprC.mkBVar` is `expr::mk_bvar`, and the file needs no
//! type of its own.  The one `ExprC.lean` *function* the shipped path calls by
//! name, `ExprC.hasFvar`, is ported below rather than left to
//! `expr_ops::has_fvar`, because the cited `ParsedC.lean` docstring turns on
//! the two being different declarations.
//!
//! ## Conventions
//!
//! As `expr_ops`: terms in by shared reference and out owned with an explicit
//! `dup` (a `P` bump) wherever Lean returns a subterm unchanged; `Nat` is
//! `u64` (§3.3); `List`/`Array` is a `Vec` walked by an index helper
//! (`*_from`); a memo is a `crate::ron::hashmap::HashMap` passed as `&mut`,
//! which Aeneas's back-end turns back into the cited threaded `(result, memo)`
//! pair.  The memo keys reuse `expr_ops`' dictionaries (`ExprNatKey`, and the
//! `Expr` ones of `expr.rs`), because they are the same derived
//! `Hashable`/`BEq` instances at the same types.
//!
//! Every memo here is **local** (`{}` per call), as in `expr_ops`: none of
//! them lives in `CState`, so this module adds no field to
//! `crate::cached::state_c`.

use crate::kernel::env::ProjEntry;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::kernel::expr::ExprView;
use crate::kernel::expr_ops;
use crate::kernel::expr_ops::ExprNatKey;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::ron::hashmap::HashMap;
use crate::ron::node;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// `ExprC.lean`'s one executed function
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar
/// The node's fvar flag (`fvarB != 0`), `O(1)`.
///
/// Deviation: this is `expr_ops::has_fvar`'s body character for character,
/// and it is spelled again because the two are different *declarations* —
/// `ExprC.hasFvar` is the `O(1)` field read, `Expr.hasFvar` the walk its
/// `@[csimp]` twin replaces — and `ParsedC.lean`'s own docstring turns on the
/// distinction ("the two `hasFvar`s differ ... which is why the guard below
/// names `ExprC.hasFvar` outright").  Ported here, with `ExprOpsC`, because
/// `leaf_guard` below reads it.
pub fn has_fvar(e: &Expr) -> bool {
    expr_ops::fvar_b(e) != 0
}

// ---------------------------------------------------------------------------
// Spines (`ExprOpsC.lean:63-81`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn
/// The head of an application spine.
pub fn get_app_fn(e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::App(f, _) => get_app_fn(f),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:37-40 getAppArgsAccC
/// Prepend the spine arguments of `e` to `acc` (outermost last).
///
/// Deviation: the cited `a :: acc` is a front cons, which a `Vec` cannot do
/// in `O(1)`; pushing *after* the recursive call produces the same list in
/// one pass (task #13's deviation 3), and the accumulator is threaded by
/// value (task #6's rule).
pub fn get_app_args_acc(e: &Expr, acc: Vec<Expr>) -> Vec<Expr> {
    match expr::view(&e) {
        ExprView::App(f, a) => {
            let mut out: Vec<Expr> = get_app_args_acc(f, acc);
            out.push(expr::dup(a));
            out
        }
        _ => acc,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:42-43 getAppArgsC
/// The arguments of an application spine, outermost last.
pub fn get_app_args(e: &Expr) -> Vec<Expr> {
    get_app_args_acc(e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN
/// Apply to a list of arguments.  The `i = 0` wrapper of the index recursion
/// below (DESIGN.md §3.4).
pub fn mk_app_n(f: Expr, args: &Vec<Expr>) -> Expr {
    mk_app_n_from(f, args, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN
/// The index recursion behind `mk_app_n`.
pub fn mk_app_n_from(f: Expr, args: &Vec<Expr>, i: usize) -> Expr {
    if i >= args.len() {
        f
    } else {
        mk_app_n_from(expr::app(f, expr::dup(&args[i])), args, i + 1)
    }
}

// ---------------------------------------------------------------------------
// The memo table types, and the helpers with no Lean counterpart
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:214-216 MemoXP
/// Memo table for cursored node→node traversals.
///
/// **Deviation: the key is structural, con-leche's is the node's ADDRESS**
/// packed with the cursor (`pkey`, con-leche task #316).  `expr_ops::
/// ExprNatKey` is the `(ExprC × Nat)` dictionary pair — Lean's own derived
/// `Hashable`/`BEq` at the same components (task #14's point 6) — which is
/// what the cited table used before that task and what the model can see; an
/// address is not a value here any more than it is in `beq`'s memo, whose key
/// deviates the same way and for the same reason (`expr::beq_key`).  The
/// discipline the key serves — probe and record only a shared compound node —
/// is the cited one exactly.  Also deviating: the cited `Option (HTab s)`,
/// absent until the first shared node, is a table allocated by the wrapper,
/// as it was before; the wrapper's own cutoff already keeps a decided-outright
/// call away from it.  Erased before Charon, as `core_types::CheckM` is.
pub type MemoN = HashMap<ExprNatKey, Expr>;

/// con-leche: ConLeche/Cached/ExprOpsC.lean:214-216 MemoXP
/// Memo table for the bulk traversals, `(node, cursor)` — **the live prefix
/// `k` is not part of the key** (module note 3).  The same Rust type as
/// `MemoN`, as it is the same Lean type; the two names are kept because the
/// two walks that use it are the bulk ones.  (con-leche's own `MemoNL` went
/// with the structural key at its task #317; the entries of the table that
/// replaced it carry their own proofs, so no invariant is stated of either.)
pub type MemoNL = HashMap<ExprNatKey, Expr>;

/// con-leche: ConLeche/Cached/ExprOpsC.lean:250-252 MemoXP0
/// Memo table for cursor-free node→node traversals.
pub type Memo0 = HashMap<Expr, Expr>;

/// con-leche: none — `args.reverse` of `instSpine`, `targs.reverse` of `typeAtI`
/// `out ++ xs.reverse`, as the downward index recursion `xs[k-1]`, `xs[k-2]`,
/// … (`core_k::rev_append_exprs` is the same helper for `Core.lean`'s own
/// `ProjEntry.typeAt`; a `Vec` reversal copies the spine, as Lean's
/// `List.reverse` allocates).
pub fn rev_append_exprs(out: Vec<Expr>, xs: &Vec<Expr>, k: usize) -> Vec<Expr> {
    if k == 0 || k > xs.len() {
        out
    } else {
        let mut out = out;
        out.push(expr::dup(&xs[k - 1]));
        rev_append_exprs(out, xs, k - 1)
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `(ExprC × Nat)` key, `Bool` values
/// As `expr_ops::memo_b_get`, for `wscopedBGo`'s cursored table: `match
/// memo[k]?` needs the map's borrow to end before the miss branch mutates it
/// (task #13's pattern 1).
pub fn memo_b1_get(memo: &HashMap<ExprNatKey, bool>, k: &ExprNatKey) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:905-910 isCompoundF
/// The nodes a `Bool` memo entry can save a descent of: the compound nodes,
/// and `fvar` — every walk of this section descends into the ANNOTATION, so
/// the cached fvar range does not decide an `fvar` node.
pub fn is_compound_f(e: &Expr) -> bool {
    match expr::view(e) {
        ExprView::Fvar(_, _) => true,
        ExprView::App(_, _) => true,
        ExprView::Lam(_, _, _) => true,
        ExprView::ForallE(_, _, _) => true,
        ExprView::LetE(_, _, _) => true,
        ExprView::Proj(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1017-1027 enterWSP
/// **The `Bool` walks' memo gate** (con-leche's task #319), the two tests its
/// `enter*` steps make past the cutoff, as one predicate: a LEAF is decided
/// on the spot, so an entry for it can never save a descent, and an
/// EXCLUSIVE node — one reference, hence one place it is reachable from —
/// cannot be met again by this walk.  Either way the node costs no key, no
/// probe, no bucket and no stored `dup`.
///
/// Before this the guards recorded every node they decided, leaves included,
/// which is what con-leche measured away.  In the model `is_exclusive` is
/// `false`, so this is `!is_compound_f e` and the leaves are the only nodes
/// the model skips.
pub fn memo_skip(e: &Expr) -> bool {
    if !is_compound_f(e) {
        true
    } else {
        node::is_exclusive(e)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:953-970 MemoB.shared
/// The cursored `Bool` probe, `excl`-gated: an exclusive node is not looked
/// up, so it costs neither the key (which would be a second share of the
/// node — `kernel::expr_ops`'s note on the six helpers) nor the bucket walk.
pub fn memo_b1_probe(
    memo: &HashMap<ExprNatKey, bool>,
    excl: bool,
    e: &Expr,
    d: u64,
) -> Option<bool> {
    if excl {
        None
    } else {
        memo_b1_get(memo, &expr_ops::expr_nat_key(e, d))
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:945-951 MemoB.insert
/// The cursored `Bool` record, `excl`-gated.
pub fn memo_b1_record(
    memo: &mut HashMap<ExprNatKey, bool>,
    excl: bool,
    e: &Expr,
    d: u64,
    r: bool,
) {
    if !excl {
        memo.insert(expr_ops::expr_nat_key(e, d), r);
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `ExprC` key, `Unit` values
/// The `seen` set of `fvarLeavesGo`, probed so the borrow ends at the call.
pub fn seen_get(seen: &HashMap<Expr, ()>, k: &Expr) -> Option<()> {
    match seen.get(k) {
        Some(_) => Some(()),
        None => None,
    }
}

// ---------------------------------------------------------------------------
// `instantiate1` (`ExprOpsC.lean:83-151`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:373-404 instantiate1XP
/// Core of `instantiate1`: replace `bvar d` by `v`, lowering the loose
/// `bvar`s above `d` by one.  The `bvarB ≤ d` cutoff returns the node itself;
/// the five atom kinds are answered on the spot; the five compound kinds
/// build the key once and probe, then insert (module notes 1 and 2).
pub fn instantiate1_go(v: &Expr, memo: &mut MemoN, e: &Expr, d: u64) -> Expr {
    if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i == d {
                    expr::dup(v)
                } else if *i > d {
                    expr::mk_bvar(*i - 1)
                } else {
                    expr::dup(e)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, d) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = instantiate1_go(v, memo, f, d);
                                let a2: Expr = instantiate1_go(v, memo, a, d);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = instantiate1_go(v, memo, ty, d);
                                let b: Expr = instantiate1_go(v, memo, body, d + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = instantiate1_go(v, memo, ty, d);
                                let b: Expr = instantiate1_go(v, memo, body, d + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = instantiate1_go(v, memo, ty, d);
                                let w: Expr = instantiate1_go(v, memo, val, d);
                                let b: Expr = instantiate1_go(v, memo, body, d + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = instantiate1_go(v, memo, sub, d);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, d, &r);
                        r
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// `instantiate1Lift` (`ExprOpsC.lean:153-273`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:305-336 instantiate1LiftXP
/// The memoised descent, in `instantiate1Go`'s shape: the `bvar` arm lifts
/// `v`'s own loose variables past the binders crossed on the way, which is
/// what `instantiate1` may not do.
pub fn instantiate1_lift_go(v: &Expr, memo: &mut MemoN, e: &Expr, d: u64) -> Expr {
    if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i == d {
                    expr_ops::lift_loose_bvars(d, 0, v)
                } else if *i > d {
                    expr::mk_bvar(*i - 1)
                } else {
                    expr::dup(e)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, d) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = instantiate1_lift_go(v, memo, f, d);
                                let a2: Expr = instantiate1_lift_go(v, memo, a, d);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = instantiate1_lift_go(v, memo, ty, d);
                                let b: Expr = instantiate1_lift_go(v, memo, body, d + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = instantiate1_lift_go(v, memo, ty, d);
                                let b: Expr = instantiate1_lift_go(v, memo, body, d + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = instantiate1_lift_go(v, memo, ty, d);
                                let w: Expr = instantiate1_lift_go(v, memo, val, d);
                                let b: Expr = instantiate1_lift_go(v, memo, body, d + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = instantiate1_lift_go(v, memo, sub, d);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, d, &r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:338-341 instantiate1LiftC
/// `Expr.instantiate1Lift` on `ExprC`: the cutoff, then the walk.  The
/// budgeted plain descent at 4 096 nodes that used to stand in front of it is
/// gone with con-leche's own (its task #317 ruling: a node budget is a
/// heuristic cutoff, and the memo discipline that replaced it spends nothing
/// on a small term because it spends nothing on an unshared node).
/// Deviation: the cited
/// `(d : Nat := 0)` default is an explicit argument (Rust has no field or
/// parameter defaults, task #14's point 2).
pub fn instantiate1_lift(e: &Expr, v: &Expr, d: u64) -> Expr {
    if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        let mut memo: MemoN = HashMap::new();
        instantiate1_lift_go(v, &mut memo, e, d)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:406-409 instantiate1C
/// `Expr.instantiate1` on `ExprC` (fresh per-call memo).
pub fn instantiate1(e: &Expr, v: &Expr, d: u64) -> Expr {
    if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        let mut memo: MemoN = HashMap::new();
        instantiate1_go(v, &mut memo, e, d)
    }
}

// ---------------------------------------------------------------------------
// `instantiateList` (`ExprOpsC.lean:279-368`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:455-504 instantiateListXP
/// Core of the bulk instantiation: `vs` innermost binder first, `k` the live
/// prefix length.  The `bvar` arm re-enters at the replacement with the
/// shorter prefix `i - d` and under a **fresh** table, which is what keeps
/// `k` out of the key (module note 3); it is guarded, so a replacement that
/// is closed at the cursor — the checker substitutes `fvar`s — allocates no
/// table at all.
///
/// Deviations: the cited dependent `if _h : i - d < k` is an ordinary `if`
/// (its only purpose is to put `i - d < k` in scope for the termination
/// obligation, and Aeneas's `partial_fixpoint` carries no measure, so the
/// `termination_by (k, sizeOf e)` block has no counterpart either), and the
/// `i - d = 0 || w.bvarB ≤ d` disjunction is an `if` nest (task #3's
/// pattern 9).
pub fn instantiate_list_go(vs: &Vec<Expr>, memo: &mut MemoNL, e: &Expr, k: u64, d: u64) -> Expr {
    if k == 0 {
        expr::dup(e)
    } else if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i < d {
                    expr::dup(e)
                } else if *i - d < k {
                    instantiate_list_bvar(vs, e, *i - d, d)
                } else {
                    expr::mk_bvar(*i - k)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, d) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = instantiate_list_go(vs, memo, f, k, d);
                                let a2: Expr = instantiate_list_go(vs, memo, a, k, d);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = instantiate_list_go(vs, memo, ty, k, d);
                                let b: Expr = instantiate_list_go(vs, memo, body, k, d + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = instantiate_list_go(vs, memo, ty, k, d);
                                let b: Expr = instantiate_list_go(vs, memo, body, k, d + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = instantiate_list_go(vs, memo, ty, k, d);
                                let w: Expr = instantiate_list_go(vs, memo, val, k, d);
                                let b: Expr = instantiate_list_go(vs, memo, body, k, d + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = instantiate_list_go(vs, memo, sub, k, d);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, d, &r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:455-504 instantiateListXP
/// The `.bvar` arm's inner block at `j = i - d`, which the cited code reaches
/// under `j < k`: the replacement, guarded, and the re-entry under a fresh
/// table.  Lifted into a callee so the arm above ends in a call while the
/// walk's `&mut memo` is live (task #24's rule); the fresh table is this
/// function's own, exactly as the Lean's `{}` is.
pub fn instantiate_list_bvar(vs: &Vec<Expr>, e: &Expr, j: u64, d: u64) -> Expr {
    if (j as usize) < vs.len() {
        let w: &Expr = &vs[j as usize];
        if j == 0 {
            expr::dup(w)
        } else if expr_ops::bvar_b(w) <= d {
            expr::dup(w)
        } else {
            let mut fresh: MemoNL = HashMap::new();
            instantiate_list_go(vs, &mut fresh, w, j, d)
        }
    } else {
        expr::dup(e)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:506-513 instantiateListC
/// `Expr.instantiateList` on `ExprC` (bulk, one memoised DAG pass).  The
/// cited `vs.toArray` is the `Vec` itself, and `a.size` its length.
pub fn instantiate_list(e: &Expr, vs: &Vec<Expr>, d: u64) -> Expr {
    if vs.len() == 0 {
        expr::dup(e)
    } else {
        let mut memo: MemoNL = HashMap::new();
        instantiate_list_go(vs, &mut memo, e, vs.len() as u64, d)
    }
}

// ---------------------------------------------------------------------------
// `instantiateRev` (`ExprOpsC.lean:370-445`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:559-609 instantiateRevXP
/// As `instantiateListGo`, but the replacement array holds the innermost
/// binder **last** (the binder loops' push order — lean4lean's
/// `instantiateRev`).  Same key, same fresh table on re-entry, same
/// deviations.
pub fn instantiate_rev_go(vs: &Vec<Expr>, memo: &mut MemoNL, e: &Expr, k: u64, d: u64) -> Expr {
    if k == 0 {
        expr::dup(e)
    } else if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i < d {
                    expr::dup(e)
                } else if *i - d < k {
                    instantiate_rev_bvar(vs, e, *i - d, d)
                } else {
                    expr::mk_bvar(*i - k)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, d) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = instantiate_rev_go(vs, memo, f, k, d);
                                let a2: Expr = instantiate_rev_go(vs, memo, a, k, d);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = instantiate_rev_go(vs, memo, ty, k, d);
                                let b: Expr = instantiate_rev_go(vs, memo, body, k, d + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = instantiate_rev_go(vs, memo, ty, k, d);
                                let b: Expr = instantiate_rev_go(vs, memo, body, k, d + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = instantiate_rev_go(vs, memo, ty, k, d);
                                let w: Expr = instantiate_rev_go(vs, memo, val, k, d);
                                let b: Expr = instantiate_rev_go(vs, memo, body, k, d + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = instantiate_rev_go(vs, memo, sub, k, d);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, d, &r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:559-609 instantiateRevXP
/// The `.bvar` arm's inner block, reading the replacement from the **end** of
/// the array (`vs[vs.size - 1 - j]`).  Lifted into a callee as
/// `instantiate_list_bvar` is.
pub fn instantiate_rev_bvar(vs: &Vec<Expr>, e: &Expr, j: u64, d: u64) -> Expr {
    if (j as usize) < vs.len() {
        let w: &Expr = &vs[vs.len() - 1 - (j as usize)];
        if j == 0 {
            expr::dup(w)
        } else if expr_ops::bvar_b(w) <= d {
            expr::dup(w)
        } else {
            let mut fresh: MemoNL = HashMap::new();
            instantiate_rev_go(vs, &mut fresh, w, j, d)
        }
    } else {
        expr::dup(e)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:611-616 instantiateRev
/// Bulk instantiation on a reversed accumulator array.
pub fn instantiate_rev(e: &Expr, vs: &Vec<Expr>, d: u64) -> Expr {
    if vs.len() == 0 {
        expr::dup(e)
    } else if expr_ops::bvar_b(e) <= d {
        expr::dup(e)
    } else {
        let mut memo: MemoNL = HashMap::new();
        instantiate_rev_go(vs, &mut memo, e, vs.len() as u64, d)
    }
}

// ---------------------------------------------------------------------------
// Abstraction (`ExprOpsC.lean:447-574`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:647-677 abstract1XP
/// Core of `abstract1`: replace `fvar d` by `bvar k`.  The cutoff is the
/// cached fvar range (a node with `fvarB ≤ d` cannot contain `fvar d`) — the
/// cited documented deviation from the retired arena twin, the same value
/// either way — and the key's second component is the binder cursor.
pub fn abstract1_go(d: u64, memo: &mut MemoN, e: &Expr, k: u64) -> Expr {
    if expr_ops::fvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Fvar(idx, _) => {
                if *idx == d {
                    expr::mk_bvar(k)
                } else {
                    expr::dup(e)
                }
            }
            ExprView::Bvar(_) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, k) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = abstract1_go(d, memo, f, k);
                                let a2: Expr = abstract1_go(d, memo, a, k);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = abstract1_go(d, memo, ty, k);
                                let b: Expr = abstract1_go(d, memo, body, k + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = abstract1_go(d, memo, ty, k);
                                let b: Expr = abstract1_go(d, memo, body, k + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = abstract1_go(d, memo, ty, k);
                                let w: Expr = abstract1_go(d, memo, val, k);
                                let b: Expr = abstract1_go(d, memo, body, k + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = abstract1_go(d, memo, sub, k);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, k, &r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:679-682 abstract1C
/// `Expr.abstract1` on `ExprC`.
pub fn abstract1(e: &Expr, d: u64, k: u64) -> Expr {
    if expr_ops::fvar_b(e) <= d {
        expr::dup(e)
    } else {
        let mut memo: MemoN = HashMap::new();
        abstract1_go(d, &mut memo, e, k)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:715-746 abstractRangeXP
/// Core of `abstractRange`: abstract the block `fvar d … fvar (d + k - 1)`,
/// outermost first.  Same memo discipline as `abstract1Go`.  Deviation: the
/// `.fvar` arm's `d ≤ idx ∧ idx < d + k` is an `if` nest (task #3's
/// pattern 9).
pub fn abstract_range_go(d: u64, k: u64, memo: &mut MemoN, e: &Expr, c: u64) -> Expr {
    if expr_ops::fvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Fvar(idx, _) => {
                if d <= *idx {
                    if *idx < d + k {
                        expr::mk_bvar(c + (d + k - 1 - *idx))
                    } else {
                        expr::dup(e)
                    }
                } else {
                    expr::dup(e)
                }
            }
            ExprView::Bvar(_) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let excl: bool = node::is_exclusive(e);
                match expr_ops::memo1_probe(memo, excl, e, c) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = abstract_range_go(d, k, memo, f, c);
                                let a2: Expr = abstract_range_go(d, k, memo, a, c);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = abstract_range_go(d, k, memo, ty, c);
                                let b: Expr = abstract_range_go(d, k, memo, body, c + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = abstract_range_go(d, k, memo, ty, c);
                                let b: Expr = abstract_range_go(d, k, memo, body, c + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = abstract_range_go(d, k, memo, ty, c);
                                let w: Expr = abstract_range_go(d, k, memo, val, c);
                                let b: Expr = abstract_range_go(d, k, memo, body, c + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(sn, i, sub) => {
                                let s2: Expr = abstract_range_go(d, k, memo, sub, c);
                                expr::proj(name::dup(sn), *i, s2)
                            }
                            _ => expr::dup(e),
                        };
                        expr_ops::memo1_record(memo, excl, e, c, &r);
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:748-755 abstractRangeC
/// `Expr.abstractRange` on `ExprC`; `k = 0` is the identity and skips the
/// traversal, as in the retired arena.
pub fn abstract_range(e: &Expr, d: u64, k: u64, c: u64) -> Expr {
    if k == 0 {
        expr::dup(e)
    } else if expr_ops::fvar_b(e) <= d {
        expr::dup(e)
    } else {
        let mut memo: MemoN = HashMap::new();
        abstract_range_go(d, k, &mut memo, e, c)
    }
}

// ---------------------------------------------------------------------------
// Level instantiation (`ExprOpsC.lean:576-642`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:795-831 instLevelParamsXP
/// Core of `instantiateLevelParams` on `ExprC`: nodes without a level
/// parameter are returned unchanged (the `hasLP` cutoff), and **every other
/// node kind is memoised** — the probe and the insert sit around the whole
/// match, not inside the compound arms, so an atom gets an entry here where
/// `instantiate1Go` would answer it on the spot.  That is the cited shape and
/// §3.1 makes it binding.
pub fn inst_level_params_go(
    ks: &Vec<Name>,
    us: &Vec<Level>,
    memo: &mut Memo0,
    e: &Expr,
) -> Expr {
    if !expr::has_lp(e) {
        expr::dup(e)
    } else {
        let excl: bool = node::is_exclusive(e);
        match expr_ops::memo_e_probe(memo, excl, e) {
            Some(r) => r,
            None => {
                let r: Expr = match expr::view(&e) {
                    ExprView::Bvar(_) => expr::dup(e),
                    ExprView::Lit(_) => expr::dup(e),
                    ExprView::Sort(u) => expr::sort(level::subst(ks, us, u)),
                    ExprView::Const(n, vs) => {
                        expr::mk_const(name::dup(n), expr_ops::levels_subst(ks, us, vs))
                    }
                    ExprView::Fvar(idx, ty) => {
                        let t: Expr = inst_level_params_go(ks, us, memo, ty);
                        expr::fvar(*idx, t)
                    }
                    ExprView::App(f, a) => {
                        let f2: Expr = inst_level_params_go(ks, us, memo, f);
                        let a2: Expr = inst_level_params_go(ks, us, memo, a);
                        expr::app(f2, a2)
                    }
                    ExprView::Lam(ty, body, m) => {
                        let t: Expr = inst_level_params_go(ks, us, memo, ty);
                        let b: Expr = inst_level_params_go(ks, us, memo, body);
                        expr::lam(t, b, expr::binder_meta(level::subst_pw(ks, us, &m.pw)))
                    }
                    ExprView::ForallE(ty, body, m) => {
                        let t: Expr = inst_level_params_go(ks, us, memo, ty);
                        let b: Expr = inst_level_params_go(ks, us, memo, body);
                        expr::forall_e(
                            t,
                            b,
                            expr::binder_meta(level::subst_pw(ks, us, &m.pw)),
                        )
                    }
                    ExprView::LetE(ty, val, body) => {
                        let t: Expr = inst_level_params_go(ks, us, memo, ty);
                        let w: Expr = inst_level_params_go(ks, us, memo, val);
                        let b: Expr = inst_level_params_go(ks, us, memo, body);
                        expr::let_e(t, w, b)
                    }
                    ExprView::Proj(sn, i, sub) => {
                        let s2: Expr = inst_level_params_go(ks, us, memo, sub);
                        expr::proj(name::dup(sn), *i, s2)
                    }
                };
                expr_ops::memo_e_record(memo, excl, e, &r);
                r
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:833-837 instLevelParams
/// `Expr.instantiateLevelParams` on `ExprC`.
pub fn inst_level_params(ks: &Vec<Name>, us: &Vec<Level>, e: &Expr) -> Expr {
    if !expr::has_lp(e) {
        expr::dup(e)
    } else {
        let mut memo: Memo0 = HashMap::new();
        inst_level_params_go(ks, us, &mut memo, e)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:839-858 ProjEntry.typeAtI
/// `ProjEntry.typeAt` on `ExprC`: the same two instantiations through the
/// memoised, **sharing-preserving** operations above.  The spec's
/// `core_k::proj_entry_type_at` calls `expr_ops`' unmemoised walks, whose
/// `bvar` arm re-traverses the replacement, so every occurrence of the
/// subject and of every parameter came back as a fresh *tree* copy of a term
/// that was a DAG — the out-of-memory of DESIGN.md's "affine frontier".
///
/// **Owed reconciliation.**  `core_k::proj_entry_type_at` carries this same
/// citation (task #23 added it while `ExprOpsC` was unported) and is what
/// `core_k::infer_proj_at` — the shared `.proj` clause of both inference
/// bodies — still calls.  Retargeting that one call site here is a two-line
/// change, but it would make `kernel::core_k` depend on `crate::cached`,
/// which task #23 deliberately kept it free of ("its syntactic layer"), so it
/// belongs with whoever next owns that seam.  Until then the executed `.proj`
/// type is the `Expr`-level formula: the same value, at one memo policy short
/// of the cited one.
pub fn proj_entry_type_at_i(
    entry: &ProjEntry,
    us: &Vec<Level>,
    targs: &Vec<Expr>,
    pe: &Expr,
) -> Expr {
    let body: Expr = inst_level_params(&entry.level_params, us, &entry.body);
    let mut vs: Vec<Expr> = Vec::new();
    vs.push(expr::dup(pe));
    let vs: Vec<Expr> = rev_append_exprs(vs, targs, targs.len());
    instantiate_list(&body, &vs, 0)
}

// ---------------------------------------------------------------------------
// Scope queries (`ExprOpsC.lean:644-748`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded
/// `Expr.looseBVarsBounded k` — `O(1)`, because the cached bound is *exact*
/// (the least such `k`).
pub fn loose_bvars_bounded(k: u64, e: &Expr) -> bool {
    expr_ops::bvar_b(e) <= k
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP
/// Core of `wscopedB`: every reachable `fvar` index is below `d`,
/// hereditarily through the annotations — so the cached fvar range does not
/// decide it and the `fvar` children are descended.  The memo is probed
/// before the match, so every node kind gets an entry.
///
/// Deviation: each arm that branches on an intermediate answer is lifted into
/// a callee (`wscoped_b_fvar`, `wscoped_b_pair`, `wscoped_b_triple`), so the
/// arm ends in a call and the `&mut memo` borrow never joins two contexts at
/// the insert (task #24's rule).  The branch itself is kept — it is the
/// Lean's short-circuit, and computing both sides would write memo entries
/// the Lean does not (module note 4).
pub fn wscoped_b_go(memo: &mut HashMap<ExprNatKey, bool>, d: u64, e: &Expr) -> bool {
    if expr_ops::fvar_b(e) == 0 {
        true
    } else {
        let skip: bool = memo_skip(e);
        match memo_b1_probe(memo, skip, e, d) {
            Some(r) => r,
            None => {
                let r: bool = match expr::view(&e) {
                    ExprView::Bvar(_) => true,
                    ExprView::Sort(_) => true,
                    ExprView::Const(_, _) => true,
                    ExprView::Lit(_) => true,
                    ExprView::Fvar(idx, ty) => wscoped_b_fvar(memo, d, *idx, ty),
                    ExprView::App(f, a) => wscoped_b_pair(memo, d, f, a),
                    ExprView::Lam(ty, body, _) => wscoped_b_pair(memo, d, ty, body),
                    ExprView::ForallE(ty, body, _) => wscoped_b_pair(memo, d, ty, body),
                    ExprView::LetE(ty, val, body) => wscoped_b_triple(memo, d, ty, val, body),
                    ExprView::Proj(_, _, sub) => wscoped_b_go(memo, d, sub),
                };
                memo_b1_record(memo, skip, e, d, r);
                r
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP
/// The `.fvar` arm: an index in scope licenses its annotation, which is
/// checked at the *index's own* bound.
pub fn wscoped_b_fvar(memo: &mut HashMap<ExprNatKey, bool>, d: u64, idx: u64, ty: &Expr) -> bool {
    if idx < d {
        wscoped_b_go(memo, idx, ty)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP
/// The two-child arms' short-circuit: the second child is walked only when
/// the first answered `true`.
pub fn wscoped_b_pair(
    memo: &mut HashMap<ExprNatKey, bool>,
    d: u64,
    x: &Expr,
    y: &Expr,
) -> bool {
    if wscoped_b_go(memo, d, x) {
        wscoped_b_go(memo, d, y)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1029-1088 wscopedBXP
/// The `.letE` arm's three-child short-circuit.
pub fn wscoped_b_triple(
    memo: &mut HashMap<ExprNatKey, bool>,
    d: u64,
    x: &Expr,
    y: &Expr,
    z: &Expr,
) -> bool {
    if wscoped_b_go(memo, d, x) {
        wscoped_b_pair(memo, d, y, z)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1090-1095 wscopedBC
/// `Expr.wscopedB d` on `ExprC` (one memoised DAG walk).
pub fn wscoped_b(d: u64, e: &Expr) -> bool {
    let mut memo: HashMap<ExprNatKey, bool> = HashMap::new();
    wscoped_b_go(&mut memo, d, e)
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1097-1151 fvarLeavesGoC
/// Core of `fvarLeaves`: the reachable `fvar` leaves, hereditarily through
/// the annotations, each node visited once — the `seen` set is inserted into
/// *before* the match, so a shared sub-DAG is walked once.
///
/// Deviations: the accumulator is threaded by value and returned (task #6's
/// rule), and the cited `(idx, ty) :: acc` front cons becomes a push, so the
/// list comes out in the reverse order.  Its only consumer is `leafMem`, a
/// membership test, and the `seen` set makes the list duplicate-free, so the
/// *set* is what the cited `leafGuard` reads and it is the same set.
pub fn fvar_leaves_go(
    acc: Vec<(u64, Expr)>,
    seen: &mut HashMap<Expr, ()>,
    e: &Expr,
) -> Vec<(u64, Expr)> {
    if expr_ops::fvar_b(e) == 0 {
        acc
    } else {
        match seen_get(seen, e) {
            Some(_) => acc,
            None => {
                seen.insert(expr::dup(e), ());
                match expr::view(&e) {
                    ExprView::Bvar(_) => acc,
                    ExprView::Sort(_) => acc,
                    ExprView::Const(_, _) => acc,
                    ExprView::Lit(_) => acc,
                    ExprView::Fvar(idx, ty) => {
                        let mut acc2: Vec<(u64, Expr)> = acc;
                        acc2.push((*idx, expr::dup(ty)));
                        fvar_leaves_go(acc2, seen, ty)
                    }
                    ExprView::App(f, a) => {
                        let acc2: Vec<(u64, Expr)> = fvar_leaves_go(acc, seen, f);
                        fvar_leaves_go(acc2, seen, a)
                    }
                    ExprView::Lam(ty, body, _) => {
                        let acc2: Vec<(u64, Expr)> = fvar_leaves_go(acc, seen, ty);
                        fvar_leaves_go(acc2, seen, body)
                    }
                    ExprView::ForallE(ty, body, _) => {
                        let acc2: Vec<(u64, Expr)> = fvar_leaves_go(acc, seen, ty);
                        fvar_leaves_go(acc2, seen, body)
                    }
                    ExprView::LetE(ty, val, body) => {
                        let acc2: Vec<(u64, Expr)> = fvar_leaves_go(acc, seen, ty);
                        let acc3: Vec<(u64, Expr)> = fvar_leaves_go(acc2, seen, val);
                        fvar_leaves_go(acc3, seen, body)
                    }
                    ExprView::Proj(_, _, sub) => fvar_leaves_go(acc, seen, sub),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1153-1155 fvarLeavesC
/// The reachable `fvar` leaves (hereditarily through annotations).
pub fn fvar_leaves(e: &Expr) -> Vec<(u64, Expr)> {
    let mut seen: HashMap<Expr, ()> = HashMap::new();
    fvar_leaves_go(Vec::new(), &mut seen, e)
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem
/// Is `(idx, ty)` in the base leaf list?  The `i = 0` wrapper of the index
/// recursion below; the annotation is compared with `ExprC.beq`
/// (pointer-first, DESIGN.md §3.2).
pub fn leaf_mem(bl: &Vec<(u64, Expr)>, idx: u64, ty: &Expr) -> bool {
    leaf_mem_from(bl, 0, idx, ty)
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1157-1162 leafMem
/// The index recursion behind `leaf_mem`.  Deviation: the cited
/// `(i == idx && t == ty) || leafMem rest idx ty` is an `if` nest (task #3's
/// pattern 9).
pub fn leaf_mem_from(bl: &Vec<(u64, Expr)>, i: usize, idx: u64, ty: &Expr) -> bool {
    if i >= bl.len() {
        false
    } else if bl[i].0 == idx {
        if expr::beq(&bl[i].1, ty) {
            true
        } else {
            leaf_mem_from(bl, i + 1, idx, ty)
        }
    } else {
        leaf_mem_from(bl, i + 1, idx, ty)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP
/// Core of the fabrication-side leaf-subset test (con-leche task #86): every
/// `fvar` leaf of the walked term is one of `bl`.  Memo probed before the
/// match, the branching arms lifted into callees, as in `wscopedBGo`.
pub fn leaves_sub_go(bl: &Vec<(u64, Expr)>, memo: &mut HashMap<Expr, bool>, e: &Expr) -> bool {
    if expr_ops::fvar_b(e) == 0 {
        true
    } else {
        let skip: bool = memo_skip(e);
        match expr_ops::memo_b_probe(memo, skip, e) {
            Some(r) => r,
            None => {
                let r: bool = match expr::view(&e) {
                    ExprView::Bvar(_) => true,
                    ExprView::Sort(_) => true,
                    ExprView::Const(_, _) => true,
                    ExprView::Lit(_) => true,
                    ExprView::Fvar(idx, ty) => leaves_sub_fvar(bl, memo, *idx, ty),
                    ExprView::App(f, a) => leaves_sub_pair(bl, memo, f, a),
                    ExprView::Lam(ty, body, _) => leaves_sub_pair(bl, memo, ty, body),
                    ExprView::ForallE(ty, body, _) => leaves_sub_pair(bl, memo, ty, body),
                    ExprView::LetE(ty, val, body) => leaves_sub_triple(bl, memo, ty, val, body),
                    ExprView::Proj(_, _, sub) => leaves_sub_go(bl, memo, sub),
                };
                expr_ops::memo_b_record(memo, skip, e, r);
                r
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP
/// The `.fvar` arm: a leaf in the base list licenses its annotation.
pub fn leaves_sub_fvar(
    bl: &Vec<(u64, Expr)>,
    memo: &mut HashMap<Expr, bool>,
    idx: u64,
    ty: &Expr,
) -> bool {
    if leaf_mem(bl, idx, ty) {
        leaves_sub_go(bl, memo, ty)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP
/// The two-child arms' short-circuit.
pub fn leaves_sub_pair(
    bl: &Vec<(u64, Expr)>,
    memo: &mut HashMap<Expr, bool>,
    x: &Expr,
    y: &Expr,
) -> bool {
    if leaves_sub_go(bl, memo, x) {
        leaves_sub_go(bl, memo, y)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1197-1256 leavesSubXP
/// The `.letE` arm's three-child short-circuit.
pub fn leaves_sub_triple(
    bl: &Vec<(u64, Expr)>,
    memo: &mut HashMap<Expr, bool>,
    x: &Expr,
    y: &Expr,
    z: &Expr,
) -> bool {
    if leaves_sub_go(bl, memo, x) {
        leaves_sub_pair(bl, memo, y, z)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1264-1268 leafGuard
/// The fabrication leaf guard: every `fvar` leaf of `fab` is one of `base`.
/// `O(1)` off the cached range on an `fvar`-free fabrication, which is why
/// the cited disjunction is spelled here as the early return.
pub fn leaf_guard(fab: &Expr, base: &Expr) -> bool {
    if !has_fvar(fab) {
        true
    } else {
        let bl: Vec<(u64, Expr)> = fvar_leaves(base);
        let mut memo: HashMap<Expr, bool> = HashMap::new();
        leaves_sub_go(&bl, &mut memo, fab)
    }
}

// ---------------------------------------------------------------------------
// Telescope operations (`ExprOpsC.lean:750-787`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1272-1275 instSpineChainC
/// The `instantiate1` chain of `Expr.instSpine`.  The `i = 0` wrapper of the
/// index recursion below.
pub fn inst_spine_chain(args: &Vec<Expr>, t: u64, e: &Expr) -> Expr {
    inst_spine_chain_from(args, 0, t, e)
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1272-1275 instSpineChainC
/// The index recursion behind `inst_spine_chain`; the cursor's `t - 1` is
/// Lean's truncated `Nat` subtraction, hence `expr_ops::sub_nat`.
pub fn inst_spine_chain_from(args: &Vec<Expr>, i: usize, t: u64, e: &Expr) -> Expr {
    if i >= args.len() {
        expr::dup(e)
    } else {
        let e2: Expr = instantiate1(e, &args[i], t);
        inst_spine_chain_from(args, i + 1, expr_ops::sub_nat(t, 1), &e2)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1277-1281 instSpineC
/// `Expr.instSpine` on `ExprC`: the one bulk pass when the spine spans the
/// telescope context, the `instantiate1` chain otherwise.
pub fn inst_spine(args: &Vec<Expr>, t: u64, e: &Expr) -> Expr {
    if (args.len() as u64) == t + 1 {
        let rev: Vec<Expr> = rev_append_exprs(Vec::new(), args, args.len());
        instantiate_list(e, &rev, 0)
    } else {
        inst_spine_chain(args, t, e)
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1283-1303 piResidualAcc
/// Core of `piResidual` in bulk form: peel one `∀`-binder per argument,
/// substituting in one pass at the end.  The `bvar` arm re-enters on the same
/// argument list with the accumulator flushed, which is the cited
/// non-structural recursion (its `termination_by (as.length, acc.length)` has
/// no counterpart: Aeneas's `partial_fixpoint` carries no measure).
///
/// Deviations: the argument list is walked by an index rather than
/// destructured, and `a :: acc` is `expr_ops::cons_expr` — the accumulator's
/// order is what `instantiateList` reads, so the front cons is genuine (task
/// #13's deviation 3).
pub fn pi_residual_acc(acc: Vec<Expr>, e: &Expr, args: &Vec<Expr>, i: usize) -> Option<Expr> {
    if i >= args.len() {
        Some(instantiate_list(e, &acc, 0))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(_, b, _) => {
                let acc2: Vec<Expr> = expr_ops::cons_expr(&args[i], &acc);
                pi_residual_acc(acc2, b, args, i + 1)
            }
            ExprView::Bvar(_) => {
                if acc.len() == 0 {
                    None
                } else {
                    let e2: Expr = instantiate_list(e, &acc, 0);
                    pi_residual_acc(Vec::new(), &e2, args, i)
                }
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1305-1307 piResidual
/// The residual of a `∀`-telescope at an argument spine.
pub fn pi_residual(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    pi_residual_acc(Vec::new(), e, args, 0)
}

// ---------------------------------------------------------------------------
// Level-parameter definedness (`ExprOpsC.lean:789-828`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1351-1421 allLevelParamsDefinedXP
/// Core of `allLevelParamsDefined`: nodes without a level parameter are
/// `true` without traversal (the `hasLP` cutoff), everything else is memoised
/// before the match.  The binder arms' `rb && m.pw.paramsDefined params` is
/// *not* a short-circuit in the Lean — both operands are already computed —
/// so it goes through `expr_ops::bool_and` (task #24's rule); the other
/// conjunctions are short-circuits and are lifted into callees instead
/// (module note 4).
pub fn all_level_params_defined_go(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    e: &Expr,
) -> bool {
    if !expr::has_lp(e) {
        true
    } else {
        let skip: bool = memo_skip(e);
        match expr_ops::memo_b_probe(memo, skip, e) {
            Some(r) => r,
            None => {
                let r: bool = match expr::view(&e) {
                    ExprView::Bvar(_) => true,
                    ExprView::Lit(_) => true,
                    ExprView::Sort(u) => level::all_params_defined(params, u),
                    ExprView::Const(_, us) => {
                        expr_ops::levels_all_params_defined(params, us, 0)
                    }
                    ExprView::Fvar(_, ty) => all_level_params_defined_go(params, memo, ty),
                    ExprView::App(f, a) => alpd_pair(params, memo, f, a),
                    ExprView::Lam(ty, body, m) => alpd_binder(params, memo, ty, body, &m.pw),
                    ExprView::ForallE(ty, body, m) => {
                        alpd_binder(params, memo, ty, body, &m.pw)
                    }
                    ExprView::LetE(ty, val, body) => alpd_triple(params, memo, ty, val, body),
                    ExprView::Proj(_, _, sub) => {
                        all_level_params_defined_go(params, memo, sub)
                    }
                };
                expr_ops::memo_b_record(memo, skip, e, r);
                r
            }
        }
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1351-1421 allLevelParamsDefinedXP
/// The `.app` arm's short-circuit.
pub fn alpd_pair(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    x: &Expr,
    y: &Expr,
) -> bool {
    if all_level_params_defined_go(params, memo, x) {
        all_level_params_defined_go(params, memo, y)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1351-1421 allLevelParamsDefinedXP
/// The two binder arms: the domain short-circuits, and the body's answer is
/// conjoined with the binder datum's *without* short-circuiting, because the
/// cited `(rb && m.pw.paramsDefined params, memo)` has already run both.
pub fn alpd_binder(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    ty: &Expr,
    body: &Expr,
    pw: &PropWhen,
) -> bool {
    if all_level_params_defined_go(params, memo, ty) {
        let rb: bool = all_level_params_defined_go(params, memo, body);
        let rp: bool = prop_when::params_defined(params, pw);
        expr_ops::bool_and(rb, rp)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1351-1421 allLevelParamsDefinedXP
/// The `.letE` arm's three-child short-circuit.
pub fn alpd_triple(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    x: &Expr,
    y: &Expr,
    z: &Expr,
) -> bool {
    if all_level_params_defined_go(params, memo, x) {
        alpd_pair(params, memo, y, z)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/ExprOpsC.lean:1423-1427 allLevelParamsDefinedC
/// `Expr.allLevelParamsDefined params` on `ExprC` (one memoised DAG walk).
pub fn all_level_params_defined(params: &Vec<Name>, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    all_level_params_defined_go(params, &mut memo, e)
}

/* Not ported from `ExprOpsC.lean`: nothing.  All 37 top-level declarations of
   the file are here — the 34 executable ones as Rust functions, the three
   `abbrev` memo tables as the type aliases above — and every one of them is
   on the shipped path:

   * `getAppFn`/`getAppArgsAcc`/`getAppArgs` through `Cached/CoreC.lean`'s
     spine readers and `Cached/StateC.lean`'s environment-index guards;
   * `instantiate1`, `instantiateList`, `instantiateRev`, `abstract1`,
     `abstractRange`, `mkAppN`, `instSpine`, `piResidual` and
     `instLevelParams` through `StateC.lean`'s nine `*M` wrappers, whose
     bodies are `pure (ExprC.…)` — so the port's callers call these functions
     directly (task #14's point 9);
   * `instantiate1LiftB`/`instantiate1LiftGo`/`instantiate1Lift` through
     `CheckerC.lean`'s `instPisAtLiftC` and `structProjBodiesGoC`;
   * `wscopedB` and `leafGuard` (hence `fvarLeaves`, `leafMem`,
     `leavesSubGo`) through `CoreC.lean`'s three η/ι fabrication guards;
   * `ProjEntry.typeAtI` through `CoreC.lean`'s `.proj` inference clause;
   * `looseBVarsBounded` and `allLevelParamsDefined` through
     `Cached/ParsedC.lean`'s and `Cached/Installed.lean`'s declaration
     guards.

   The file has no `theorem` and no memo invariant of its own: the `*_spec`
   equations with `ConLeche.Expr`'s operations live in
   `ConLeche/Verify/Cached/OpsC.lean` and are the specification this port will
   be proved against (task #13's ruling). */

#[cfg(test)]
mod tests {
    use crate::cached::expr_ops_c;
    use crate::kernel::expr;
    use crate::kernel::expr::{BinderMeta, Expr};
    use crate::kernel::expr_ops;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;
    use crate::ron::hashmap::HashMap;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn never() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    /// **The memo of `instantiate1XP` is hit exactly where con-leche's is.**
    /// The subject is `f s s` with one *shared* `s = (λ _ : A. bvar 1)`
    /// occurring twice, so the second visit to `s` is a hit.  The assertions
    /// are on the table, not just the answer, and they are the statement of
    /// module note 2's discipline: the only node recorded is `s`, the one node
    /// the walk can meet twice.  The two `.app` nodes are compound and above
    /// the cutoff, but each has exactly one reference — the outer one is held
    /// by `e` alone and the inner one by the outer one alone — so
    /// `ron::node::is_exclusive` reports them unshared and they cost no entry;
    /// `A`, `f` and the `.bvar`s are atoms or below the cutoff.  Both
    /// occurrences of `s` still come back as the same value.
    #[test]
    fn instantiate1_memoises_shared_compound_nodes_only() {
        // s = λ (_ : A). bvar 1   — its body is loose at 1, so bvarB s = 1
        let a = expr::mk_const(nm("A"), Vec::new());
        let s = expr::lam(expr::dup(&a), expr::bvar(1), never());
        assert_eq!(expr_ops::bvar_b(&s), 1);
        // e = (f s) s, with `f` a closed constant: bvarB e = 1 too
        let f = expr::mk_const(nm("f"), Vec::new());
        let e = expr::app(expr::app(f, expr::dup(&s)), expr::dup(&s));
        assert_eq!(expr_ops::bvar_b(&e), 1);

        let v = expr::mk_const(nm("v"), Vec::new());
        let mut memo: expr_ops_c::MemoN = HashMap::new();
        let r = expr_ops_c::instantiate1_go(&v, &mut memo, &e, 0);

        // ONE entry: `s`, which the local binding and the two occurrences in
        // `e` share.  The two `.app`s are exclusive and are rebuilt with the
        // table untouched; `A`, `f` and the `.bvar`s are atoms or below the
        // cutoff and were never candidates.
        assert_eq!(memo.len(), 1);
        // the result: both occurrences of `s` became `λ (_ : A). v`
        let s2 = expr::lam(expr::dup(&a), expr::dup(&v), never());
        let want = expr::app(
            expr::app(expr::mk_const(nm("f"), Vec::new()), expr::dup(&s2)),
            expr::dup(&s2),
        );
        assert!(expr::beq(&r, &want));

        // A second call on a *fresh* table writes the same one entry — the
        // count is a property of the term, not of the history — and a second
        // call on the *same* table writes nothing more and answers the same
        // term (the hit).
        let mut memo2: expr_ops_c::MemoN = HashMap::new();
        let _ = expr_ops_c::instantiate1_go(&v, &mut memo2, &e, 0);
        assert_eq!(memo2.len(), 1);
        let r2 = expr_ops_c::instantiate1_go(&v, &mut memo, &e, 0);
        assert_eq!(memo.len(), 1);
        assert!(expr::beq(&r2, &want));

        // And the discipline is about SHARING, not about the shape: hold a
        // second reference to the inner `.app` and it is recorded too, while
        // the walk's answer does not move.
        let inner = expr::app(expr::mk_const(nm("f"), Vec::new()), expr::dup(&s));
        let e2 = expr::app(expr::dup(&inner), expr::dup(&s));
        let mut memo3: expr_ops_c::MemoN = HashMap::new();
        let r3 = expr_ops_c::instantiate1_go(&v, &mut memo3, &e2, 0);
        assert_eq!(memo3.len(), 2, "`s` and the inner `.app`, which `inner` holds");
        assert!(expr::beq(&r3, &want));

        // The cutoff: a term closed at the cursor is returned *itself*, with
        // no table at all — `instantiate1`'s `bvarB ≤ d` guard.
        let closed = expr::mk_const(nm("c"), Vec::new());
        let same = expr_ops_c::instantiate1(&closed, &v, 0);
        assert!(expr::ptr_eq(&same, &closed) || expr::beq(&same, &closed));
    }

    /// The wrappers agree with `expr_ops`' structural specifications on a
    /// term with a shared sub-DAG — which is what
    /// `ConLeche/Verify/Cached/OpsC.lean` proves in general — and the
    /// `O(1)` scope reads agree with the walks.
    #[test]
    fn the_cached_walks_agree_with_the_specifications() {
        let a = expr::mk_const(nm("A"), Vec::new());
        let v = expr::mk_const(nm("v"), Vec::new());
        let shared = expr::lam(expr::dup(&a), expr::bvar(1), never());
        let e = expr::app(
            expr::app(expr::mk_const(nm("f"), Vec::new()), expr::dup(&shared)),
            expr::dup(&shared),
        );

        // instantiate1 / instantiateList / instantiate1Lift
        assert!(expr::beq(
            &expr_ops_c::instantiate1(&e, &v, 0),
            &expr_ops::instantiate1(&e, &v, 0)
        ));
        let mut vs: Vec<Expr> = Vec::new();
        vs.push(expr::dup(&v));
        assert!(expr::beq(
            &expr_ops_c::instantiate_list(&e, &vs, 0),
            &expr_ops::instantiate_list_fast(&e, &vs, 0)
        ));
        assert!(expr::beq(
            &expr_ops_c::instantiate1_lift(&e, &v, 0),
            &expr_ops::instantiate1_lift(&e, &v, 0)
        ));
        // instantiateRev on a one-element array is instantiateList
        assert!(expr::beq(
            &expr_ops_c::instantiate_rev(&e, &vs, 0),
            &expr_ops_c::instantiate_list(&e, &vs, 0)
        ));

        // abstraction: open at `fvar 0`, close it again
        let opened = expr_ops_c::instantiate1(&e, &expr::fvar(0, expr::dup(&a)), 0);
        assert!(expr_ops_c::has_fvar(&opened));
        let closed = expr_ops_c::abstract1(&opened, 0, 0);
        assert!(expr::beq(&closed, &expr_ops::abstract1(&opened, 0, 0)));
        assert!(!expr_ops_c::has_fvar(&closed));
        assert!(expr::beq(
            &expr_ops_c::abstract_range(&opened, 0, 1, 0),
            &expr_ops::abstract_range(&opened, 0, 1, 0)
        ));
        // `k = 0` is the identity and skips the traversal
        assert!(expr::beq(&expr_ops_c::abstract_range(&opened, 0, 0, 0), &opened));

        // the scope reads and their walks
        assert_eq!(
            expr_ops_c::loose_bvars_bounded(0, &e),
            expr_ops::loose_bvars_bounded(0, &e)
        );
        assert!(expr_ops_c::loose_bvars_bounded(1, &e));
        assert!(!expr_ops_c::loose_bvars_bounded(0, &e));
        assert_eq!(expr_ops_c::wscoped_b(1, &opened), expr_ops::wscoped_b(1, &opened));
        assert!(expr_ops_c::wscoped_b(1, &opened));
        assert!(!expr_ops_c::wscoped_b(0, &opened));
        // `leafGuard`: a fabrication over the subject's own leaves passes, one
        // over a foreign leaf does not, and an `fvar`-free one is `O(1)` true
        assert_eq!(expr_ops_c::fvar_leaves(&opened).len(), 1);
        assert!(expr_ops_c::leaf_guard(&opened, &opened));
        assert!(expr_ops_c::leaf_guard(&e, &opened));
        let foreign = expr::fvar(3, expr::dup(&a));
        assert!(!expr_ops_c::leaf_guard(&foreign, &opened));

        // spines and telescopes
        let spine = expr_ops_c::mk_app_n(expr::mk_const(nm("g"), Vec::new()), &vs);
        assert!(expr::beq(
            &expr_ops_c::get_app_fn(&spine),
            &expr::mk_const(nm("g"), Vec::new())
        ));
        assert_eq!(expr_ops_c::get_app_args(&spine).len(), 1);
        assert!(expr::beq(
            &expr_ops_c::inst_spine(&vs, 0, &e),
            &expr_ops::inst_spine(&vs, 0, &e)
        ));
        // piResidual: `∀ (_ : A), bvar 0` at one argument is that argument
        let pi = expr::forall_e(expr::dup(&a), expr::bvar(0), never());
        match expr_ops_c::pi_residual(&pi, &vs) {
            Some(r) => assert!(expr::beq(&r, &v)),
            None => panic!("the residual of a one-binder telescope at one argument"),
        }
        // and a non-telescope declines
        match expr_ops_c::pi_residual(&a, &vs) {
            Some(_) => panic!("a constant is not a telescope"),
            None => (),
        }

        // level instantiation, and the `hasLP` cutoff
        let mut ks: Vec<Name> = Vec::new();
        ks.push(nm("u"));
        let mut us: Vec<level::Level> = Vec::new();
        us.push(level::zero());
        let lp = expr::forall_e(
            expr::sort(level::param(nm("u"))),
            expr::bvar(0),
            expr::binder_meta(prop_when::never()),
        );
        assert!(expr::has_lp(&lp));
        assert!(expr::beq(
            &expr_ops_c::inst_level_params(&ks, &us, &lp),
            &expr_ops::instantiate_level_params(&ks, &us, &lp)
        ));
        assert!(expr::beq(&expr_ops_c::inst_level_params(&ks, &us, &e), &e));
        // and the definedness guard
        assert_eq!(
            expr_ops_c::all_level_params_defined(&ks, &lp),
            expr_ops::all_level_params_defined_fast(&ks, &lp)
        );
        assert!(expr_ops_c::all_level_params_defined(&ks, &lp));
        assert!(!expr_ops_c::all_level_params_defined(&Vec::new(), &lp));
    }
}
