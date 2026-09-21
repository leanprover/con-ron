//! Port of `ConLeche/Kernel/ExprOps.lean` — the term operations.
//!
//! Everything the checker does *to* a term that is not building or comparing
//! one (`crate::kernel::expr`): opening and closing binders (`instantiate1`,
//! `instantiateList`, `abstract1`, `abstractRange`), shifting loose bound
//! variables (`liftLooseBVars`, `lowerBVars`, `instantiate1Lift`), reading
//! spines and telescopes (`getAppFn`, `getAppArgs`, `stripPis`, `instPisAt`
//! and friends), and the *exact* derived-field accessors `bvarB`/`fvarB`
//! with the memoized walks behind their saturated branch.
//!
//! **The `@[csimp]` families.**  con-leche writes each of these walks twice:
//! a plain structural `def` (the specification every proof consumes) and a
//! memoized `*Go`/`*Fast` pair that a `@[csimp]` lemma substitutes for it in
//! compiled code.  The port implements the **`*Fast`** member — that is what
//! con-leche executes — and cites the logical definition, the `*Go` walk, the
//! `*Fast` wrapper and the `@[csimp]` lemma together; the lemma *is* the
//! transparency argument for the deviation, since it is a kernel-checked
//! equation between the two, so the port's single function refines the
//! logical definition by that equation.  Nine families are folded this way
//! (`instantiate1`, `instantiateList`, `liftLooseBVars`, `resetMeta`,
//! `abstract1`, `lowerBVars`, `instantiate1Lift`, `renameConsts` and
//! `instantiateLevelParams`), plus `hasFvar` and `looseBVarsBounded`, whose
//! `*Fast` members are not walks at all but `O(1)` reads of the packed word.
//!
//! **Memos.**  Every memo in this file is *local*: con-leche creates it
//! empty (`{}`) inside the `*Fast` wrapper and drops it when the call
//! returns, because the answer also depends on the parameters that are not
//! in the key (`v`, `vs`, `amount`, `d`, `f`, `ks`/`us`).  The port does the
//! same — a `crate::ron::hashmap::HashMap` local to the wrapper, handed to the
//! walk as a `&mut` parameter.  `&mut` rather than Lean's threaded
//! `(result, memo)` pair because Aeneas's back-end translates a `&mut`
//! parameter into exactly that threaded pair, so the generated Lean carries
//! the cited signature; DESIGN.md §3.4 reserves `&mut` for the state
//! parameter, and the memo is precisely this walk's state.  (The memo tables
//! that live in `CState` are `ConLeche/Cached/*`'s business, not this
//! file's; none of them appears here.)
//!
//! Conventions, as in `expr.rs`: terms come in by shared reference and go
//! out owned, with an explicit `dup` (a `P` bump) wherever Lean returns a
//! subterm or an unchanged node; Lean's `List` is a `Vec` walked by an index
//! helper (`*_from`, DESIGN.md §3.4); the `Nat` indices and cutoffs are
//! `u64` (§3.3), with `sub_nat` for the truncated subtractions Lean's `Nat`
//! performs and Rust's `u64` would fail on.  Higher-order arguments are
//! one-method traits (`NameToName` here), the pattern task #9 fixed.
//!
//! Order follows the Lean file; where a `@[csimp]` family's members are far
//! apart the single Rust item sits at the *logical* definition's position,
//! which is why `abstract1`, `lower_bvars` and `instantiate1_lift` use
//! `fvar_b`/`bvar_b` before this file defines them.

use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Expr;
use crate::kernel::expr::ExprView;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::HashMap;
use crate::ron::hashmap::Hashable;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;

// ---------------------------------------------------------------------------
// Small helpers with no Lean counterpart
// ---------------------------------------------------------------------------

/// con-leche: none — Lean's `Nat` subtraction, which truncates at zero
/// `a - b` as Lean's `Nat` computes it.  Rust's `-` on `u64` underflows (a
/// `fail` in the Aeneas model), so every place the cited Lean subtracts
/// without a guard that keeps the result non-negative goes through this:
/// `bvarBound`'s `body.bvarBound - 1`, `instSpine`'s `t - 1` and
/// `recRulePlain`'s `mI - 1 - k`.  Where the Lean arm *does* carry the guard
/// (`instantiate1`'s `i > d` before `.bvar (i - 1)`, `lowerBVars`'s
/// `i ≥ c + amount` before `.bvar (i - amount)`) the port subtracts
/// directly, as the cited code does.
pub fn sub_nat(a: u64, b: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        0
    }
}

/// con-leche: none — the memo key of `Std.HashMap (Expr × Nat) Expr`
/// The `(node, cursor)` key five of this file's memos use.  Lean's `Prod`
/// carries derived `BEq`/`Hashable` instances; here they are the two
/// dictionaries below (task #7's `Eq2`/`Hashable`, not `core::cmp`).
pub struct ExprNatKey {
    pub e: Expr,
    pub d: u64,
}

/// con-leche: none — the memo key of `Std.HashMap (Expr × Nat) Expr`
/// Build a key, taking the node by a `P` bump.
pub fn expr_nat_key(e: &Expr, d: u64) -> ExprNatKey {
    ExprNatKey { e: expr::dup(e), d: d }
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
/// The derived `Hashable (Expr × Nat)`.  Hash values are verdict-neutral
/// (DESIGN.md §3.2), so the crate's own `Expr` hash is what goes in.
impl Hashable for ExprNatKey {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(expr::hash(&self.e), name::nat_hash(self.d))
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
/// The derived `BEq (Expr × Nat)`: the node by `Expr.beq` (pointer test,
/// packed word, descent), then the cursor.
impl Eq2 for ExprNatKey {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &Self) -> bool {
        if expr::beq(&self.e, &other.e) {
            self.d == other.d
        } else {
            false
        }
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `(Expr × Nat)` key
/// A memo probe that owns its answer, so the map's borrow ends with the
/// lookup: the `none` branch of every cited `match memo[k]? with` needs the
/// map mutably again.
pub fn memo1_get(memo: &HashMap<ExprNatKey, Expr>, k: &ExprNatKey) -> Option<Expr> {
    match memo.get(k) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `Expr` key
/// The `Expr`-keyed twin of `memo1_get`.
pub fn memo_e_get(memo: &HashMap<Expr, Expr>, k: &Expr) -> Option<Expr> {
    match memo.get(k) {
        Some(r) => Some(expr::dup(r)),
        None => None,
    }
}

/// con-leche: none — `Std.HashMap.getElem?` at an `Expr` key, `Nat` values
/// The `Expr → Nat` twin of `memo1_get`, for the two range walks.
pub fn memo_n_get(memo: &HashMap<Expr, u64>, k: &Expr) -> Option<u64> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: none — `List.take`/`List.append` over a `Vec<Expr>`
/// The first `k` entries of `xs`, appended to `out`.  Lean's lists are
/// shared, a `Vec` has to copy — task #9's deviation 5; the entries
/// themselves stay shared (`expr::dup` is a `P` bump).
pub fn exprs_copy_upto(xs: &Vec<Expr>, k: usize, i: usize, mut out: Vec<Expr>) -> Vec<Expr> {
    if i >= k || i >= xs.len() {
        out
    } else {
        out.push(expr::dup(&xs[i]));
        exprs_copy_upto(xs, k, i + 1, out)
    }
}

/// con-leche: none — `List.take` over a `Vec<Expr>`
/// `xs.take k`, the entry point of the index recursion above.
pub fn take_exprs(xs: &Vec<Expr>, k: usize) -> Vec<Expr> {
    exprs_copy_upto(xs, k, 0, Vec::with_capacity(k))
}

/// con-leche: none — the `a :: acc` of `instPisAtFGo`/`instLamsAtFGo`
/// Lean's cons.  A `Vec` has no cheap cons, so the accumulator is rebuilt
/// (task #9's deviation 5): `O(|acc|)` pointer copies per binder instead of
/// `O(1)`, which keeps the `*F` walks' point — one *tree* traversal per
/// domain instead of one per argument — while the list itself stays tiny
/// (one entry per telescope binder).
pub fn cons_expr(a: &Expr, acc: &Vec<Expr>) -> Vec<Expr> {
    let mut out: Vec<Expr> = Vec::with_capacity(acc.len() + 1);
    out.push(expr::dup(a));
    exprs_copy_upto(acc, acc.len(), 0, out)
}

/// con-leche: none — the `us` a rebuilt `.const` node carries over unchanged
/// The index recursion behind `levels_copy`.
pub fn levels_copy_from(us: &Vec<Level>, i: usize, mut out: Vec<Level>) -> Vec<Level> {
    if i >= us.len() {
        out
    } else {
        out.push(level::dup(&us[i]));
        levels_copy_from(us, i + 1, out)
    }
}

/// con-leche: none — the `us` a rebuilt `.const` node carries over unchanged
/// A `Vec<Level>` copy; Lean's lists are shared values (DESIGN.md §3.3).
pub fn levels_copy(us: &Vec<Level>) -> Vec<Level> {
    levels_copy_from(us, 0, Vec::with_capacity(us.len()))
}

// ---------------------------------------------------------------------------
// `instantiate1` (`ExprOps.lean:29-189`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:80-116 instantiate1Go
/// con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
/// The memoized walk behind `instantiate1`: replace `bvar d` by `v`,
/// lowering the loose `bvar`s above `d` by one.  The five leaf constructors
/// skip the memo, as in the cited code; the rebuilding ones probe it at
/// `(node, cursor)` and write the answer back.
///
/// Deviation: the memo is a `&mut` parameter rather than Lean's threaded
/// `(Expr, Std.HashMap …)` pair — Aeneas's back-end turns the one into the
/// other (module doc).  The identity arms (`.fvar idx ty`, `.sort u`, …)
/// rebuild a node in Lean and return a `P` bump here: the same value,
/// because `expr.rs`'s smart constructors are functions.
pub fn instantiate1_go(v: &Expr, memo: &mut HashMap<ExprNatKey, Expr>, e: &Expr, d: u64) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(i) => {
            if *i == d {
                expr::dup(v)
            } else if *i > d {
                expr::bvar(*i - 1)
            } else {
                expr::bvar(*i)
            }
        }
        ExprView::Fvar(_, _) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        _ => {
            let k: ExprNatKey = expr_nat_key(e, d);
            match memo1_get(memo, &k) {
                Some(r) => r,
                None => {
                    let r: Expr = match expr::view(&e) {
                        ExprView::App(f, a) => {
                            let f2: Expr = instantiate1_go(v, memo, f, d);
                            let a2: Expr = instantiate1_go(v, memo, a, d);
                            expr::app(f2, a2)
                        }
                        ExprView::Lam(ty, body, bi) => {
                            let t: Expr = instantiate1_go(v, memo, ty, d);
                            let b: Expr = instantiate1_go(v, memo, body, d + 1);
                            expr::lam(t, b, expr::binder_meta_dup(bi))
                        }
                        ExprView::ForallE(ty, body, bi) => {
                            let t: Expr = instantiate1_go(v, memo, ty, d);
                            let b: Expr = instantiate1_go(v, memo, body, d + 1);
                            expr::forall_e(t, b, expr::binder_meta_dup(bi))
                        }
                        ExprView::LetE(ty, val, body) => {
                            let t: Expr = instantiate1_go(v, memo, ty, d);
                            let w: Expr = instantiate1_go(v, memo, val, d);
                            let b: Expr = instantiate1_go(v, memo, body, d + 1);
                            expr::let_e(t, w, b)
                        }
                        ExprView::Proj(s, i, sub) => {
                            let u: Expr = instantiate1_go(v, memo, sub, d);
                            expr::proj(name::dup(s), *i, u)
                        }
                        _ => expr::dup(e),
                    };
                    memo.insert(k, expr::dup(&r));
                    r
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:182-184 instantiate1Fast
/// con-leche: ConLeche/Kernel/ExprOps.lean:29-45 instantiate1
/// con-leche: ConLeche/Kernel/ExprOps.lean:186-189 instantiate1_eq_instantiate1Fast
/// Open a binder body: replace `bvar d` by `v` (which must be
/// `bvar`-closed), lowering the loose `bvar`s above `d`.  This is the
/// *executed* `instantiate1` — the cited `@[csimp]` lemma is the equation
/// that makes the memoized walk the logical definition, and therefore the
/// transparency argument for porting the fast member (module doc).
pub fn instantiate1(e: &Expr, v: &Expr, d: u64) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    instantiate1_go(v, &mut memo, e, d)
}

// ---------------------------------------------------------------------------
// `instantiateList` (`ExprOps.lean:191-378`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList
/// Bulk instantiation: `vs[0]` replaces `bvar d`, `vs[i]` replaces
/// `bvar (d + i)`, loose `bvar`s above the range drop by `vs.length`.
///
/// The pure walk, kept because the memoized one below *calls* it on `.bvar`
/// nodes: the `bvar` arm recurses into the replacement with the
/// earlier-listed entries (`vs.take (j - d)`), which is the identity at
/// every checker call site but is what makes the function the fold of
/// `instantiate1`.  Deviation: `vs.take` copies a `Vec` (the entries stay
/// shared).
pub fn instantiate_list(e: &Expr, vs: &Vec<Expr>, d: u64) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(j) => {
            if *j < d {
                expr::bvar(*j)
            } else {
                let n: u64 = vs.len() as u64;
                if *j - d < n {
                    let i: usize = (*j - d) as usize;
                    let pre: Vec<Expr> = take_exprs(vs, i);
                    instantiate_list(&vs[i], &pre, d)
                } else {
                    expr::bvar(*j - n)
                }
            }
        }
        ExprView::Fvar(_, _) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        ExprView::App(f, a) => {
            let f2: Expr = instantiate_list(f, vs, d);
            let a2: Expr = instantiate_list(a, vs, d);
            expr::app(f2, a2)
        }
        ExprView::Lam(ty, body, bi) => {
            let t: Expr = instantiate_list(ty, vs, d);
            let b: Expr = instantiate_list(body, vs, d + 1);
            expr::lam(t, b, expr::binder_meta_dup(bi))
        }
        ExprView::ForallE(ty, body, bi) => {
            let t: Expr = instantiate_list(ty, vs, d);
            let b: Expr = instantiate_list(body, vs, d + 1);
            expr::forall_e(t, b, expr::binder_meta_dup(bi))
        }
        ExprView::LetE(ty, val, body) => {
            let t: Expr = instantiate_list(ty, vs, d);
            let w: Expr = instantiate_list(val, vs, d);
            let b: Expr = instantiate_list(body, vs, d + 1);
            expr::let_e(t, w, b)
        }
        ExprView::Proj(s, i, sub) => {
            let u: Expr = instantiate_list(sub, vs, d);
            expr::proj(name::dup(s), *i, u)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:267-303 instantiateListGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:191-235 instantiateList
/// The memoized walk behind `instantiateList`; the `.bvar` arm defers to the
/// pure function above, exactly as the cited code does.
pub fn instantiate_list_go(
    vs: &Vec<Expr>,
    memo: &mut HashMap<ExprNatKey, Expr>,
    e: &Expr,
    d: u64,
) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(_) => instantiate_list(e, vs, d),
        ExprView::Fvar(_, _) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        _ => {
            let k: ExprNatKey = expr_nat_key(e, d);
            match memo1_get(memo, &k) {
                Some(r) => r,
                None => {
                    let r: Expr = match expr::view(&e) {
                        ExprView::App(f, a) => {
                            let f2: Expr = instantiate_list_go(vs, memo, f, d);
                            let a2: Expr = instantiate_list_go(vs, memo, a, d);
                            expr::app(f2, a2)
                        }
                        ExprView::Lam(ty, body, bi) => {
                            let t: Expr = instantiate_list_go(vs, memo, ty, d);
                            let b: Expr = instantiate_list_go(vs, memo, body, d + 1);
                            expr::lam(t, b, expr::binder_meta_dup(bi))
                        }
                        ExprView::ForallE(ty, body, bi) => {
                            let t: Expr = instantiate_list_go(vs, memo, ty, d);
                            let b: Expr = instantiate_list_go(vs, memo, body, d + 1);
                            expr::forall_e(t, b, expr::binder_meta_dup(bi))
                        }
                        ExprView::LetE(ty, val, body) => {
                            let t: Expr = instantiate_list_go(vs, memo, ty, d);
                            let w: Expr = instantiate_list_go(vs, memo, val, d);
                            let b: Expr = instantiate_list_go(vs, memo, body, d + 1);
                            expr::let_e(t, w, b)
                        }
                        ExprView::Proj(s, i, sub) => {
                            let u: Expr = instantiate_list_go(vs, memo, sub, d);
                            expr::proj(name::dup(s), *i, u)
                        }
                        _ => expr::dup(e),
                    };
                    memo.insert(k, expr::dup(&r));
                    r
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:371-373 instantiateListFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:375-378 instantiateList_eq_instantiateListFast
/// The executed `instantiateList` (one memoized DAG walk).
pub fn instantiate_list_fast(e: &Expr, vs: &Vec<Expr>, d: u64) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    instantiate_list_go(vs, &mut memo, e, d)
}

// ---------------------------------------------------------------------------
// `liftLooseBVars` (`ExprOps.lean:380-539`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:430-466 liftLooseBVarsGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
/// The memoized walk behind `liftLooseBVars`: bump every loose bound
/// variable `≥ cutoff` by `amount`.
pub fn lift_loose_bvars_go(
    amount: u64,
    memo: &mut HashMap<ExprNatKey, Expr>,
    e: &Expr,
    c: u64,
) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(i) => {
            if *i >= c {
                expr::bvar(*i + amount)
            } else {
                expr::bvar(*i)
            }
        }
        ExprView::Fvar(_, _) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        _ => {
            let k: ExprNatKey = expr_nat_key(e, c);
            match memo1_get(memo, &k) {
                Some(r) => r,
                None => {
                    let r: Expr = match expr::view(&e) {
                        ExprView::App(a, b) => {
                            let a2: Expr = lift_loose_bvars_go(amount, memo, a, c);
                            let b2: Expr = lift_loose_bvars_go(amount, memo, b, c);
                            expr::app(a2, b2)
                        }
                        ExprView::Lam(ty, body, m) => {
                            let t: Expr = lift_loose_bvars_go(amount, memo, ty, c);
                            let b: Expr = lift_loose_bvars_go(amount, memo, body, c + 1);
                            expr::lam(t, b, expr::binder_meta_dup(m))
                        }
                        ExprView::ForallE(ty, body, m) => {
                            let t: Expr = lift_loose_bvars_go(amount, memo, ty, c);
                            let b: Expr = lift_loose_bvars_go(amount, memo, body, c + 1);
                            expr::forall_e(t, b, expr::binder_meta_dup(m))
                        }
                        ExprView::LetE(ty, v, body) => {
                            let t: Expr = lift_loose_bvars_go(amount, memo, ty, c);
                            let w: Expr = lift_loose_bvars_go(amount, memo, v, c);
                            let b: Expr = lift_loose_bvars_go(amount, memo, body, c + 1);
                            expr::let_e(t, w, b)
                        }
                        ExprView::Proj(s, i, sub) => {
                            let u: Expr = lift_loose_bvars_go(amount, memo, sub, c);
                            expr::proj(name::dup(s), *i, u)
                        }
                        _ => expr::dup(e),
                    };
                    memo.insert(k, expr::dup(&r));
                    r
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:532-534 liftLooseBVarsFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:380-400 liftLooseBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:536-539 liftLooseBVars_eq_liftLooseBVarsFast
/// The executed `liftLooseBVars`.
pub fn lift_loose_bvars(amount: u64, c: u64, e: &Expr) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    lift_loose_bvars_go(amount, &mut memo, e, c)
}

// ---------------------------------------------------------------------------
// `resetMeta` (`ExprOps.lean:552-692`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:579-615 resetMetaGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
/// The memoized walk behind `resetMeta`: every binder's prop-ness datum back
/// to the parse placeholder `.never`.  Unlike the substitution walks this
/// one *does* descend into `fvar` type annotations.
pub fn reset_meta_go(memo: &mut HashMap<Expr, Expr>, e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(_) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        _ => match memo_e_get(memo, e) {
            Some(r) => r,
            None => {
                let r: Expr = match expr::view(&e) {
                    ExprView::Fvar(i, ty) => {
                        let t: Expr = reset_meta_go(memo, ty);
                        expr::fvar(*i, t)
                    }
                    ExprView::App(f, a) => {
                        let f2: Expr = reset_meta_go(memo, f);
                        let a2: Expr = reset_meta_go(memo, a);
                        expr::app(f2, a2)
                    }
                    ExprView::Lam(ty, body, _) => {
                        let t: Expr = reset_meta_go(memo, ty);
                        let b: Expr = reset_meta_go(memo, body);
                        expr::lam(t, b, expr::binder_meta(prop_when::never()))
                    }
                    ExprView::ForallE(ty, body, _) => {
                        let t: Expr = reset_meta_go(memo, ty);
                        let b: Expr = reset_meta_go(memo, body);
                        expr::forall_e(t, b, expr::binder_meta(prop_when::never()))
                    }
                    ExprView::LetE(ty, val, body) => {
                        let t: Expr = reset_meta_go(memo, ty);
                        let w: Expr = reset_meta_go(memo, val);
                        let b: Expr = reset_meta_go(memo, body);
                        expr::let_e(t, w, b)
                    }
                    ExprView::Proj(s, i, sub) => {
                        let u: Expr = reset_meta_go(memo, sub);
                        expr::proj(name::dup(s), *i, u)
                    }
                    _ => expr::dup(e),
                };
                memo.insert(expr::dup(e), expr::dup(&r));
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:687-688 resetMetaFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:552-559 resetMeta
/// con-leche: ConLeche/Kernel/ExprOps.lean:690-692 resetMeta_eq_resetMetaFast
/// The executed `resetMeta`.
pub fn reset_meta(e: &Expr) -> Expr {
    let mut memo: HashMap<Expr, Expr> = HashMap::new();
    reset_meta_go(&mut memo, e)
}

// ---------------------------------------------------------------------------
// `lowerBVars` (`ExprOps.lean:694-716`, memoized at `:2012-2151`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:2014-2051 lowerBVarsGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
/// The memoized walk behind `lowerBVars`: lower every loose bound variable
/// `≥ cutoff + amount` by `amount`, leaving the window
/// `[cutoff, cutoff + amount)` alone.  The `bvarB` cutoff at the top is the
/// cited field read: a node whose loose-bvar bound is small enough cannot
/// contain a variable the walk would move.
pub fn lower_bvars_go(
    amount: u64,
    memo: &mut HashMap<ExprNatKey, Expr>,
    e: &Expr,
    c: u64,
) -> Expr {
    if bvar_b(e) <= c + amount {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i >= c + amount {
                    expr::bvar(*i - amount)
                } else {
                    expr::bvar(*i)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let k: ExprNatKey = expr_nat_key(e, c);
                match memo1_get(memo, &k) {
                    Some(r) => r,
                    None => {
                        let r: Expr = match expr::view(&e) {
                            ExprView::App(f, a) => {
                                let f2: Expr = lower_bvars_go(amount, memo, f, c);
                                let a2: Expr = lower_bvars_go(amount, memo, a, c);
                                expr::app(f2, a2)
                            }
                            ExprView::Lam(ty, body, m) => {
                                let t: Expr = lower_bvars_go(amount, memo, ty, c);
                                let b: Expr = lower_bvars_go(amount, memo, body, c + 1);
                                expr::lam(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::ForallE(ty, body, m) => {
                                let t: Expr = lower_bvars_go(amount, memo, ty, c);
                                let b: Expr = lower_bvars_go(amount, memo, body, c + 1);
                                expr::forall_e(t, b, expr::binder_meta_dup(m))
                            }
                            ExprView::LetE(ty, val, body) => {
                                let t: Expr = lower_bvars_go(amount, memo, ty, c);
                                let w: Expr = lower_bvars_go(amount, memo, val, c);
                                let b: Expr = lower_bvars_go(amount, memo, body, c + 1);
                                expr::let_e(t, w, b)
                            }
                            ExprView::Proj(s, i, sub) => {
                                let u: Expr = lower_bvars_go(amount, memo, sub, c);
                                expr::proj(name::dup(s), *i, u)
                            }
                            _ => expr::dup(e),
                        };
                        memo.insert(k, expr::dup(&r));
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2146-2148 lowerBVarsFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:694-716 lowerBVars
/// con-leche: ConLeche/Kernel/ExprOps.lean:2150-2153 lowerBVars_eq_lowerBVarsFast
/// The executed `lowerBVars`.
pub fn lower_bvars(amount: u64, c: u64, e: &Expr) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    lower_bvars_go(amount, &mut memo, e, c)
}

// ---------------------------------------------------------------------------
// `instantiate1Lift` (`ExprOps.lean:718-739`, memoized at `:2222-2363`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:2224-2263 instantiate1LiftGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
/// The memoized walk behind `instantiate1Lift`: the general
/// capture-avoiding substitution, which lifts `v`'s own loose `bvar`s past
/// the binders crossed on the way (`instantiate1` may not, and requires a
/// `bvar`-closed `v`).
pub fn instantiate1_lift_go(
    v: &Expr,
    memo: &mut HashMap<ExprNatKey, Expr>,
    e: &Expr,
    d: u64,
) -> Expr {
    if bvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => {
                if *i == d {
                    lift_loose_bvars(d, 0, v)
                } else if *i > d {
                    expr::bvar(*i - 1)
                } else {
                    expr::bvar(*i)
                }
            }
            ExprView::Fvar(_, _) => expr::dup(e),
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let k: ExprNatKey = expr_nat_key(e, d);
                match memo1_get(memo, &k) {
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
                            ExprView::Proj(s, i, sub) => {
                                let u: Expr = instantiate1_lift_go(v, memo, sub, d);
                                expr::proj(name::dup(s), *i, u)
                            }
                            _ => expr::dup(e),
                        };
                        memo.insert(k, expr::dup(&r));
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2358-2360 instantiate1LiftFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:718-739 instantiate1Lift
/// con-leche: ConLeche/Kernel/ExprOps.lean:2362-2365 instantiate1Lift_eq_instantiate1LiftFast
/// The executed `instantiate1Lift`.
pub fn instantiate1_lift(e: &Expr, v: &Expr, d: u64) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    instantiate1_lift_go(v, &mut memo, e, d)
}

// ---------------------------------------------------------------------------
// Sizes, abstraction, scope predicates (`ExprOps.lean:741-913`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:741-748 sizeB
/// Node count with `fvar` a leaf (its annotation ignored): con-leche's
/// termination measure for recursion into instantiated binder bodies.
/// Nothing in the port recurses on it — Aeneas's `partial_fixpoint` carries
/// no measure — but it is executable, and keeping it in step with its source
/// is what the provenance gate is for.
pub fn size_b(e: &Expr) -> u64 {
    match expr::view(&e) {
        ExprView::Bvar(_) => 1,
        ExprView::Fvar(_, _) => 1,
        ExprView::Sort(_) => 1,
        ExprView::Const(_, _) => 1,
        ExprView::Lit(_) => 1,
        ExprView::App(f, a) => size_b(f) + size_b(a) + 1,
        ExprView::Lam(ty, body, _) => size_b(ty) + size_b(body) + 1,
        ExprView::ForallE(ty, body, _) => size_b(ty) + size_b(body) + 1,
        ExprView::LetE(ty, val, body) => size_b(ty) + size_b(val) + size_b(body) + 1,
        ExprView::Proj(_, _, sub) => size_b(sub) + 1,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1791-1835 abstract1Go
/// con-leche: ConLeche/Kernel/ExprOps.lean:760-776 abstract1
/// The memoized walk behind `abstract1`: close a binder body by replacing
/// the `fvar d` leaves with `bvar k`, bumping `k` under binders.  The
/// `fvarB ≤ d` cutoff at the top is the cited `fvarB` field read — a node
/// whose fvar range is below `d` cannot contain `fvar d` — and the memo
/// covers the case the cutoff cannot, a shared tower built *over* the
/// variable being abstracted.
pub fn abstract1_go(d: u64, memo: &mut HashMap<ExprNatKey, Expr>, e: &Expr, k: u64) -> Expr {
    if fvar_b(e) <= d {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => expr::bvar(*i),
            ExprView::Fvar(idx, _) => {
                if *idx == d {
                    expr::bvar(k)
                } else {
                    expr::dup(e)
                }
            }
            ExprView::Sort(_) => expr::dup(e),
            ExprView::Const(_, _) => expr::dup(e),
            ExprView::Lit(_) => expr::dup(e),
            _ => {
                let key: ExprNatKey = expr_nat_key(e, k);
                match memo1_get(memo, &key) {
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
                            ExprView::Proj(s, i, sub) => {
                                let u: Expr = abstract1_go(d, memo, sub, k);
                                expr::proj(name::dup(s), *i, u)
                            }
                            _ => expr::dup(e),
                        };
                        memo.insert(key, expr::dup(&r));
                        r
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1929-1931 abstract1Fast
/// con-leche: ConLeche/Kernel/ExprOps.lean:760-776 abstract1
/// con-leche: ConLeche/Kernel/ExprOps.lean:1933-1936 abstract1_eq_abstract1Fast
/// The executed `abstract1`: the inverse of `instantiate1` at a fresh
/// variable.
pub fn abstract1(e: &Expr, d: u64, k: u64) -> Expr {
    let mut memo: HashMap<ExprNatKey, Expr> = HashMap::new();
    abstract1_go(d, &mut memo, e, k)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:778-808 abstractRange
/// Bulk abstraction: close `k` binders in one traversal, `fvar (d + i)`
/// becoming the bound variable of the `i`-th binder counted outermost-first.
/// Not memoized in con-leche, and not here.  `fvar` type annotations are not
/// descended into, as in `abstract1`.  Deviation: the cited `d ≤ idx ∧ idx <
/// d + k` becomes an `if` nest (task #3's pattern 9).
pub fn abstract_range(e: &Expr, d: u64, k: u64, c: u64) -> Expr {
    match expr::view(&e) {
        ExprView::Bvar(i) => expr::bvar(*i),
        ExprView::Fvar(idx, _) => {
            if d <= *idx {
                if *idx < d + k {
                    expr::bvar(c + ((d + k - 1) - *idx))
                } else {
                    expr::dup(e)
                }
            } else {
                expr::dup(e)
            }
        }
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Const(_, _) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        ExprView::App(f, a) => {
            let f2: Expr = abstract_range(f, d, k, c);
            let a2: Expr = abstract_range(a, d, k, c);
            expr::app(f2, a2)
        }
        ExprView::Lam(ty, body, m) => {
            let t: Expr = abstract_range(ty, d, k, c);
            let b: Expr = abstract_range(body, d, k, c + 1);
            expr::lam(t, b, expr::binder_meta_dup(m))
        }
        ExprView::ForallE(ty, body, m) => {
            let t: Expr = abstract_range(ty, d, k, c);
            let b: Expr = abstract_range(body, d, k, c + 1);
            expr::forall_e(t, b, expr::binder_meta_dup(m))
        }
        ExprView::LetE(ty, val, body) => {
            let t: Expr = abstract_range(ty, d, k, c);
            let w: Expr = abstract_range(val, d, k, c);
            let b: Expr = abstract_range(body, d, k, c + 1);
            expr::let_e(t, w, b)
        }
        ExprView::Proj(s, i, sub) => {
            let u: Expr = abstract_range(sub, d, k, c);
            expr::proj(name::dup(s), *i, u)
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:810-819 sizeF
/// Full node count, `fvar` type annotations included: con-leche's
/// termination measure for the predicates that recurse into annotations.
pub fn size_f(e: &Expr) -> u64 {
    match expr::view(&e) {
        ExprView::Bvar(_) => 1,
        ExprView::Sort(_) => 1,
        ExprView::Const(_, _) => 1,
        ExprView::Lit(_) => 1,
        ExprView::Fvar(_, ty) => size_f(ty) + 1,
        ExprView::App(f, a) => size_f(f) + size_f(a) + 1,
        ExprView::Lam(ty, body, _) => size_f(ty) + size_f(body) + 1,
        ExprView::ForallE(ty, body, _) => size_f(ty) + size_f(body) + 1,
        ExprView::LetE(ty, val, body) => size_f(ty) + size_f(val) + size_f(body) + 1,
        ExprView::Proj(_, _, sub) => size_f(sub) + 1,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves
/// Every reachable `fvar` leaf, hereditarily through the annotations.  The
/// `out = []` wrapper of the accumulator recursion below.
pub fn fvar_leaves(e: &Expr) -> Vec<(u64, Expr)> {
    fvar_leaves_go(e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:821-833 fvarLeaves
/// The accumulator recursion behind `fvar_leaves`.  Deviation: Lean's `++`
/// allocates a list per node; the accumulator passed by value and returned
/// (task #6's rule) produces the same order in one pass.
pub fn fvar_leaves_go(e: &Expr, mut out: Vec<(u64, Expr)>) -> Vec<(u64, Expr)> {
    match expr::view(&e) {
        ExprView::Fvar(idx, ty) => {
            out.push((*idx, expr::dup(ty)));
            fvar_leaves_go(ty, out)
        }
        ExprView::App(f, a) => {
            let out2: Vec<(u64, Expr)> = fvar_leaves_go(f, out);
            fvar_leaves_go(a, out2)
        }
        ExprView::Lam(ty, b, _) => {
            let out2: Vec<(u64, Expr)> = fvar_leaves_go(ty, out);
            fvar_leaves_go(b, out2)
        }
        ExprView::ForallE(ty, b, _) => {
            let out2: Vec<(u64, Expr)> = fvar_leaves_go(ty, out);
            fvar_leaves_go(b, out2)
        }
        ExprView::LetE(t, v, b) => {
            let out2: Vec<(u64, Expr)> = fvar_leaves_go(t, out);
            let out3: Vec<(u64, Expr)> = fvar_leaves_go(v, out2);
            fvar_leaves_go(b, out3)
        }
        ExprView::Proj(_, _, sub) => fvar_leaves_go(sub, out),
        _ => out,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:835-861 wscopedB
/// Scope check: every reachable `fvar` index is below `d`, hereditarily
/// through the annotations.  Deviation: the cited `&&` chains become `if`
/// nests, which is what Charon produces from them anyway (task #3's
/// pattern 9).
pub fn wscoped_b(d: u64, e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Fvar(idx, ty) => {
            if *idx < d {
                wscoped_b(*idx, ty)
            } else {
                false
            }
        }
        ExprView::App(f, a) => {
            if wscoped_b(d, f) {
                wscoped_b(d, a)
            } else {
                false
            }
        }
        ExprView::Lam(ty, body, _) => {
            if wscoped_b(d, ty) {
                wscoped_b(d, body)
            } else {
                false
            }
        }
        ExprView::ForallE(ty, body, _) => {
            if wscoped_b(d, ty) {
                wscoped_b(d, body)
            } else {
                false
            }
        }
        ExprView::LetE(ty, val, body) => {
            if wscoped_b(d, ty) {
                if wscoped_b(d, val) {
                    wscoped_b(d, body)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprView::Proj(_, _, sub) => wscoped_b(d, sub),
        _ => true,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1718-1719 looseBVarsBoundedFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:863-877 looseBVarsBounded
/// con-leche: ConLeche/Kernel/ExprOps.lean:1721-1731 looseBVarsBounded_eq_looseBVarsBoundedFast
/// Are all bound-variable references bound within the expression (below `k`
/// at the root)?  The executed member is not a walk at all: it is the `O(1)`
/// `bvarB` read, and the cited `@[csimp]` lemma — proved from `bvarB_eq` and
/// `looseBVarsBounded_iff` — is what makes it the logical definition.
pub fn loose_bvars_bounded(k: u64, e: &Expr) -> bool {
    bvar_b(e) <= k
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:879-885 isLam
/// Is the expression a λ?
pub fn is_lam(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Lam(_, _, _) => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:887-894 lamPw
/// A λ node's prop-ness annotation, `none` off λs.
pub fn lam_pw(e: &Expr) -> Option<PropWhen> {
    match expr::view(&e) {
        ExprView::Lam(_, _, m) => Some(prop_when::dup(&m.pw)),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:896-902 forallPw
/// The ∀ twin of `lamPw`.
pub fn forall_pw(e: &Expr) -> Option<PropWhen> {
    match expr::view(&e) {
        ExprView::ForallE(_, _, m) => Some(prop_when::dup(&m.pw)),
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1709-1710 hasFvarFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:904-913 hasFvar
/// con-leche: ConLeche/Kernel/ExprOps.lean:1712-1716 hasFvar_eq_hasFvarFast
/// Does the expression contain a free variable?  As with
/// `looseBVarsBounded`, the executed member is the `O(1)` field read and the
/// cited `@[csimp]` lemma (via `fvarB_eq` and `fvarRange_bne_zero`) is what
/// makes it the walk.
pub fn has_fvar(e: &Expr) -> bool {
    fvar_b(e) != 0
}

// ---------------------------------------------------------------------------
// Spines (`ExprOps.lean:915-928`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:915-918 getAppFn
/// The head of an application spine.
pub fn get_app_fn(e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::App(f, _) => get_app_fn(f),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs
/// The arguments of an application spine, outermost last.  The `out = []`
/// wrapper of the accumulator recursion below.
pub fn get_app_args(e: &Expr) -> Vec<Expr> {
    get_app_args_go(e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:920-923 getAppArgs
/// The accumulator recursion behind `get_app_args`.  Deviation: Lean's
/// `getAppArgs f ++ [a]` allocates a list per spine node; pushing after the
/// recursive call gives the same order in one pass.
pub fn get_app_args_go(e: &Expr, out: Vec<Expr>) -> Vec<Expr> {
    match expr::view(&e) {
        ExprView::App(f, a) => {
            let mut out2: Vec<Expr> = get_app_args_go(f, out);
            out2.push(expr::dup(a));
            out2
        }
        _ => out,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:925-928 mkAppN
/// Apply to a list of arguments.  The `i = 0` wrapper of the index
/// recursion below (DESIGN.md §3.4).
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
// `renameConsts` (`ExprOps.lean:930-1116`)
// ---------------------------------------------------------------------------

/// con-leche: none — replaces the `f : Name → Name` argument of `renameConsts`
/// The one-method trait that stands for a Lean function argument (task #9's
/// pattern 1; DESIGN.md §3.4 forbids closures).  Aeneas renders it as a
/// one-field structure threaded as a dictionary.
pub trait NameToName {
    /// con-leche: none — the `f` of `renameConsts f`
    fn rename(&self, n: &Name) -> Name;
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1001-1038 renameConstsGo
/// con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
/// The memoized walk behind `renameConsts`: rename constants throughout,
/// including inside `fvar` type annotations.  A `.proj` node's structure
/// name is deliberately *not* renamed (the cited comment, task #175 W5);
/// levels and binder data are untouched.
pub fn rename_consts_go<F>(f: &F, memo: &mut HashMap<Expr, Expr>, e: &Expr) -> Expr
where
    F: NameToName,
{
    match expr::view(&e) {
        ExprView::Bvar(_) => expr::dup(e),
        ExprView::Sort(_) => expr::dup(e),
        ExprView::Lit(_) => expr::dup(e),
        ExprView::Const(n, us) => expr::mk_const(f.rename(n), levels_copy(us)),
        _ => match memo_e_get(memo, e) {
            Some(r) => r,
            None => {
                let r: Expr = match expr::view(&e) {
                    ExprView::Fvar(i, ty) => {
                        let t: Expr = rename_consts_go(f, memo, ty);
                        expr::fvar(*i, t)
                    }
                    ExprView::App(a, b) => {
                        let a2: Expr = rename_consts_go(f, memo, a);
                        let b2: Expr = rename_consts_go(f, memo, b);
                        expr::app(a2, b2)
                    }
                    ExprView::Lam(ty, body, m) => {
                        let t: Expr = rename_consts_go(f, memo, ty);
                        let b: Expr = rename_consts_go(f, memo, body);
                        expr::lam(t, b, expr::binder_meta_dup(m))
                    }
                    ExprView::ForallE(ty, body, m) => {
                        let t: Expr = rename_consts_go(f, memo, ty);
                        let b: Expr = rename_consts_go(f, memo, body);
                        expr::forall_e(t, b, expr::binder_meta_dup(m))
                    }
                    ExprView::LetE(ty, v, body) => {
                        let t: Expr = rename_consts_go(f, memo, ty);
                        let v2: Expr = rename_consts_go(f, memo, v);
                        let b: Expr = rename_consts_go(f, memo, body);
                        expr::let_e(t, v2, b)
                    }
                    ExprView::Proj(s, i, sub) => {
                        let u: Expr = rename_consts_go(f, memo, sub);
                        expr::proj(name::dup(s), *i, u)
                    }
                    _ => expr::dup(e),
                };
                memo.insert(expr::dup(e), expr::dup(&r));
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1111-1113 renameConstsFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:930-956 renameConsts
/// con-leche: ConLeche/Kernel/ExprOps.lean:1115-1118 renameConsts_eq_renameConstsFast
/// The executed `renameConsts`.
pub fn rename_consts<F>(f: &F, e: &Expr) -> Expr
where
    F: NameToName,
{
    let mut memo: HashMap<Expr, Expr> = HashMap::new();
    rename_consts_go(f, &mut memo, e)
}

// ---------------------------------------------------------------------------
// Telescopes (`ExprOps.lean:1118-1278`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams
/// Strip `k` leading lambdas: the binder list (outermost first) and the
/// body.  The `out = []` wrapper of the accumulator recursion below.
pub fn strip_lams(k: u64, e: &Expr) -> Option<(Vec<(Expr, BinderMeta)>, Expr)> {
    strip_lams_go(k, e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1120-1126 stripLams
/// The accumulator recursion behind `strip_lams`.  Deviation: Lean conses
/// the binder on the way *out* of the recursion; a `Vec` has no cons, so the
/// port pushes on the way *in*, which produces the same outermost-first list
/// (task #3's pattern 2).
pub fn strip_lams_go(
    k: u64,
    e: &Expr,
    mut out: Vec<(Expr, BinderMeta)>,
) -> Option<(Vec<(Expr, BinderMeta)>, Expr)> {
    if k == 0 {
        Some((out, expr::dup(e)))
    } else {
        match expr::view(&e) {
            ExprView::Lam(ty, b, m) => {
                out.push((expr::dup(ty), expr::binder_meta_dup(m)));
                strip_lams_go(k - 1, b, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis
/// Strip `k` leading `∀`s.  The `out = []` wrapper of the recursion below.
pub fn strip_pis(k: u64, e: &Expr) -> Option<(Vec<(Expr, BinderMeta)>, Expr)> {
    strip_pis_go(k, e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1128-1134 stripPis
/// The accumulator recursion behind `strip_pis` (see `strip_lams_go`).
pub fn strip_pis_go(
    k: u64,
    e: &Expr,
    mut out: Vec<(Expr, BinderMeta)>,
) -> Option<(Vec<(Expr, BinderMeta)>, Expr)> {
    if k == 0 {
        Some((out, expr::dup(e)))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(ty, b, m) => {
                out.push((expr::dup(ty), expr::binder_meta_dup(m)));
                strip_pis_go(k - 1, b, out)
            }
            _ => None,
        }
    }
}

/// con-leche: none — `List.get?` on a `stripPis` telescope at a `u64` index
/// The domain of binder `i` of a `strip_pis` result, without a `usize` cast.
/// Task #61's hazard: the index is a machine word of the checker's own
/// arithmetic (a parameter count) while `Vec` indexing is `usize`, so the
/// obvious `doms[i as usize].0` is a *truncating* cast under Aeneas
/// (DESIGN.md §3.4: no `as` on data).  The index is therefore consumed by
/// the recursion, and the `None` arm subsumes the caller's bounds test.
pub fn dom_at_n(doms: &Vec<(Expr, BinderMeta)>, i: u64) -> Option<Expr> {
    dom_at_n_from(doms, i, 0)
}

/// con-leche: none — the index recursion behind `dom_at_n`
/// `j` walks the `Vec` while `i` counts down, so no value ever crosses
/// between the two widths.
pub fn dom_at_n_from(doms: &Vec<(Expr, BinderMeta)>, i: u64, j: usize) -> Option<Expr> {
    if j >= doms.len() {
        None
    } else if i == 0 {
        Some(expr::dup(&doms[j].0))
    } else {
        dom_at_n_from(doms, i - 1, j + 1)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1136-1140 piResult
/// The body of a syntactic `∀`-telescope.
pub fn pi_result(e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::ForallE(_, b, _) => pi_result(b),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1142-1146 instPis
/// Instantiate a `∀`-telescope with arguments, in order.  The `i = 0`
/// wrapper of the index recursion below.
pub fn inst_pis(e: &Expr, args: &Vec<Expr>) -> Option<Expr> {
    inst_pis_from(e, args, 0)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1142-1146 instPis
/// The index recursion behind `inst_pis`.
pub fn inst_pis_from(e: &Expr, args: &Vec<Expr>, i: usize) -> Option<Expr> {
    if i >= args.len() {
        Some(expr::dup(e))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(_, body, _) => {
                let b: Expr = instantiate1(body, &args[i], 0);
                inst_pis_from(&b, args, i + 1)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1148-1156 instPisAt
/// Instantiate the leading `∀`-binders at the given arguments, returning
/// each binder's progressively instantiated domain with the residual.
pub fn inst_pis_at(args: &Vec<Expr>, e: &Expr) -> Option<(Vec<Expr>, Expr)> {
    inst_pis_at_from(args, 0, e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1148-1156 instPisAt
/// The index recursion behind `inst_pis_at`; the domain list is accumulated
/// on the way in, as in `strip_pis_go`.
pub fn inst_pis_at_from(
    args: &Vec<Expr>,
    i: usize,
    e: &Expr,
    mut out: Vec<Expr>,
) -> Option<(Vec<Expr>, Expr)> {
    if i >= args.len() {
        Some((out, expr::dup(e)))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(dom, body, _) => {
                out.push(expr::dup(dom));
                let b: Expr = instantiate1(body, &args[i], 0);
                inst_pis_at_from(args, i + 1, &b, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1158-1164 instLamsAt
/// `instPisAt` for `λ`-binders.
pub fn inst_lams_at(args: &Vec<Expr>, e: &Expr) -> Option<(Vec<Expr>, Expr)> {
    inst_lams_at_from(args, 0, e, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1158-1164 instLamsAt
/// The index recursion behind `inst_lams_at`.
pub fn inst_lams_at_from(
    args: &Vec<Expr>,
    i: usize,
    e: &Expr,
    mut out: Vec<Expr>,
) -> Option<(Vec<Expr>, Expr)> {
    if i >= args.len() {
        Some((out, expr::dup(e)))
    } else {
        match expr::view(&e) {
            ExprView::Lam(dom, body, _) => {
                out.push(expr::dup(dom));
                let b: Expr = instantiate1(body, &args[i], 0);
                inst_lams_at_from(args, i + 1, &b, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1181-1190 instPisAtFGo
/// Core of `instPisAtF`: `acc` holds the pending substitutions, innermost
/// binder first, and each domain receives them in one `instantiateList` pass
/// instead of one `instantiate1` pass per argument.
pub fn inst_pis_at_f_go(
    acc: &Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
    e: &Expr,
    mut out: Vec<Expr>,
) -> Option<(Vec<Expr>, Expr)> {
    if i >= args.len() {
        Some((out, instantiate_list_fast(e, acc, 0)))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(dom, body, _) => {
                out.push(instantiate_list_fast(dom, acc, 0));
                let acc2: Vec<Expr> = cons_expr(&args[i], acc);
                inst_pis_at_f_go(&acc2, args, i + 1, body, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1192-1196 instPisAtF
/// One-pass `instPisAt`, with the cited fall-back to the sequential
/// definition when the raw telescope is shorter than the argument list.
pub fn inst_pis_at_f(args: &Vec<Expr>, e: &Expr) -> Option<(Vec<Expr>, Expr)> {
    let acc: Vec<Expr> = Vec::new();
    match inst_pis_at_f_go(&acc, args, 0, e, Vec::new()) {
        Some(r) => Some(r),
        None => inst_pis_at(args, e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1198-1204 instLamsAtFGo
/// Core of `instLamsAtF` (the `λ` counterpart of `inst_pis_at_f_go`).
pub fn inst_lams_at_f_go(
    acc: &Vec<Expr>,
    args: &Vec<Expr>,
    i: usize,
    e: &Expr,
    mut out: Vec<Expr>,
) -> Option<(Vec<Expr>, Expr)> {
    if i >= args.len() {
        Some((out, instantiate_list_fast(e, acc, 0)))
    } else {
        match expr::view(&e) {
            ExprView::Lam(dom, body, _) => {
                out.push(instantiate_list_fast(dom, acc, 0));
                let acc2: Vec<Expr> = cons_expr(&args[i], acc);
                inst_lams_at_f_go(&acc2, args, i + 1, body, out)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1206-1210 instLamsAtF
/// One-pass `instLamsAt`.
pub fn inst_lams_at_f(args: &Vec<Expr>, e: &Expr) -> Option<(Vec<Expr>, Expr)> {
    let acc: Vec<Expr> = Vec::new();
    match inst_lams_at_f_go(&acc, args, 0, e, Vec::new()) {
        Some(r) => Some(r),
        None => inst_lams_at(args, e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1212-1217 fvarTypeD
/// The type annotation of a free-variable leaf (the expression itself
/// otherwise).
pub fn fvar_type_d(e: &Expr) -> Expr {
    match expr::view(&e) {
        ExprView::Fvar(_, ty) => expr::dup(ty),
        _ => expr::dup(e),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1219-1227 instSpine
/// Instantiate a telescope-context expression at an argument spine.  The
/// `i = 0` wrapper of the index recursion below.
pub fn inst_spine(args: &Vec<Expr>, t: u64, e: &Expr) -> Expr {
    inst_spine_from(args, 0, t, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1219-1227 instSpine
/// The index recursion behind `inst_spine`; the cursor's `t - 1` is Lean's
/// truncated `Nat` subtraction, hence `sub_nat`.
pub fn inst_spine_from(args: &Vec<Expr>, i: usize, t: u64, e: &Expr) -> Expr {
    if i >= args.len() {
        expr::dup(e)
    } else {
        let e2: Expr = instantiate1(e, &args[i], t);
        inst_spine_from(args, i + 1, sub_nat(t, 1), &e2)
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain
/// Is a recursor rule *canonical* — are the constructor's parameters exactly
/// the recursor's own leading arguments?  Deviations: the cited
/// `decide (cnP ≤ rP) && decide (rP ≤ mI) && …` becomes an `if` nest
/// (task #3's pattern 9), and the list comparison
/// `dom.getAppArgs.take cnP == (List.range cnP).map (fun k => .bvar (mI-1-k))`
/// becomes the index recursion below, whose "ran out of arguments" arm is
/// the length mismatch a short `List.take` would produce.
pub fn rec_rule_plain(rec_ty: &Expr, m_i: u64, r_p: u64, cn_p: u64) -> bool {
    if cn_p <= r_p {
        if r_p <= m_i {
            match strip_pis(m_i, rec_ty) {
                Some(r) => match expr::view(&r.1 ) {
                    ExprView::ForallE(dom, _, _) => {
                        let args: Vec<Expr> = get_app_args(dom);
                        rec_rule_args_eq(&args, m_i, cn_p, 0)
                    }
                    _ => false,
                },
                None => false,
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1229-1244 recRulePlain
/// The index recursion behind `rec_rule_plain`'s list comparison.
pub fn rec_rule_args_eq(args: &Vec<Expr>, m_i: u64, cn_p: u64, k: u64) -> bool {
    if k >= cn_p {
        true
    } else if k >= args.len() as u64 {
        false
    } else {
        let want: Expr = expr::bvar(sub_nat(sub_nat(m_i, 1), k));
        if expr::beq(&args[k as usize], &want) {
            rec_rule_args_eq(args, m_i, cn_p, k + 1)
        } else {
            false
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1246-1261 pisToLams
/// Convert the first `k` `∀`-binders into `λ`-binders over a body, at the
/// parse placeholder `.never` (the cited comment: a ∀'s `pw` claims the
/// codomain's prop-ness, which is not the λ's claim, so every consumer must
/// re-run the annotate pass over the result).
pub fn pis_to_lams(k: u64, e: &Expr, body: &Expr) -> Option<Expr> {
    if k == 0 {
        Some(expr::dup(body))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(ty, rest, _) => match pis_to_lams(k - 1, rest, body) {
                Some(b) => Some(expr::lam(
                    expr::dup(ty),
                    b,
                    expr::binder_meta(prop_when::never()),
                )),
                None => None,
            },
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1263-1269 replacePiBody
/// Replace the body under the first `k` `∀`-binders, domains and binder data
/// kept.
pub fn replace_pi_body(k: u64, e: &Expr, b: &Expr) -> Option<Expr> {
    if k == 0 {
        Some(expr::dup(b))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(ty, rest, m) => match replace_pi_body(k - 1, rest, b) {
                Some(r) => Some(expr::forall_e(expr::dup(ty), r, expr::binder_meta_dup(m))),
                None => None,
            },
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1271-1274 piArity
/// The length of the leading `∀`-telescope.
pub fn pi_arity(e: &Expr) -> u64 {
    match expr::view(&e) {
        ExprView::ForallE(_, b, _) => pi_arity(b) + 1,
        _ => 0,
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1276-1280 resultSort
/// The result sort at the end of a `∀`-telescope.
pub fn result_sort(e: &Expr) -> Option<Level> {
    match expr::view(&e) {
        ExprView::ForallE(_, b, _) => result_sort(b),
        ExprView::Sort(u) => Some(level::dup(u)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The derived-field spec functions, and the saturated branch
// (`ExprOps.lean:1293-1439`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:1295-1305 Expr.bvarBound
/// The least `k` with `looseBVarsBounded k` — the specification of the
/// packed word's `bvarB` field.  Unmemoized, as in the cited code; nothing
/// in the port calls it (the checker reads `bvar_b`, whose saturated branch
/// runs the memoized `bvar_bound_go` below), and it is kept so that the
/// provenance gate stays in step with its source.  The `- 1` under a binder
/// is Lean's truncated `Nat` subtraction, hence `sub_nat`.
pub fn bvar_bound(e: &Expr) -> u64 {
    match expr::view(&e) {
        ExprView::Bvar(i) => *i + 1,
        ExprView::Fvar(_, _) => 0,
        ExprView::Sort(_) => 0,
        ExprView::Const(_, _) => 0,
        ExprView::Lit(_) => 0,
        ExprView::App(f, a) => expr::max_u64(bvar_bound(f), bvar_bound(a)),
        ExprView::Lam(ty, body, _) => expr::max_u64(bvar_bound(ty), sub_nat(bvar_bound(body), 1)),
        ExprView::ForallE(ty, body, _) => {
            expr::max_u64(bvar_bound(ty), sub_nat(bvar_bound(body), 1))
        }
        ExprView::LetE(ty, val, body) => expr::max_u64(
            expr::max_u64(bvar_bound(ty), bvar_bound(val)),
            sub_nat(bvar_bound(body), 1),
        ),
        ExprView::Proj(_, _, sub) => bvar_bound(sub),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1314-1325 Expr.fvarRange
/// The least `d` with `fvarsBelow d` — the specification of the packed
/// word's `fvarB` field.  `fvar` type annotations are not descended into,
/// matching the abstraction traversals.  Unmemoized and uncalled, as
/// `bvar_bound` above.
pub fn fvar_range(e: &Expr) -> u64 {
    match expr::view(&e) {
        ExprView::Fvar(idx, _) => *idx + 1,
        ExprView::Bvar(_) => 0,
        ExprView::Sort(_) => 0,
        ExprView::Const(_, _) => 0,
        ExprView::Lit(_) => 0,
        ExprView::App(f, a) => expr::max_u64(fvar_range(f), fvar_range(a)),
        ExprView::Lam(ty, body, _) => expr::max_u64(fvar_range(ty), fvar_range(body)),
        ExprView::ForallE(ty, body, _) => expr::max_u64(fvar_range(ty), fvar_range(body)),
        ExprView::LetE(ty, val, body) => expr::max_u64(
            expr::max_u64(fvar_range(ty), fvar_range(val)),
            fvar_range(body),
        ),
        ExprView::Proj(_, _, sub) => fvar_range(sub),
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1370-1394 bvarBoundGo
/// Memoized `bvarBound`: the saturated branch's exact recomputation.  The
/// memo keeps the fallback linear in the DAG rather than in the unfolded
/// tree — con-leche's standing "no unmemoized traversals in executable
/// paths" rule applies to the saturated branch too.
pub fn bvar_bound_go(memo: &mut HashMap<Expr, u64>, e: &Expr) -> u64 {
    match memo_n_get(memo, e) {
        Some(r) => r,
        None => {
            let r: u64 = match expr::view(&e) {
                ExprView::Bvar(i) => *i + 1,
                ExprView::Fvar(_, _) => 0,
                ExprView::Sort(_) => 0,
                ExprView::Const(_, _) => 0,
                ExprView::Lit(_) => 0,
                ExprView::App(f, a) => {
                    let rf: u64 = bvar_bound_go(memo, f);
                    let ra: u64 = bvar_bound_go(memo, a);
                    expr::max_u64(rf, ra)
                }
                ExprView::Lam(ty, body, _) => {
                    let rt: u64 = bvar_bound_go(memo, ty);
                    let rb: u64 = bvar_bound_go(memo, body);
                    expr::max_u64(rt, sub_nat(rb, 1))
                }
                ExprView::ForallE(ty, body, _) => {
                    let rt: u64 = bvar_bound_go(memo, ty);
                    let rb: u64 = bvar_bound_go(memo, body);
                    expr::max_u64(rt, sub_nat(rb, 1))
                }
                ExprView::LetE(ty, val, body) => {
                    let rt: u64 = bvar_bound_go(memo, ty);
                    let rv: u64 = bvar_bound_go(memo, val);
                    let rb: u64 = bvar_bound_go(memo, body);
                    expr::max_u64(expr::max_u64(rt, rv), sub_nat(rb, 1))
                }
                ExprView::Proj(_, _, sub) => bvar_bound_go(memo, sub),
            };
            memo.insert(expr::dup(e), r);
            r
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1396-1397 bvarBoundMemo
/// con-leche: ConLeche/Kernel/ExprOps.lean:1571-1574 bvarBoundMemo_eq
/// One memoized `bvarBound` walk, the memo dropped on return.
pub fn bvar_bound_memo(e: &Expr) -> u64 {
    let mut memo: HashMap<Expr, u64> = HashMap::new();
    bvar_bound_go(&mut memo, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1399-1424 fvarRangeGo
/// Memoized `fvarRange`, the `fvar` twin of `bvar_bound_go`.
pub fn fvar_range_go(memo: &mut HashMap<Expr, u64>, e: &Expr) -> u64 {
    match memo_n_get(memo, e) {
        Some(r) => r,
        None => {
            let r: u64 = match expr::view(&e) {
                ExprView::Fvar(idx, _) => *idx + 1,
                ExprView::Bvar(_) => 0,
                ExprView::Sort(_) => 0,
                ExprView::Const(_, _) => 0,
                ExprView::Lit(_) => 0,
                ExprView::App(f, a) => {
                    let rf: u64 = fvar_range_go(memo, f);
                    let ra: u64 = fvar_range_go(memo, a);
                    expr::max_u64(rf, ra)
                }
                ExprView::Lam(ty, body, _) => {
                    let rt: u64 = fvar_range_go(memo, ty);
                    let rb: u64 = fvar_range_go(memo, body);
                    expr::max_u64(rt, rb)
                }
                ExprView::ForallE(ty, body, _) => {
                    let rt: u64 = fvar_range_go(memo, ty);
                    let rb: u64 = fvar_range_go(memo, body);
                    expr::max_u64(rt, rb)
                }
                ExprView::LetE(ty, val, body) => {
                    let rt: u64 = fvar_range_go(memo, ty);
                    let rv: u64 = fvar_range_go(memo, val);
                    let rb: u64 = fvar_range_go(memo, body);
                    expr::max_u64(expr::max_u64(rt, rv), rb)
                }
                ExprView::Proj(_, _, sub) => fvar_range_go(memo, sub),
            };
            memo.insert(expr::dup(e), r);
            r
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1426-1427 fvarRangeMemo
/// con-leche: ConLeche/Kernel/ExprOps.lean:1692-1695 fvarRangeMemo_eq
/// One memoized `fvarRange` walk.
pub fn fvar_range_memo(e: &Expr) -> u64 {
    let mut memo: HashMap<Expr, u64> = HashMap::new();
    fvar_range_go(&mut memo, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1429-1434 bvarB
/// con-leche: ConLeche/Kernel/ExprOps.lean:1576-1586 bvarB_eq
/// **The loose-bvar bound the checker reads**: the packed 15-bit field, or —
/// on the saturated branch alone — the exact memoized recomputation.  The
/// cited `bvarB_eq` is what keeps it equal to `Expr.bvarBound`
/// unconditionally, so no consumer grows a saturation guard.
pub fn bvar_b(e: &Expr) -> u64 {
    let r: u64 = expr::bvar_b_raw(e);
    if r == expr::sat_range() {
        bvar_bound_memo(e)
    } else {
        r
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:1436-1441 fvarB
/// con-leche: ConLeche/Kernel/ExprOps.lean:1697-1707 fvarB_eq
/// **The fvar range the checker reads**, the `fvar` twin of `bvar_b`.
pub fn fvar_b(e: &Expr) -> u64 {
    let r: u64 = expr::fvar_b_raw(e);
    if r == expr::sat_range() {
        fvar_range_memo(e)
    } else {
        r
    }
}

// ---------------------------------------------------------------------------
// Open-argument telescope instantiation, and the pointer shortcut
// (`ExprOps.lean:2365-2388`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift
/// con-leche: ConLeche/Cached/CheckerC.lean:31-35 instPisAtLiftC
/// Instantiate the leading `∀`-binders at *open* arguments, by the general
/// capture-avoiding substitution.  The `i = 0` wrapper of the recursion
/// below.
///
/// The cached driver's walker (`instPisAtLiftC`, the second citation) differs
/// only in taking `ExprC.instantiate1Lift` where this takes
/// `Expr.instantiate1Lift`; since con-leche's task #172 B3a there is one
/// expression type, so the port has one spelling (as for
/// `struct_parts::struct_proj_bodies`, whose Lean twin calls this one).
pub fn inst_pis_at_lift(args: &Vec<Expr>, e: &Expr) -> Option<Expr> {
    inst_pis_at_lift_from(args, 0, e)
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2367-2380 instPisAtLift
/// con-leche: ConLeche/Cached/CheckerC.lean:31-35 instPisAtLiftC
/// The index recursion behind `inst_pis_at_lift`.
pub fn inst_pis_at_lift_from(args: &Vec<Expr>, i: usize, e: &Expr) -> Option<Expr> {
    if i >= args.len() {
        Some(expr::dup(e))
    } else {
        match expr::view(&e) {
            ExprView::ForallE(_, body, _) => {
                let b: Expr = instantiate1_lift(body, &args[i], 0);
                inst_pis_at_lift_from(args, i + 1, &b)
            }
            _ => None,
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2384-2390 exprPtrBEq
/// Structural expression equality with a physical-equality shortcut.
/// Deviation (DESIGN.md §3.2): the cited `withPtrEq`'s pointer test is
/// modeled as `false`, so the model always takes the `beq` branch; the
/// obligation the fast path leaves is the reflexivity of `Expr.beq`, which
/// is what `withPtrEq`'s own `(fun h => by subst h; simp)` argument
/// discharges on the Lean side.  `expr::beq` opens with the same test, so
/// this is the cited composition.
pub fn expr_ptr_beq(a: &Expr, b: &Expr) -> bool {
    if expr::ptr_eq(a, b) {
        true
    } else {
        expr::beq(a, b)
    }
}

// ---------------------------------------------------------------------------
// Level-parameter occurrence, and `instantiateLevelParams`
// (`ExprOps.lean:2399-2724`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/ExprOps.lean:2422-2437 Expr.hasLevelParam
/// con-leche: ConLeche/Kernel/ExprOps.lean:2539-2544 Expr.hasLP_eq
/// Whether an expression mentions any level parameter — the specification of
/// the packed word's `hasLP` bit, binder prop-ness data included.  The
/// *executed* reading is `expr::has_lp`, the `O(1)` field read, and the
/// cited `hasLP_eq` is the equation between them; this walk is ported
/// because it is an executable `def` of the source.  Its level walkers are
/// `crate::kernel::level`'s `levelHasParam`/`levelsHaveParam`, which the same file's
/// `levelHasParam_eq`/`levelsHaveParam_eq` identify with `Level.hasParam`
/// and `List.any Level.hasParam`.
pub fn has_level_param(e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Bvar(_) => false,
        ExprView::Lit(_) => false,
        ExprView::Sort(u) => level::level_has_param(u),
        ExprView::Const(_, us) => level::levels_have_param(us),
        ExprView::Fvar(_, ty) => has_level_param(ty),
        ExprView::App(f, a) => has_level_param(f) || has_level_param(a),
        ExprView::Lam(ty, body, m) => {
            has_level_param(ty) || has_level_param(body) || prop_when::has_params(&m.pw)
        }
        ExprView::ForallE(ty, body, m) => {
            has_level_param(ty) || has_level_param(body) || prop_when::has_params(&m.pw)
        }
        ExprView::LetE(ty, val, body) => {
            has_level_param(ty) || has_level_param(val) || has_level_param(body)
        }
        ExprView::Proj(_, _, sub) => has_level_param(sub),
    }
}

/// con-leche: none — `vs.map (Level.subst ks us)` in `instLPGo`'s `.const` arm
/// The index recursion behind `levels_subst`.
pub fn levels_subst_from(
    ks: &Vec<Name>,
    us: &Vec<Level>,
    vs: &Vec<Level>,
    i: usize,
    mut out: Vec<Level>,
) -> Vec<Level> {
    if i >= vs.len() {
        out
    } else {
        out.push(level::subst(ks, us, &vs[i]));
        levels_subst_from(ks, us, vs, i + 1, out)
    }
}

/// con-leche: none — `vs.map (Level.subst ks us)` in `instLPGo`'s `.const` arm
/// `List.map` over a `Vec<Level>`; DESIGN.md §3.4 forbids the closure.
pub fn levels_subst(ks: &Vec<Name>, us: &Vec<Level>, vs: &Vec<Level>) -> Vec<Level> {
    levels_subst_from(ks, us, vs, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2566-2605 Expr.instLPGo
/// con-leche: ConLeche/Kernel/Level.lean:232-249 Expr.instantiateLevelParams
/// The memoized walk behind `instantiateLevelParams`: substitute level
/// parameters throughout, binder prop-ness data included.  The `!hasLP`
/// cutoff at the top is the packed word's bit; the memo covers what the bit
/// cannot, a shared node that *does* mention a parameter and is reached
/// along many paths.
///
/// The logical definition it replaces lives in `Kernel/Level.lean` — an
/// `Expr` operation spelled there because that is where `Level.subst` is —
/// so the port puts it in this module, and fills its two `Level.lean`
/// prerequisites (`Level.zeronessOf` `:189`, `Level.substPW` `:205`,
/// deferred at task #3 only because `PropWhen` did not exist yet) into
/// `crate::kernel::level`, where their file belongs.
pub fn instantiate_level_params_go(
    ks: &Vec<Name>,
    us: &Vec<Level>,
    memo: &mut HashMap<Expr, Expr>,
    e: &Expr,
) -> Expr {
    if !expr::has_lp(e) {
        expr::dup(e)
    } else {
        match expr::view(&e) {
            ExprView::Bvar(i) => expr::bvar(*i),
            ExprView::Lit(l) => expr::lit(expr::literal_dup(l)),
            ExprView::Sort(u) => expr::sort(level::subst(ks, us, u)),
            ExprView::Const(n, vs) => expr::mk_const(name::dup(n), levels_subst(ks, us, vs)),
            _ => match memo_e_get(memo, e) {
                Some(r) => r,
                None => {
                    let r: Expr = match expr::view(&e) {
                        ExprView::Fvar(idx, ty) => {
                            let t: Expr = instantiate_level_params_go(ks, us, memo, ty);
                            expr::fvar(*idx, t)
                        }
                        ExprView::App(f, a) => {
                            let f2: Expr = instantiate_level_params_go(ks, us, memo, f);
                            let a2: Expr = instantiate_level_params_go(ks, us, memo, a);
                            expr::app(f2, a2)
                        }
                        ExprView::Lam(ty, body, m) => {
                            let t: Expr = instantiate_level_params_go(ks, us, memo, ty);
                            let b: Expr = instantiate_level_params_go(ks, us, memo, body);
                            expr::lam(t, b, expr::binder_meta(level::subst_pw(ks, us, &m.pw)))
                        }
                        ExprView::ForallE(ty, body, m) => {
                            let t: Expr = instantiate_level_params_go(ks, us, memo, ty);
                            let b: Expr = instantiate_level_params_go(ks, us, memo, body);
                            expr::forall_e(t, b, expr::binder_meta(level::subst_pw(ks, us, &m.pw)))
                        }
                        ExprView::LetE(ty, val, body) => {
                            let t: Expr = instantiate_level_params_go(ks, us, memo, ty);
                            let w: Expr = instantiate_level_params_go(ks, us, memo, val);
                            let b: Expr = instantiate_level_params_go(ks, us, memo, body);
                            expr::let_e(t, w, b)
                        }
                        ExprView::Proj(s, i, sub) => {
                            let u2: Expr = instantiate_level_params_go(ks, us, memo, sub);
                            expr::proj(name::dup(s), *i, u2)
                        }
                        _ => expr::dup(e),
                    };
                    memo.insert(expr::dup(e), expr::dup(&r));
                    r
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/ExprOps.lean:2720-2722 Expr.instLPFast
/// con-leche: ConLeche/Kernel/ExprOps.lean:2724-2727 Expr.instantiateLevelParams_eq_instLPFast
/// con-leche: ConLeche/Kernel/Level.lean:232-249 Expr.instantiateLevelParams
/// The executed `instantiateLevelParams`.
pub fn instantiate_level_params(ks: &Vec<Name>, us: &Vec<Level>, e: &Expr) -> Expr {
    let mut memo: HashMap<Expr, Expr> = HashMap::new();
    instantiate_level_params_go(ks, us, &mut memo, e)
}

// ---------------------------------------------------------------------------
// `allLevelParamsDefined` (`Level.lean:251-412`), the second `Expr` operation
// spelled in `Kernel/Level.lean` for import order (task #13's note).  Task
// #24 needed it — `checkConstantVal` asks it of every declaration's type —
// and task #13 had left it owed.
// ---------------------------------------------------------------------------

/// con-leche: none — an owning probe of a `Bool`-valued memo
/// As `memo_e_get`/`memo_n_get`: `match memo[k]?` needs the map's borrow to
/// end before the miss branch mutates it (task #13's pattern 1).
pub fn memo_b_get(memo: &HashMap<Expr, bool>, k: &Expr) -> Option<bool> {
    match memo.get(k) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: none — the `&&` of a memoized walk's `(b₁ && b₂, memo)` result
/// **The conjunction as a call, not as a branch.**  Aeneas cannot match the
/// contexts when an arm of a `&mut`-threaded `match` ends in an `if` (or in a
/// short-circuiting `&&`, which is one) and the arms then join on the memo
/// insert — task #18's rule that a gated result whose arms rejoin must become
/// a call.  Both operands are computed before the call, so the memo is
/// threaded through every recursion exactly as the cited Lean threads it; a
/// short-circuit here would be a memo-policy deviation (DESIGN.md §3.1),
/// not just a shape one.
pub fn bool_and(a: bool, b: bool) -> bool {
    if a {
        b
    } else {
        false
    }
}

/// con-leche: none — the `b₁ && b₂ && b₃` of a three-way memoized walk arm
/// As `bool_and`, at three operands.
pub fn bool_and3(a: bool, b: bool, c: bool) -> bool {
    bool_and(bool_and(a, b), c)
}

/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// Are all level parameters occurring in `e` among `params`?  Binder
/// prop-ness data included (con-leche task #161): their parameters are level
/// parameters of the term, and `instantiateLevelParams`' composition law
/// needs them covered exactly as it needs the levels'.
///
/// **The specification**; the executed walk is `*_fast` below (`@[csimp]`).
/// Ported and uncalled, as task #11's `beqRecursive` rule asks.
pub fn all_level_params_defined(params: &Vec<Name>, e: &Expr) -> bool {
    match expr::view(&e) {
        ExprView::Bvar(_) => true,
        ExprView::Fvar(_, t) => all_level_params_defined(params, t),
        ExprView::Sort(u) => level::all_params_defined(params, u),
        ExprView::Const(_, us) => levels_all_params_defined(params, us, 0),
        ExprView::App(f, a) => {
            if all_level_params_defined(params, f) {
                all_level_params_defined(params, a)
            } else {
                false
            }
        }
        ExprView::Lam(t, b, m) => {
            if all_level_params_defined(params, t) {
                if all_level_params_defined(params, b) {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprView::ForallE(t, b, m) => {
            if all_level_params_defined(params, t) {
                if all_level_params_defined(params, b) {
                    prop_when::params_defined(params, &m.pw)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprView::LetE(t, v, b) => {
            if all_level_params_defined(params, t) {
                if all_level_params_defined(params, v) {
                    all_level_params_defined(params, b)
                } else {
                    false
                }
            } else {
                false
            }
        }
        ExprView::Lit(_) => true,
        ExprView::Proj(_, _, sub) => all_level_params_defined(params, sub),
    }
}

/// con-leche: none — `us.all (Level.allParamsDefined params)` of the `.const` arm
/// `List.all` over a `Vec<Level>` as an index recursion (task #3's pattern).
pub fn levels_all_params_defined(params: &Vec<Name>, us: &Vec<Level>, i: usize) -> bool {
    if i >= us.len() {
        true
    } else if level::all_params_defined(params, &us[i]) {
        levels_all_params_defined(params, us, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:299-332 Expr.allLevelParamsDefinedGo
/// con-leche: ConLeche/Kernel/Level.lean:251-268 Expr.allLevelParamsDefined
/// The memoized walk: the recursor-generation checks and `checkConstantVal`
/// ask it of a whole declaration type, and a tree walk does not finish on a
/// DAG-shared field type (con-leche task #215's `tower_struct`).  Keyed by
/// the node and dropped after each call, because the answer depends on
/// `params`; the leaf arms answer through the spec walk, as the Lean's do.
pub fn all_level_params_defined_go(
    params: &Vec<Name>,
    memo: &mut HashMap<Expr, bool>,
    e: &Expr,
) -> bool {
    match expr::view(&e) {
        ExprView::Bvar(_) => true,
        ExprView::Sort(u) => level::all_params_defined(params, u),
        ExprView::Const(_, us) => levels_all_params_defined(params, us, 0),
        ExprView::Lit(_) => true,
        _ => match memo_b_get(memo, e) {
            Some(r) => r,
            None => {
                let r: bool = match expr::view(&e) {
                    ExprView::Fvar(_, t) => all_level_params_defined_go(params, memo, t),
                    ExprView::App(f, a) => {
                        let b1: bool = all_level_params_defined_go(params, memo, f);
                        let b2: bool = all_level_params_defined_go(params, memo, a);
                        bool_and(b1, b2)
                    }
                    ExprView::Lam(t, b, m) => {
                        let b1: bool = all_level_params_defined_go(params, memo, t);
                        let b2: bool = all_level_params_defined_go(params, memo, b);
                        let b3: bool = prop_when::params_defined(params, &m.pw);
                        bool_and3(b1, b2, b3)
                    }
                    ExprView::ForallE(t, b, m) => {
                        let b1: bool = all_level_params_defined_go(params, memo, t);
                        let b2: bool = all_level_params_defined_go(params, memo, b);
                        let b3: bool = prop_when::params_defined(params, &m.pw);
                        bool_and3(b1, b2, b3)
                    }
                    ExprView::LetE(t, v, b) => {
                        let b1: bool = all_level_params_defined_go(params, memo, t);
                        let b2: bool = all_level_params_defined_go(params, memo, v);
                        let b3: bool = all_level_params_defined_go(params, memo, b);
                        bool_and3(b1, b2, b3)
                    }
                    ExprView::Proj(_, _, sub) => all_level_params_defined_go(params, memo, sub),
                    _ => all_level_params_defined(params, e),
                };
                memo.insert(expr::dup(e), r);
                r
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:405-407 Expr.allLevelParamsDefinedFast
/// con-leche: ConLeche/Kernel/Level.lean:409-412 Expr.allLevelParamsDefined_eq_allLevelParamsDefinedFast
/// The executed `allLevelParamsDefined` (one memoized DAG walk).  The cited
/// `@[csimp]` lemma is the kernel-checked equation with the spec walk, so
/// nothing downstream ever sees the memo (task #13's `@[csimp]` rule).
pub fn all_level_params_defined_fast(params: &Vec<Name>, e: &Expr) -> bool {
    let mut memo: HashMap<Expr, bool> = HashMap::new();
    all_level_params_defined_go(params, &mut memo, e)
}

/* Not ported from `ExprOps.lean` (DESIGN.md §3.1: the `theorem`s are the
   spec this port will be proved against, not part of it):

   * the eleven memo invariants — `Inst1MemoInv` (:60), `InstLMemoInv`
     (:247), `LiftMemoInv` (:410), `ResetMemoInv` (:561), `RenameMemoInv`
     (:980), `MemoBInv` (:1494), `MemoFInv` (:1615), `Abs1MemoInv` (:1769),
     `LowerMemoInv` (:1992), `Inst1LMemoInv` (:2202) and `ILPMemoInv`
     (:2543) — and their `empty`/`insert` lemmas.  They are `Prop`s ("every
     recorded answer is the real one"); Charon erases `Prop`s, and these are
     exactly the invariants the Rust-side refinement proof will restate
     about `crate::ron::hashmap` memos.
   * every `theorem`: the `*Go_spec` soundness lemmas, the eleven `@[csimp]`
     equations (each cited on the item it licenses), `sizeB_instantiate1`
     (:750), `looseBVarsBounded_iff` (:1305), `hasFvar_eq_false_iff` (:1325),
     `fvarRange_bne_zero` (:1332), `bvarBRaw_exact` (:1453),
     `fvarBRaw_exact` (:1587), `bvarB_eq`/`fvarB_eq`,
     `abstract1_of_fvarRange_le` (:1762), `lowerBVars_of_bvarBound_le`
     (:1956), `instantiate1Lift_of_bvarBound_le` (:2166),
     `Level.subst_eq_self` (:2408), `Level.allParamsDefined_of_not_hasParam`
     (:2414), `Level.substPW_eq_self` (:2439),
     `PropWhen.paramsDefined_of_not_hasParams` (:2450),
     `Expr.instantiateLevelParams_eq_self` (:2462),
     `Expr.levelHasParam_eq`/`levelsHaveParam_eq`/`hasLP_eq`, and
     `Expr.allLevelParamsDefined_of_not_hasLevelParam` (:2727).
   * `Level.hasParam` (:2399) is not a new function: it is the spec
     recurrence of `Expr.levelHasParam`, which task #3 ported as
     `level::level_has_param`; the citation for it sits there. */

#[cfg(test)]
mod tests {
    use crate::kernel::expr;
    use crate::kernel::expr::BinderMeta;
    use crate::kernel::expr::Expr;
    use crate::kernel::expr::ExprView;
    use crate::ron::node;
    use crate::kernel::expr_ops;
    use crate::kernel::expr_ops::NameToName;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::ron::nat;
    use crate::kernel::prop_when;

    fn nm(s: &str) -> Name {
        name::mk_str(name::anonymous(), s.chars().map(|c| c as u32).collect())
    }

    fn bm_never() -> BinderMeta {
        expr::binder_meta(prop_when::never())
    }

    fn cst(s: &str) -> Expr {
        expr::mk_const(nm(s), Vec::new())
    }

    fn cst_at(s: &str, ps: &[&str]) -> Expr {
        let mut us: Vec<Level> = Vec::new();
        for p in ps {
            us.push(level::param(nm(p)));
        }
        expr::mk_const(nm(s), us)
    }

    fn app2(f: Expr, a: Expr) -> Expr {
        expr::app(f, a)
    }

    fn lam(ty: Expr, b: Expr) -> Expr {
        expr::lam(ty, b, bm_never())
    }

    fn pi(ty: Expr, b: Expr) -> Expr {
        expr::forall_e(ty, b, bm_never())
    }

    /// A 5-argument spine `f a0 a1 a2 a3 a4` over shared constants.
    fn spine5() -> (Expr, Vec<Expr>) {
        let head: Expr = cst("f");
        let mut args: Vec<Expr> = Vec::new();
        args.push(cst("a0"));
        args.push(cst("a1"));
        args.push(cst("a2"));
        args.push(cst("a3"));
        args.push(cst("a4"));
        let mut e: Expr = expr::dup(&head);
        for a in args.iter() {
            e = expr::app(e, expr::dup(a));
        }
        (e, args)
    }

    // -- instantiate / abstract -------------------------------------------

    #[test]
    fn instantiate1_replaces_bvar_zero_and_lowers_the_rest() {
        // `fun _ => bvar 0 (bvar 1)` — body is `bvar 0 applied to bvar 1`.
        let body: Expr = app2(expr::bvar(0), expr::bvar(1));
        let v: Expr = cst("v");
        let got: Expr = expr_ops::instantiate1(&body, &v, 0);
        let want: Expr = app2(expr::dup(&v), expr::bvar(0));
        assert!(expr::beq(&got, &want));
        // Under one binder the cursor moves: `bvar 1` is the target.
        let under: Expr = lam(cst("T"), app2(expr::bvar(1), expr::bvar(0)));
        let got2: Expr = expr_ops::instantiate1(&under, &v, 0);
        let want2: Expr = lam(cst("T"), app2(expr::dup(&v), expr::bvar(0)));
        assert!(expr::beq(&got2, &want2));
    }

    #[test]
    fn instantiate1_and_abstract1_round_trip_on_a_shared_dag() {
        // `shared` occurs three times in `body`, so the memo is exercised.
        let shared: Expr = app2(cst("g"), expr::bvar(0));
        let body: Expr = expr::let_e(
            expr::dup(&shared),
            app2(expr::dup(&shared), expr::dup(&shared)),
            app2(expr::bvar(1), expr::bvar(0)),
        );
        let fv: Expr = expr::fvar(7, cst("T"));
        let opened: Expr = expr_ops::instantiate1(&body, &fv, 0);
        let closed: Expr = expr_ops::abstract1(&opened, 7, 0);
        assert!(expr::beq(&closed, &body));
        // The opened term really mentions the variable, the closed one does not.
        assert!(expr_ops::has_fvar(&opened));
        assert!(!expr_ops::has_fvar(&closed));
    }

    #[test]
    fn instantiate_list_is_the_fold_of_instantiate1() {
        // `bvar 0`, `bvar 1`, `bvar 2` in a term; vs = [v0, v1].
        let e: Expr = app2(
            app2(expr::bvar(0), expr::bvar(1)),
            app2(expr::bvar(2), lam(cst("T"), expr::bvar(3))),
        );
        let mut vs: Vec<Expr> = Vec::new();
        vs.push(cst("v0"));
        vs.push(cst("v1"));
        let got: Expr = expr_ops::instantiate_list_fast(&e, &vs, 0);
        // The fold: instantiate1 at v0 (d = 0) after instantiateList at [v1] (d = 1)
        // is `instantiateList e [v0, v1] 0`; check against the explicit answer.
        let want: Expr = app2(
            app2(cst("v0"), cst("v1")),
            app2(expr::bvar(0), lam(cst("T"), expr::bvar(1))),
        );
        assert!(expr::beq(&got, &want));
        // The pure walk and the memoized walk agree.
        assert!(expr::beq(&got, &expr_ops::instantiate_list(&e, &vs, 0)));
    }

    #[test]
    fn abstract_range_closes_a_block_of_variables_outermost_first() {
        // fvar 3 and fvar 4, abstracted as a two-binder block at d = 3.
        let e: Expr = app2(expr::fvar(3, cst("A")), expr::fvar(4, cst("B")));
        let got: Expr = expr_ops::abstract_range(&e, 3, 2, 0);
        // idx = 3 ↦ bvar (0 + (3 + 2 - 1 - 3)) = bvar 1; idx = 4 ↦ bvar 0.
        let want: Expr = app2(expr::bvar(1), expr::bvar(0));
        assert!(expr::beq(&got, &want));
        // Out of range is untouched, and the cursor bumps under a binder.
        let e2: Expr = lam(cst("T"), expr::fvar(3, cst("A")));
        let got2: Expr = expr_ops::abstract_range(&e2, 3, 2, 0);
        let want2: Expr = lam(cst("T"), expr::bvar(2));
        assert!(expr::beq(&got2, &want2));
        let e3: Expr = expr::fvar(9, cst("A"));
        assert!(expr::beq(&expr_ops::abstract_range(&e3, 3, 2, 0), &e3));
    }

    #[test]
    fn lift_and_lower_are_inverse_outside_the_window() {
        let e: Expr = lam(
            cst("T"),
            app2(expr::bvar(0), app2(expr::bvar(1), expr::bvar(5))),
        );
        let up: Expr = expr_ops::lift_loose_bvars(3, 0, &e);
        let want: Expr = lam(
            cst("T"),
            app2(expr::bvar(0), app2(expr::bvar(4), expr::bvar(8))),
        );
        assert!(expr::beq(&up, &want));
        let down: Expr = expr_ops::lower_bvars(3, 0, &up);
        assert!(expr::beq(&down, &e));
    }

    #[test]
    fn instantiate1_lift_shifts_an_open_replacement() {
        // Replace `bvar 0` under one binder by the open term `bvar 0`.
        let body: Expr = lam(cst("T"), expr::bvar(1));
        let v: Expr = expr::bvar(0);
        let got: Expr = expr_ops::instantiate1_lift(&body, &v, 0);
        // Crossing one binder lifts `v` by one.
        let want: Expr = lam(cst("T"), expr::bvar(1));
        assert!(expr::beq(&got, &want));
        // `instantiate1` would not have lifted it.
        let plain: Expr = expr_ops::instantiate1(&body, &v, 0);
        assert!(expr::beq(&plain, &lam(cst("T"), expr::bvar(0))));
    }

    // -- the saturation boundary ------------------------------------------

    /// A node with a hand-built data word: the packed fields are what
    /// `bvar_b`/`fvar_b` read, and a saturated one must send them to the
    /// memoized walk.  `expr.rs`'s smart constructors cannot produce a
    /// saturated word without 32 767 real binders, so the test synthesises
    /// the word directly — which is exactly the boundary logic under test.
    fn word(b: u64, f: u64) -> u64 {
        expr::pack_data(0, b, f, false)
    }

    fn bvar_with_word(i: u64, b: u64, f: u64) -> Expr {
        node::alloc_bvar(word(b, f), i)
    }

    fn fvar_with_word(idx: u64, ty: Expr, b: u64, f: u64) -> Expr {
        node::alloc_fvar(word(b, f), idx, ty)
    }

    fn lam_with_word(ty: Expr, body: Expr, m: BinderMeta, b: u64, f: u64) -> Expr {
        node::alloc_lam(word(b, f), ty, body, m)
    }

    #[test]
    fn bvar_b_and_fvar_b_read_the_field_below_saturation() {
        let e: Expr = bvar_with_word(4, 5, 0);
        assert_eq!(expr::bvar_b_raw(&e), 5);
        assert_eq!(expr_ops::bvar_b(&e), 5);
        // 32 766 is still a stored value, not the saturation sentinel.
        let e2: Expr = bvar_with_word(4, 32766, 0);
        assert_eq!(expr_ops::bvar_b(&e2), 32766);
        let e3: Expr = fvar_with_word(2, cst("T"), 0, 32766);
        assert_eq!(expr_ops::fvar_b(&e3), 32766);
    }

    #[test]
    fn a_saturated_word_falls_back_to_the_exact_memoized_walk() {
        assert_eq!(expr::sat_range(), 32767);
        // The word claims saturation; the node is `bvar 4`, whose exact
        // bound is 5.  The fallback must give 5, not 32 767.
        let e: Expr = bvar_with_word(4, expr::sat_range(), 0);
        assert_eq!(expr::bvar_b_raw(&e), 32767);
        assert_eq!(expr_ops::bvar_b(&e), 5);
        assert_eq!(expr_ops::bvar_bound_memo(&e), 5);
        assert_eq!(expr_ops::bvar_bound(&e), 5);
        // The same for the fvar range.
        let g: Expr = fvar_with_word(6, cst("T"), 0, expr::sat_range());
        assert_eq!(expr_ops::fvar_b(&g), 7);
        assert_eq!(expr_ops::fvar_range_memo(&g), 7);
        assert_eq!(expr_ops::fvar_range(&g), 7);
        // And a saturated *interior* node: the walk descends through it.
        let inner: Expr = bvar_with_word(9, expr::sat_range(), 0);
        let outer: Expr = lam_with_word(
            cst("T"),
            expr::dup(&inner),
            bm_never(),
            expr::sat_range(),
            0,
        );
        assert_eq!(expr_ops::bvar_b(&outer), 9);
        assert_eq!(expr_ops::bvar_bound(&outer), 9);
    }

    #[test]
    fn the_memoized_range_walks_agree_with_the_spec_recurrences() {
        let shared: Expr = app2(expr::bvar(2), expr::fvar(3, cst("T")));
        let battery: Vec<Expr> = vec![
            expr::bvar(0),
            expr::bvar(11),
            expr::fvar(4, cst("T")),
            cst("c"),
            expr::sort(level::zero()),
            expr::lit(expr::literal_nat(nat::from_u64(7))),
            expr::dup(&shared),
            lam(expr::dup(&shared), expr::dup(&shared)),
            pi(expr::dup(&shared), expr::bvar(0)),
            expr::let_e(expr::dup(&shared), expr::bvar(5), expr::dup(&shared)),
            expr::proj(nm("S"), 1, expr::dup(&shared)),
        ];
        for e in battery.iter() {
            assert_eq!(expr_ops::bvar_bound_memo(e), expr_ops::bvar_bound(e));
            assert_eq!(expr_ops::fvar_range_memo(e), expr_ops::fvar_range(e));
            // Below saturation the field and the walk agree too.
            assert_eq!(expr_ops::bvar_b(e), expr_ops::bvar_bound(e));
            assert_eq!(expr_ops::fvar_b(e), expr_ops::fvar_range(e));
        }
    }

    #[test]
    fn has_loose_bvar_under_binders() {
        // `bvar 0` is loose at the root, bound under one binder.
        let v0: Expr = expr::bvar(0);
        assert!(!expr_ops::loose_bvars_bounded(0, &v0));
        assert!(expr_ops::loose_bvars_bounded(1, &v0));
        let under1: Expr = lam(cst("T"), expr::dup(&v0));
        assert!(expr_ops::loose_bvars_bounded(0, &under1));
        // `bvar 1` needs two binders.
        let v1: Expr = expr::bvar(1);
        let under1b: Expr = lam(cst("T"), expr::dup(&v1));
        assert!(!expr_ops::loose_bvars_bounded(0, &under1b));
        assert!(expr_ops::loose_bvars_bounded(1, &under1b));
        let under2: Expr = lam(cst("T"), lam(cst("T"), expr::dup(&v1)));
        assert!(expr_ops::loose_bvars_bounded(0, &under2));
        // A binder's *domain* is not under the binder.
        let dom: Expr = lam(expr::dup(&v0), cst("c"));
        assert!(!expr_ops::loose_bvars_bounded(0, &dom));
        // `letE`: only the body is under the binder.
        let le: Expr = expr::let_e(cst("T"), expr::dup(&v0), expr::dup(&v0));
        assert!(!expr_ops::loose_bvars_bounded(0, &le));
        let le2: Expr = expr::let_e(cst("T"), cst("c"), expr::dup(&v0));
        assert!(expr_ops::loose_bvars_bounded(0, &le2));
        // `proj` does not bind.
        let pj: Expr = expr::proj(nm("S"), 0, expr::dup(&v0));
        assert!(!expr_ops::loose_bvars_bounded(0, &pj));
        // A closed term is bounded by 0.
        assert!(expr_ops::loose_bvars_bounded(0, &cst("c")));
        assert!(expr_ops::loose_bvars_bounded(0, &expr::fvar(3, cst("T"))));
    }

    // -- spines -------------------------------------------------------------

    #[test]
    fn get_app_fn_and_get_app_args_on_a_five_argument_application() {
        let (e, args) = spine5();
        assert!(expr::beq(&expr_ops::get_app_fn(&e), &cst("f")));
        let got: Vec<Expr> = expr_ops::get_app_args(&e);
        assert_eq!(got.len(), 5);
        for i in 0..5 {
            assert!(expr::beq(&got[i], &args[i]));
        }
        // Rebuilding from head and arguments reproduces the spine.
        let rebuilt: Expr = expr_ops::mk_app_n(expr_ops::get_app_fn(&e), &got);
        assert!(expr::beq(&rebuilt, &e));
        // A non-application is its own head with no arguments.
        let c: Expr = cst("c");
        assert!(expr::beq(&expr_ops::get_app_fn(&c), &c));
        assert_eq!(expr_ops::get_app_args(&c).len(), 0);
    }

    #[test]
    fn telescopes_strip_instantiate_and_rebuild() {
        // `∀ A B C, body` with `body` mentioning all three.
        let body: Expr = app2(
            app2(expr::bvar(2), expr::bvar(1)),
            app2(expr::bvar(0), cst("k")),
        );
        let ty: Expr = pi(cst("A"), pi(cst("B"), pi(cst("C"), expr::dup(&body))));
        assert_eq!(expr_ops::pi_arity(&ty), 3);
        let stripped = expr_ops::strip_pis(3, &ty);
        match stripped {
            Some(r) => {
                assert_eq!(r.0.len(), 3);
                assert!(expr::beq(&r.0[0].0, &cst("A")));
                assert!(expr::beq(&r.0[2].0, &cst("C")));
                assert!(expr::beq(&r.1, &body));
            }
            None => panic!("strip_pis failed"),
        }
        assert!(expr_ops::strip_pis(4, &ty).is_none());
        assert!(expr_ops::strip_lams(1, &ty).is_none());
        // `dom_at_n`: in range, out of range, and the empty telescope.
        match expr_ops::strip_pis(3, &ty) {
            Some(r) => {
                match expr_ops::dom_at_n(&r.0, 0) {
                    Some(d) => assert!(expr::beq(&d, &cst("A"))),
                    None => panic!("dom_at_n 0 failed"),
                }
                match expr_ops::dom_at_n(&r.0, 2) {
                    Some(d) => assert!(expr::beq(&d, &cst("C"))),
                    None => panic!("dom_at_n 2 failed"),
                }
                assert!(expr_ops::dom_at_n(&r.0, 3).is_none());
                assert!(expr_ops::dom_at_n(&r.0, 4).is_none());
            }
            None => panic!("strip_pis failed"),
        }
        let empty: Vec<(Expr, BinderMeta)> = Vec::new();
        assert!(expr_ops::dom_at_n(&empty, 0).is_none());
        assert!(expr_ops::dom_at_n(&empty, 7).is_none());
        assert!(expr::beq(&expr_ops::pi_result(&ty), &body));
        // `instPis` and `instPisAt` agree, and `instPisAtF` agrees with both.
        let mut args: Vec<Expr> = Vec::new();
        args.push(cst("x"));
        args.push(cst("y"));
        args.push(cst("z"));
        let want: Expr = app2(app2(cst("x"), cst("y")), app2(cst("z"), cst("k")));
        match expr_ops::inst_pis(&ty, &args) {
            Some(r) => assert!(expr::beq(&r, &want)),
            None => panic!("inst_pis failed"),
        }
        let seq = expr_ops::inst_pis_at(&args, &ty);
        let fast = expr_ops::inst_pis_at_f(&args, &ty);
        match (seq, fast) {
            (Some(a), Some(b)) => {
                assert_eq!(a.0.len(), 3);
                assert_eq!(b.0.len(), 3);
                for i in 0..3 {
                    assert!(expr::beq(&a.0[i], &b.0[i]));
                }
                assert!(expr::beq(&a.1, &b.1));
                assert!(expr::beq(&a.1, &want));
            }
            _ => panic!("inst_pis_at disagreement"),
        }
        // `pisToLams` and `replacePiBody` over the same telescope.
        match expr_ops::pis_to_lams(3, &ty, &cst("B0")) {
            Some(l) => {
                assert!(expr_ops::is_lam(&l));
                match expr_ops::strip_lams(3, &l) {
                    Some(r) => assert!(expr::beq(&r.1, &cst("B0"))),
                    None => panic!("strip_lams failed"),
                }
            }
            None => panic!("pis_to_lams failed"),
        }
        match expr_ops::replace_pi_body(3, &ty, &cst("B1")) {
            Some(p) => assert!(expr::beq(&expr_ops::pi_result(&p), &cst("B1"))),
            None => panic!("replace_pi_body failed"),
        }
        // `resultSort` walks to the end of the telescope.
        let ty2: Expr = pi(cst("A"), expr::sort(level::succ(level::zero())));
        assert!(expr_ops::result_sort(&ty2).is_some());
        assert!(expr_ops::result_sort(&ty).is_none());
    }

    #[test]
    fn inst_lams_at_and_its_one_pass_twin_agree() {
        let body: Expr = app2(expr::bvar(1), expr::bvar(0));
        let l: Expr = lam(cst("A"), lam(cst("B"), expr::dup(&body)));
        let mut args: Vec<Expr> = Vec::new();
        args.push(cst("p"));
        args.push(cst("q"));
        let seq = expr_ops::inst_lams_at(&args, &l);
        let fast = expr_ops::inst_lams_at_f(&args, &l);
        match (seq, fast) {
            (Some(a), Some(b)) => {
                assert!(expr::beq(&a.1, &b.1));
                assert!(expr::beq(&a.1, &app2(cst("p"), cst("q"))));
                assert_eq!(a.0.len(), 2);
                assert_eq!(b.0.len(), 2);
            }
            _ => panic!("inst_lams_at disagreement"),
        }
        // Too many arguments: both report `none` and the `*F` wrapper falls
        // back to the sequential answer, which is also `none`.
        args.push(cst("r"));
        assert!(expr_ops::inst_lams_at(&args, &l).is_none());
        assert!(expr_ops::inst_lams_at_f(&args, &l).is_none());
    }

    #[test]
    fn inst_spine_and_fvar_type_d_and_rec_rule_plain() {
        let e: Expr = app2(expr::bvar(2), expr::bvar(1));
        let mut args: Vec<Expr> = Vec::new();
        args.push(cst("a"));
        args.push(cst("b"));
        let got: Expr = expr_ops::inst_spine(&args, 2, &e);
        assert!(expr::beq(&got, &app2(cst("a"), cst("b"))));
        // `t - 1` truncates rather than underflowing.
        assert_eq!(expr_ops::sub_nat(0, 1), 0);
        assert_eq!(expr_ops::sub_nat(5, 2), 3);
        // `fvarTypeD`.
        let fv: Expr = expr::fvar(1, cst("T"));
        assert!(expr::beq(&expr_ops::fvar_type_d(&fv), &cst("T")));
        assert!(expr::beq(&expr_ops::fvar_type_d(&cst("c")), &cst("c")));
        // `recRulePlain`: `∀ x y, (I (bvar 1) (bvar 0)) → …` with mI = 2.
        let major: Expr = pi(
            app2(app2(cst("I"), expr::bvar(1)), expr::bvar(0)),
            cst("motive"),
        );
        let rec_ty: Expr = pi(cst("A"), pi(cst("B"), major));
        assert!(expr_ops::rec_rule_plain(&rec_ty, 2, 2, 2));
        // A non-canonical rule: the major premise applies `I` to something else.
        let major2: Expr = pi(app2(cst("I"), cst("Nat")), cst("motive"));
        let rec_ty2: Expr = pi(cst("A"), pi(cst("B"), major2));
        assert!(!expr_ops::rec_rule_plain(&rec_ty2, 2, 2, 1));
        // The arity guards.
        assert!(!expr_ops::rec_rule_plain(&rec_ty, 2, 1, 2));
        assert!(!expr_ops::rec_rule_plain(&rec_ty, 1, 2, 1));
    }

    // -- rebuild walks ------------------------------------------------------

    struct CToD;

    impl NameToName for CToD {
        fn rename(&self, n: &Name) -> Name {
            if name::beq(n, &nm("C")) {
                nm("D")
            } else {
                name::dup(n)
            }
        }
    }

    #[test]
    fn rename_consts_renames_constants_but_not_projection_names() {
        let shared: Expr = cst("C");
        let e: Expr = expr::proj(
            nm("S"),
            0,
            app2(
                expr::fvar(0, expr::dup(&shared)),
                lam(expr::dup(&shared), app2(expr::dup(&shared), cst("E"))),
            ),
        );
        let got: Expr = expr_ops::rename_consts(&CToD, &e);
        let want: Expr = expr::proj(
            nm("S"),
            0,
            app2(
                expr::fvar(0, cst("D")),
                lam(cst("D"), app2(cst("D"), cst("E"))),
            ),
        );
        assert!(expr::beq(&got, &want));
        // The `.proj` structure name is untouched — that is the cited W5 rule.
        match expr::view(&got) {
            ExprView::Proj(s, _, _) => assert!(name::beq(s, &nm("S"))),
            _ => panic!("not a proj"),
        }
    }

    #[test]
    fn reset_meta_clears_every_binder_datum() {
        let mut ps: Vec<Name> = Vec::new();
        ps.push(nm("u"));
        let bm = expr::binder_meta(prop_when::if_all_zero(ps));
        let e: Expr = expr::fvar(
            0,
            expr::forall_e(cst("A"), expr::lam(cst("B"), cst("C"), bm), bm_never()),
        );
        let got: Expr = expr_ops::reset_meta(&e);
        // Every λ/∀ datum is `never` afterwards, and was not before.
        fn all_never(e: &Expr) -> bool {
            match expr::view(&e) {
                ExprView::Lam(t, b, m) => {
                    prop_when::is_never(&m.pw) && all_never(t) && all_never(b)
                }
                ExprView::ForallE(t, b, m) => {
                    prop_when::is_never(&m.pw) && all_never(t) && all_never(b)
                }
                ExprView::App(f, a) => all_never(f) && all_never(a),
                ExprView::Fvar(_, t) => all_never(t),
                ExprView::LetE(t, v, b) => all_never(t) && all_never(v) && all_never(b),
                ExprView::Proj(_, _, s) => all_never(s),
                _ => true,
            }
        }
        assert!(!all_never(&e));
        assert!(all_never(&got));
    }

    #[test]
    fn instantiate_level_params_substitutes_sorts_constants_and_binder_data() {
        let mut ks: Vec<Name> = Vec::new();
        ks.push(nm("u"));
        let mut us: Vec<Level> = Vec::new();
        us.push(level::succ(level::zero()));
        let mut ps: Vec<Name> = Vec::new();
        ps.push(nm("u"));
        let bm = expr::binder_meta(prop_when::if_all_zero(ps));
        let e: Expr = expr::forall_e(
            expr::sort(level::param(nm("u"))),
            cst_at("C", &["u"]),
            bm,
        );
        assert!(expr::has_lp(&e));
        let got: Expr = expr_ops::instantiate_level_params(&ks, &us, &e);
        // `sort u` ↦ `sort 1`, `C.{u}` ↦ `C.{1}`, and the datum's `u` is
        // replaced by `zeronessOf 1 = never`.
        let want: Expr = expr::forall_e(
            expr::sort(level::succ(level::zero())),
            expr::mk_const(nm("C"), {
                let mut v: Vec<Level> = Vec::new();
                v.push(level::succ(level::zero()));
                v
            }),
            expr::binder_meta(prop_when::never()),
        );
        assert!(expr::beq(&got, &want));
        assert!(!expr::has_lp(&got));
        // A term with no level parameter is returned unchanged by the flag.
        let closed: Expr = cst("c");
        assert!(!expr::has_lp(&closed));
        assert!(expr::beq(
            &expr_ops::instantiate_level_params(&ks, &us, &closed),
            &closed
        ));
        // `has_level_param` is the specification of that flag.
        assert!(expr_ops::has_level_param(&e));
        assert!(!expr_ops::has_level_param(&got));
        assert!(!expr_ops::has_level_param(&closed));
    }

    // -- the leaf predicates ------------------------------------------------

    #[test]
    fn sizes_leaves_and_the_scope_check() {
        let ty: Expr = cst("T");
        let fv: Expr = expr::fvar(2, expr::dup(&ty));
        let e: Expr = app2(expr::dup(&fv), expr::bvar(0));
        // `sizeB` counts an `fvar` as a leaf, `sizeF` descends into it.
        assert_eq!(expr_ops::size_b(&e), 3);
        assert_eq!(expr_ops::size_f(&e), 4);
        // `fvarLeaves` reports every reachable leaf, hereditarily.
        let nested: Expr = expr::fvar(5, expr::dup(&fv));
        let leaves: Vec<(u64, Expr)> = expr_ops::fvar_leaves(&nested);
        assert_eq!(leaves.len(), 2);
        assert_eq!(leaves[0].0, 5);
        assert_eq!(leaves[1].0, 2);
        // `wscopedB`: an index must be below `d`, and an annotation's below it.
        assert!(expr_ops::wscoped_b(3, &e));
        assert!(!expr_ops::wscoped_b(2, &e));
        assert!(expr_ops::wscoped_b(6, &nested));
        let bad: Expr = expr::fvar(1, expr::fvar(4, expr::dup(&ty)));
        assert!(!expr_ops::wscoped_b(9, &bad));
        // `isLam`, `lamPw`, `forallPw`.
        let l: Expr = lam(expr::dup(&ty), cst("b"));
        let p: Expr = pi(expr::dup(&ty), cst("b"));
        assert!(expr_ops::is_lam(&l));
        assert!(!expr_ops::is_lam(&p));
        assert!(expr_ops::lam_pw(&l).is_some());
        assert!(expr_ops::lam_pw(&p).is_none());
        assert!(expr_ops::forall_pw(&p).is_some());
        assert!(expr_ops::forall_pw(&l).is_none());
        // `exprPtrBEq` is `beq` with the pointer path in front.
        assert!(expr_ops::expr_ptr_beq(&e, &expr::dup(&e)));
        assert!(expr_ops::expr_ptr_beq(&e, &app2(expr::fvar(2, cst("T")), expr::bvar(0))));
        assert!(!expr_ops::expr_ptr_beq(&e, &cst("other")));
    }
    /// `allLevelParamsDefined` reads the *binder data*'s parameters too, as
    /// the cited definition does (con-leche task #161), and the memoized
    /// walk agrees with the specification.  (Task #25's test, moved here with
    /// the function.)
    #[test]
    fn all_level_params_defined_reads_binder_data() {
        let u = nm("u");
        let mut ps: Vec<Name> = Vec::new();
        ps.push(name::dup(&u));
        let sort_u = expr::sort(level::param(name::dup(&u)));
        assert!(expr_ops::all_level_params_defined_fast(&ps, &sort_u));
        assert!(!expr_ops::all_level_params_defined_fast(&Vec::new(), &sort_u));
        // the datum's parameters count
        let mut qs: Vec<Name> = Vec::new();
        qs.push(name::dup(&u));
        let pi = expr::forall_e(
            expr::sort(level::zero()),
            expr::bvar(0),
            expr::binder_meta(prop_when::if_all_zero(qs)),
        );
        assert!(expr_ops::all_level_params_defined_fast(&ps, &pi));
        assert!(!expr_ops::all_level_params_defined_fast(&Vec::new(), &pi));
        // and the executed walk agrees with the specification
        assert_eq!(
            expr_ops::all_level_params_defined_fast(&ps, &pi),
            expr_ops::all_level_params_defined(&ps, &pi)
        );
        assert_eq!(
            expr_ops::all_level_params_defined_fast(&Vec::new(), &pi),
            expr_ops::all_level_params_defined(&Vec::new(), &pi)
        );
    }
}
