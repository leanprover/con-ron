//! The port's own input validation pass (task #73) — con-ron's certification
//! tax.
//!
//! # What this module is for
//!
//! `Refine/Main.lean`'s capstones used to carry one hypothesis nothing in the
//! proof discharged: `hds : ∀ d ∈ ds.val, DeclCWF d`, "every parsed
//! declaration is well formed".  `DeclCWF` is the task-#5 invariant of
//! DESIGN.md §3.5 — an *inductive* predicate whose constructors are the
//! port's own smart constructors, so it says "every node of this term is what
//! `expr::app`/`name::mk_str`/… built", which pins the stored `data` word to
//! the children.  In con-leche the same fact is true by construction: the
//! `@[computed_field]`s are written by the elaborator and there is no way to
//! forge one.  In the port a `Node`'s fields are `pub`, so a caller *could*
//! hand `check_decls` a term whose word disagrees with its children, and then
//! `expr::beq` is no longer exact and the refinement is false.
//!
//! The maintainer's ruling of 2026-09-13 is that the hypothesis goes away by
//! being **checked**: this pass runs at the entry of
//! `cached::installed::check_decls`, establishes exactly the conjuncts of
//! `DeclCWF` for every declaration in the vector, and declines a malformed one
//! with `CheckError::Native` — the port's own failure, which the full-outcome
//! ruling (DESIGN.md §3, task #67) says claims nothing about con-leche.  A
//! forged term is therefore *rejected*, not assumed away.
//!
//! # Rebuild, do not recompute
//!
//! Every node with a stored derived word is checked by **rebuilding** it: the
//! children are validated first, then the node's own smart constructor is
//! called on them (a `P` bump each — `ron::ptr::clone` — so the children are
//! not copied), and the stored word is compared with the rebuilt node's, as
//! one `u64` equality.  That is the check the proof wants: the rebuilt node's
//! smart-constructor call *is* an equation of the form the `*WF` constructors
//! take, and the word comparison is what turns it into an equation about the
//! node that came in (`Refine/Validate.lean`).  Computing the hash formula
//! here instead would make every soundness lemma name a hash formula, which
//! is precisely what §3.5's inductive shape exists to avoid.
//!
//! `PropWhen` has no stored word and a sealed representation, so it is
//! rebuilt through its public view instead: `to_list_opt` reads the parameter
//! list out (`None` at `never`), the names are validated, `if_all_zero` is the
//! smart constructor applied to them, and `prop_when::beq` — which *is* the
//! representation comparison, `equivR` — says whether the datum that came in
//! is the one the smart constructor builds.  A `Two(q, p)` with `q > p`, or a
//! `Many` list that is not sorted, or a `Many` of length ≤ 2, all fail that
//! comparison, which is right: none of them is reachable from the smart
//! constructors and none of them is well formed.
//!
//! # The visited set, and why a forged word cannot hurt
//!
//! Parsed declarations are DAGs with heavy sharing — the Lean export format
//! shares subterms and the frontend preserves that sharing — so an
//! unmemoised walk of a term is exponential in the DAG's depth.  The `Expr`
//! walk therefore carries a visited set in the exact shape of the `beq` pair
//! memo (DESIGN.md §3.2, `expr::BeqMap`): a `ron::HashMap<u64, Vec<Expr>>`,
//! keyed by the node's stored **hash word** — `expr::hash`, the top 32 bits of
//! the packed `data` word, which is the field `expr::beq_key` mixes — whose
//! buckets hold whole `Expr` handles and whose probe verifies a candidate by
//! **identity** (`ron::ptr::ptr_eq`).
//!
//! **The key is the hash field and not the whole word**, which is a
//! measurement and not a taste: `ron::hashmap::bucket_index` masks the *low*
//! bits of the key, and the low 32 bits of `data` are the two 15-bit range
//! fields and the level-param bit, which are zero for the overwhelming
//! majority of nodes.  Keyed by `data` the whole table lands in a handful of
//! buckets and the pass is quadratic — `Init` does not finish in eleven
//! minutes where the checker itself takes sixty-five seconds (task #73).
//!
//! The key is untrusted here — it is part of the very word the pass is
//! checking — and that costs nothing: a forged word only puts the node in the
//! wrong bucket, so the probe misses and the node is validated the long way.
//! A *hit* is a `ptr_eq` hit, i.e. the bucket holds **this same object**, and
//! only nodes that completed the walk with `true` are ever recorded, so a hit
//! repeats an answer this deterministic pass has already produced for that
//! object.  That is the same argument as `expr::beq_go`'s, for the same
//! reason.  In the model `ptr_eq` is `false` (DESIGN.md §3.2), so the table is
//! written and never read and the model's pass is the plain structural
//! descent — which is what makes `Refine/Validate.lean` an induction on the
//! term and nothing else.
//!
//! `Name` and `Level` walks carry no memo: they are shallow (a name is a few
//! components, a level a few nodes) and the table operations would cost more
//! than the walk.  The set is local to the pass — it goes in and comes back
//! out by value, as `expr::beq_go`'s does and as task #6's accumulator rule
//! says — and is *not* part of `CState`.
//!
//! # What is established, conjunct by conjunct
//!
//! `DeclCWF` (`Refine/CheckerDecl.lean`) over `ConstantValWF` /
//! `ConstantInfosWF` (`Refine/Abs.lean`), hereditarily:
//!
//! | predicate | what this pass checks |
//! |---|---|
//! | `NameWF` | every node rebuilt through `name::anonymous`/`mk_str`/`mk_num` |
//! | `StrWF` | every stored code point is a valid `Char` (`Nat.isValidChar`) |
//! | `LevelWF` | every node rebuilt through `level::zero`/`succ`/`max`/`imax`/`param` |
//! | `PropWhenWF` | the datum is what `never`/`if_all_zero` builds from its own parameter list |
//! | `BinderMetaWF` | its `PropWhen` is |
//! | `Nat::NatWF` | the limb vector is normalised (no trailing zero limb) |
//! | `LiteralWF` | the bignum normalised, the string's code points valid |
//! | `LevelsWF` / `NamesWF` / `ExprsWF` | every entry |
//! | `ExprWF` | every node rebuilt through one of the ten smart constructors |
//! | `ConstantValWF` | the name, the level-parameter list and the type |
//! | `RecRuleFireWF` / `RecRuleWF` / `RecRulesWF` | `.nested`'s two lists; the constructor name, the firing mode and the right-hand side |
//! | `IndCapsWF` | the η constructor's name and the result-sort datum |
//! | `ProjTableWF` | the two names, the level parameters, the structure sort, the bodies and the guards |
//! | `ConstantInfoWF` / `ConstantInfosWF` | one arm per constructor, in the cited field order |
//! | `DeclCWF` | one arm per constructor; `.BasisDecl` is `True` |
//!
//! The records of `kernel::env` carry no derived data of their own
//! (`Refine/Abs.lean`'s note), so their clauses are the conjunction of their
//! fields' and there is nothing to rebuild at that layer.
//!
//! # Cost
//!
//! Measured in DESIGN.md's task #73 section: a few percent of the checker's
//! instructions on `Init` and on the `Init+Std+Lean` export.  The pass is
//! `O(distinct nodes)` thanks to the visited set, and its constant is one
//! smart-constructor call — one `P` allocation — per distinct node.

use crate::kernel::env;
use crate::kernel::env::ConstantInfo;
use crate::kernel::env::ConstantVal;
use crate::kernel::env::IndCaps;
use crate::kernel::env::ProjTable;
use crate::kernel::env::RecRule;
use crate::kernel::env::RecRuleFire;
use crate::kernel::expr;
use crate::kernel::expr::BinderMeta;
use crate::kernel::expr::Expr;
use crate::kernel::expr::ExprKind;
use crate::kernel::expr::Literal;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::level::LevelKind;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::name::NameKind;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use crate::cached::parsed_c::DeclC;
use crate::ron::hashmap::HashMap;
use crate::ron::nat;

// ---------------------------------------------------------------------------
// The visited set
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// All the terms recorded under one key — see `Seen`.  A `Vec`, walked by an
/// index like every other list in the port (DESIGN.md §3.4).
pub type SeenBucket = Vec<Expr>;

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The pass's visited set, in the shape of `expr::BeqMap` (task #38): keyed by
/// the node's stored **hash word** (`expr::hash`, see the module note on why
/// not the whole `data` word), **a bucket of terms per key**, each candidate
/// verified on a probe by `ron::ptr::ptr_eq`.  The key is part of the very
/// word under test, so a forged one can only miss its bucket and cost a walk;
/// a hit is an identity hit on a term this pass has already accepted.
pub type Seen = HashMap<u64, SeenBucket>;

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// A fresh, empty visited set.
pub fn seen_new() -> Seen {
    HashMap::new()
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// Does the key's bucket hold *this* term?  The stored handles, tested by
/// identity, are the verification, exactly as `expr::probe_hit`'s stored pairs
/// are.  In the model `ptr_eq` is `false` (DESIGN.md §3.2), so this is `false`
/// at every probe and the table is never read.
pub fn seen_hit(m: &Seen, key: u64, e: &Expr) -> bool {
    match m.get(&key) {
        None => false,
        Some(es) => seen_hit_from(es, 0, e),
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `seen_hit`: the bucket's candidates, each tested
/// by `expr::ptr_eq`.  No loops (DESIGN.md §3.4).
pub fn seen_hit_from(es: &Vec<Expr>, i: usize, e: &Expr) -> bool {
    if i >= es.len() {
        false
    } else if expr::ptr_eq(&es[i], e) {
        true
    } else {
        seen_hit_from(es, i + 1, e)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// Record a term that completed the walk with `true` in its key's bucket.
/// The insert comes first for `expr::beq_record`'s reason: `insert` hands back
/// what the key held, so the common case — a key with no bucket yet — is one
/// table operation.
pub fn seen_record(m: Seen, key: u64, e: &Expr) -> Seen {
    let mut m: Seen = m;
    let mut es: SeenBucket = Vec::new();
    es.push(expr::dup(e));
    let old: Option<SeenBucket> = m.insert(key, es);
    match old {
        None => m,
        Some(v) => seen_extend(m, key, v, e),
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The growing half of the write-back: the key already held `old`, so the
/// bucket becomes `old` with the new term appended.
pub fn seen_extend(m: Seen, key: u64, old: SeenBucket, e: &Expr) -> Seen {
    let mut m: Seen = m;
    let mut es: SeenBucket = old;
    es.push(expr::dup(e));
    m.insert(key, es);
    m
}

// ---------------------------------------------------------------------------
// Strings and bignums
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `Nat.isValidChar` on a stored code point: `StrWF`'s clause, the one
/// conjunct of the `*WF` family that no smart-constructor equation supplies
/// (`Refine/Abs.lean`).  `kernel::pins_decode::is_valid_char` is the same
/// predicate on a `u64`; this is its `u32` spelling, so that the pass casts
/// nothing.
pub fn is_valid_char(c: u32) -> bool {
    if c < 55296 {
        true
    } else {
        c > 57343 && c < 1114112
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `StrWF`: every stored code point is a valid `Char`.
pub fn validate_str(s: &Vec<u32>) -> bool {
    validate_str_from(s, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_str`.  No loops (DESIGN.md §3.4).
pub fn validate_str_from(s: &Vec<u32>, i: usize) -> bool {
    if i >= s.len() {
        true
    } else if is_valid_char(s[i]) {
        validate_str_from(s, i + 1)
    } else {
        false
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ron::nat::Nat`'s invariant (`Refine/Nat.lean`'s `NatWF`/`LimbsWF`): the
/// limb vector has no trailing zero limb.  Nothing else about a bignum is
/// derived data, so this one test is the whole of it.
pub fn validate_nat(n: &nat::Nat) -> bool {
    let k: usize = n.limbs.len();
    if k == 0 {
        true
    } else {
        n.limbs[k - 1] != 0
    }
}

// ---------------------------------------------------------------------------
// Names and levels
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `NameWF`: each node is what `name::anonymous`/`mk_str`/`mk_num` builds from
/// its own children.  Rebuild and compare the stored `hashData` word; the
/// children are `P` bumps, the string the one copy a `Vec` cannot avoid.
/// No memo (the module note): a name is a handful of components.
pub fn validate_name(n: &Name) -> bool {
    match &n.0.kind {
        NameKind::Anonymous => name::hash_data(n) == name::hash_data(&name::anonymous()),
        NameKind::Str(pre, s) => {
            if validate_name(pre) && validate_str(s) {
                name::hash_data(n)
                    == name::hash_data(&name::mk_str(name::dup(pre), expr::str_copy(s)))
            } else {
                false
            }
        }
        NameKind::Num(pre, k) => {
            if validate_name(pre) {
                name::hash_data(n) == name::hash_data(&name::mk_num(name::dup(pre), *k))
            } else {
                false
            }
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `NamesWF`: every entry of a `Vec<Name>`.
pub fn validate_names(ns: &Vec<Name>) -> bool {
    validate_names_from(ns, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_names`.
pub fn validate_names_from(ns: &Vec<Name>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if validate_name(&ns[i]) {
        validate_names_from(ns, i + 1)
    } else {
        false
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `LevelWF`: each node is what `level::zero`/`succ`/`max`/`imax`/`param`
/// builds from its own children.  Rebuild and compare the stored `hashData`
/// word.  No memo (the module note): a level is a handful of nodes.
pub fn validate_level(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => level::hash_data(u) == level::hash_data(&level::zero()),
        LevelKind::Succ(a) => {
            if validate_level(a) {
                level::hash_data(u) == level::hash_data(&level::succ(level::dup(a)))
            } else {
                false
            }
        }
        LevelKind::Max(a, b) => {
            if validate_level(a) && validate_level(b) {
                level::hash_data(u)
                    == level::hash_data(&level::max(level::dup(a), level::dup(b)))
            } else {
                false
            }
        }
        LevelKind::Imax(a, b) => {
            if validate_level(a) && validate_level(b) {
                level::hash_data(u)
                    == level::hash_data(&level::imax(level::dup(a), level::dup(b)))
            } else {
                false
            }
        }
        LevelKind::Param(n) => {
            if validate_name(n) {
                level::hash_data(u) == level::hash_data(&level::param(name::dup(n)))
            } else {
                false
            }
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `LevelsWF`: every entry of a `Vec<Level>`.
pub fn validate_levels(us: &Vec<Level>) -> bool {
    validate_levels_from(us, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_levels`.
pub fn validate_levels_from(us: &Vec<Level>, i: usize) -> bool {
    if i >= us.len() {
        true
    } else if validate_level(&us[i]) {
        validate_levels_from(us, i + 1)
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// The sealed zero-ness datum, literals and binder metadata
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `PropWhenWF`: the datum is what one of its two public smart constructors
/// builds.  `PropWhen`'s representation is sealed (`prop_when`'s `private`
/// mirror of the cited `private inductive`), so the rebuild goes through the
/// public view: `to_list_opt` is `None` exactly at `never`, and otherwise
/// hands out the parameter list, which `if_all_zero` normalises back into a
/// datum.  `prop_when::beq` *is* the representation comparison (`equivR`), so
/// a datum whose representation is not the normal form of its own list — an
/// out-of-order `Two`, a short or unsorted `Many` — fails here, as it must.
pub fn validate_prop_when(pw: &PropWhen) -> bool {
    match prop_when::to_list_opt(pw) {
        None => true,
        Some(ps) => {
            if validate_names(&ps) {
                prop_when::beq(pw, &prop_when::if_all_zero(ps))
            } else {
                false
            }
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `BinderMetaWF`: the binder datum's `PropWhen` is well formed (the record
/// has no other field).
pub fn validate_binder_meta(m: &BinderMeta) -> bool {
    validate_prop_when(&m.pw)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `LiteralWF`: the bignum normalised, the string's code points valid.
pub fn validate_literal(l: &Literal) -> bool {
    match l {
        Literal::NatVal(n) => validate_nat(n),
        Literal::StrVal(s) => validate_str(s),
    }
}

// ---------------------------------------------------------------------------
// Terms
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ExprWF`, memoised by pointer identity: probe the visited set, walk the
/// node if it misses, and record a completed `true`.  The frame around
/// `validate_expr_arm` is fixed, which is what lets `Refine/Validate.lean`
/// peel it once and induct on the term.
pub fn validate_expr(m: Seen, e: &Expr) -> (bool, Seen) {
    let key: u64 = expr::hash(e);
    if seen_hit(&m, key, e) {
        (true, m)
    } else {
        let r: (bool, Seen) = validate_expr_arm(m, e);
        if r.0 {
            (true, seen_record(r.1, key, e))
        } else {
            (false, r.1)
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The ten constructor cases, in `expr::ExprKind`'s order: validate the
/// children, then rebuild the node with its own smart constructor and compare
/// the stored `data` word.  Its own function so that the memo frame above is
/// peeled once, as `expr::beq_arm` is peeled out of `expr::beq_go`.
pub fn validate_expr_arm(m: Seen, e: &Expr) -> (bool, Seen) {
    match &e.0.kind {
        ExprKind::Bvar(i) => (expr::data(e) == expr::data(&expr::bvar(*i)), m),
        ExprKind::Fvar(i, ty) => {
            let r: (bool, Seen) = validate_expr(m, ty);
            if r.0 {
                (
                    expr::data(e) == expr::data(&expr::fvar(*i, expr::dup(ty))),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
        ExprKind::Sort(u) => {
            if validate_level(u) {
                (
                    expr::data(e) == expr::data(&expr::sort(level::dup(u))),
                    m,
                )
            } else {
                (false, m)
            }
        }
        ExprKind::Const(n, us) => {
            if validate_name(n) && validate_levels(us) {
                (
                    expr::data(e)
                        == expr::data(&expr::mk_const(
                            name::dup(n),
                            env::levels_copy(us),
                        )),
                    m,
                )
            } else {
                (false, m)
            }
        }
        ExprKind::App(f, a) => {
            let r: (bool, Seen) = validate_expr2(m, f, a);
            if r.0 {
                (
                    expr::data(e) == expr::data(&expr::app(expr::dup(f), expr::dup(a))),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
        ExprKind::Lam(ty, b, bm) => {
            let r: (bool, Seen) = validate_expr2(m, ty, b);
            if r.0 && validate_binder_meta(bm) {
                (
                    expr::data(e)
                        == expr::data(&expr::lam(
                            expr::dup(ty),
                            expr::dup(b),
                            expr::binder_meta_dup(bm),
                        )),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
        ExprKind::ForallE(ty, b, bm) => {
            let r: (bool, Seen) = validate_expr2(m, ty, b);
            if r.0 && validate_binder_meta(bm) {
                (
                    expr::data(e)
                        == expr::data(&expr::forall_e(
                            expr::dup(ty),
                            expr::dup(b),
                            expr::binder_meta_dup(bm),
                        )),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
        ExprKind::LetE(ty, v, b) => {
            let r: (bool, Seen) = validate_expr3(m, ty, v, b);
            if r.0 {
                (
                    expr::data(e)
                        == expr::data(&expr::let_e(
                            expr::dup(ty),
                            expr::dup(v),
                            expr::dup(b),
                        )),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
        ExprKind::Lit(l) => {
            if validate_literal(l) {
                (
                    expr::data(e) == expr::data(&expr::lit(expr::literal_dup(l))),
                    m,
                )
            } else {
                (false, m)
            }
        }
        ExprKind::Proj(s, i, x) => {
            let r: (bool, Seen) = validate_expr(m, x);
            if r.0 && validate_name(s) {
                (
                    expr::data(e)
                        == expr::data(&expr::proj(name::dup(s), *i, expr::dup(x))),
                    r.1,
                )
            } else {
                (false, r.1)
            }
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// Two subterms in sequence, threading the visited set — the shape of
/// `expr::beq_both`, and for the same reason: Aeneas cannot join the two
/// branches of an `if` inside an arm when one of them consumes the table.
pub fn validate_expr2(m: Seen, a: &Expr, b: &Expr) -> (bool, Seen) {
    let r: (bool, Seen) = validate_expr(m, a);
    if r.0 {
        validate_expr(r.1, b)
    } else {
        (false, r.1)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// Three subterms in sequence (`.letE`).
pub fn validate_expr3(m: Seen, a: &Expr, b: &Expr, c: &Expr) -> (bool, Seen) {
    let r: (bool, Seen) = validate_expr2(m, a, b);
    if r.0 {
        validate_expr(r.1, c)
    } else {
        (false, r.1)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ExprsWF`: every entry of a `Vec<Expr>`.
pub fn validate_exprs(m: Seen, es: &Vec<Expr>) -> (bool, Seen) {
    validate_exprs_from(m, es, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_exprs`.
pub fn validate_exprs_from(m: Seen, es: &Vec<Expr>, i: usize) -> (bool, Seen) {
    if i >= es.len() {
        (true, m)
    } else {
        let r: (bool, Seen) = validate_expr(m, &es[i]);
        if r.0 {
            validate_exprs_from(r.1, es, i + 1)
        } else {
            (false, r.1)
        }
    }
}

// ---------------------------------------------------------------------------
// The stored-constant records (`kernel::env`)
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ConstantValWF`: the name, the level-parameter list and the type.
pub fn validate_constant_val(m: Seen, cv: &ConstantVal) -> (bool, Seen) {
    if validate_name(&cv.name) && validate_names(&cv.level_params) {
        validate_expr(m, &cv.ty)
    } else {
        (false, m)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `RecRuleFireWF`: `.nested`'s stored level and term lists; the other two
/// arms carry nothing.
pub fn validate_rec_rule_fire(m: Seen, f: &RecRuleFire) -> (bool, Seen) {
    match f {
        RecRuleFire::Inert => (true, m),
        RecRuleFire::Plain => (true, m),
        RecRuleFire::Nested(us, es) => {
            if validate_levels(us) {
                validate_exprs(m, es)
            } else {
                (false, m)
            }
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `RecRuleWF`: the constructor name, the firing mode and the right-hand side
/// (the five counters and bits are machine words).
pub fn validate_rec_rule(m: Seen, r: &RecRule) -> (bool, Seen) {
    if validate_name(&r.ctor) {
        let q: (bool, Seen) = validate_rec_rule_fire(m, &r.fire);
        if q.0 {
            validate_expr(q.1, &r.rhs)
        } else {
            (false, q.1)
        }
    } else {
        (false, m)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `RecRulesWF`: every entry of a `Vec<RecRule>`.
pub fn validate_rec_rules(m: Seen, rs: &Vec<RecRule>) -> (bool, Seen) {
    validate_rec_rules_from(m, rs, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_rec_rules`.
pub fn validate_rec_rules_from(m: Seen, rs: &Vec<RecRule>, i: usize) -> (bool, Seen) {
    if i >= rs.len() {
        (true, m)
    } else {
        let r: (bool, Seen) = validate_rec_rule(m, &rs[i]);
        if r.0 {
            validate_rec_rules_from(r.1, rs, i + 1)
        } else {
            (false, r.1)
        }
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `IndCapsWF`: the η constructor's name and the result-sort zero-ness datum.
pub fn validate_ind_caps(c: &IndCaps) -> bool {
    validate_name(&c.eta_ctor) && validate_prop_when(&c.sort_z)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ProjTableWF`: every stored name, the structure's sort, the field bodies
/// and the per-field guard levels.
pub fn validate_proj_table(m: Seen, t: &ProjTable) -> (bool, Seen) {
    if validate_name(&t.struct_name)
        && validate_names(&t.level_params)
        && validate_name(&t.ctor)
        && validate_level(&t.struct_sort)
        && validate_levels(&t.guards)
    {
        validate_exprs(m, &t.bodies)
    } else {
        (false, m)
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ConstantInfoWF`: one arm per constructor, in the cited field order.
pub fn validate_constant_info(m: Seen, c: &ConstantInfo) -> (bool, Seen) {
    match c {
        ConstantInfo::AxiomInfo(cv) => validate_constant_val(m, cv),
        ConstantInfo::DefnInfo(cv, v, _) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_expr(r.1, v)
            } else {
                (false, r.1)
            }
        }
        ConstantInfo::ThmInfo(cv, v) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_expr(r.1, v)
            } else {
                (false, r.1)
            }
        }
        ConstantInfo::IndInfo(cv, caps) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                (validate_ind_caps(caps), r.1)
            } else {
                (false, r.1)
            }
        }
        ConstantInfo::CtorInfo(cv, _, _) => validate_constant_val(m, cv),
        ConstantInfo::RecInfo(cv, _, _, rs) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_rec_rules(r.1, rs)
            } else {
                (false, r.1)
            }
        }
        ConstantInfo::ProjInfo(t) => validate_proj_table(m, t),
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `ConstantInfosWF`: every entry of a `Vec<ConstantInfo>`.
pub fn validate_constant_infos(m: Seen, cs: &Vec<ConstantInfo>) -> (bool, Seen) {
    validate_constant_infos_from(m, cs, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_constant_infos`.
pub fn validate_constant_infos_from(
    m: Seen,
    cs: &Vec<ConstantInfo>,
    i: usize,
) -> (bool, Seen) {
    if i >= cs.len() {
        (true, m)
    } else {
        let r: (bool, Seen) = validate_constant_info(m, &cs[i]);
        if r.0 {
            validate_constant_infos_from(r.1, cs, i + 1)
        } else {
            (false, r.1)
        }
    }
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// `DeclCWF`: one arm per constructor of `cached::parsed_c::DeclC`.
/// `.BasisDecl` carries a `BasisKind`, which is a machine word — its clause is
/// `True`.
pub fn validate_decl(m: Seen, d: &DeclC) -> (bool, Seen) {
    match d {
        DeclC::AxiomDecl(cv) => validate_constant_val(m, cv),
        DeclC::DefnDecl(cv, v, _) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_expr(r.1, v)
            } else {
                (false, r.1)
            }
        }
        DeclC::ThmDecl(cv, v) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_expr(r.1, v)
            } else {
                (false, r.1)
            }
        }
        DeclC::OpaqueDecl(cv, v) => {
            let r: (bool, Seen) = validate_constant_val(m, cv);
            if r.0 {
                validate_expr(r.1, v)
            } else {
                (false, r.1)
            }
        }
        DeclC::BasisDecl(_) => (true, m),
        DeclC::IndDecl(block, _) => validate_constant_infos(m, block),
    }
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The pass: every declaration of the vector `check_decls` was handed.
pub fn validate_decls(m: Seen, ds: &Vec<DeclC>) -> (bool, Seen) {
    validate_decls_from(m, ds, 0)
}

/// con-leche: none — task #73, the port's own input check (con-leche's computed fields are correct by construction)
/// The index recursion behind `validate_decls`.  The visited set is threaded
/// across declarations, which is what makes the pass linear in the *stream's*
/// distinct nodes rather than in each declaration's.
pub fn validate_decls_from(m: Seen, ds: &Vec<DeclC>, i: usize) -> (bool, Seen) {
    if i >= ds.len() {
        (true, m)
    } else {
        let r: (bool, Seen) = validate_decl(m, &ds[i]);
        if r.0 {
            validate_decls_from(r.1, ds, i + 1)
        } else {
            (false, r.1)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::kernel::expr::ExprKind;
    use crate::kernel::expr::ExprNode;
    use crate::kernel::level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::kernel::prop_when;
    use crate::kernel::validate;
    use crate::ron::nat;
    use crate::ron::ptr;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    #[test]
    fn well_formed_terms_validate() {
        let e = expr::app(
            expr::mk_const(nm("f"), vec![level::zero()]),
            expr::lam(
                expr::sort(level::succ(level::zero())),
                expr::bvar(0),
                expr::binder_meta(prop_when::never()),
            ),
        );
        assert!(validate::validate_expr(validate::seen_new(), &e).0);
        let l = expr::lit(expr::literal_nat(nat::from_u64(7)));
        assert!(validate::validate_expr(validate::seen_new(), &l).0);
        let s = expr::lit(expr::literal_str(vec![104, 105]));
        assert!(validate::validate_expr(validate::seen_new(), &s).0);
        let p = expr::proj(nm("S"), 0, expr::bvar(1));
        assert!(validate::validate_expr(validate::seen_new(), &p).0);
    }

    #[test]
    fn a_forged_data_word_is_rejected() {
        // The very node `expr::app` builds, with one bit flipped in the
        // stored word: the fields are `pub`, so nothing but this pass stands
        // between a forged node and `expr::beq`.
        let good = expr::app(expr::bvar(0), expr::bvar(1));
        let forged = Expr(ptr::new(ExprNode {
            data: expr::data(&good) ^ 1,
            kind: ExprKind::App(expr::bvar(0), expr::bvar(1)),
        }));
        assert!(validate::validate_expr(validate::seen_new(), &good).0);
        assert!(!validate::validate_expr(validate::seen_new(), &forged).0);
    }

    #[test]
    fn a_forged_name_hash_is_rejected() {
        let good = nm("x");
        let forged = Name(ptr::new(name::NameNode {
            hash: name::hash_data(&good) ^ 1,
            kind: name::NameKind::Str(name::anonymous(), vec![120]),
        }));
        assert!(validate::validate_name(&good));
        assert!(!validate::validate_name(&forged));
    }

    #[test]
    fn an_invalid_code_point_is_rejected() {
        // A surrogate is not a `Char`, and `StrWF` is what makes `absString`
        // injective.
        assert!(validate::validate_str(&vec![104, 105]));
        assert!(!validate::validate_str(&vec![104, 0xD800]));
    }

    #[test]
    fn a_denormalised_bignum_is_rejected() {
        assert!(validate::validate_nat(&nat::from_u64(3)));
        assert!(!validate::validate_nat(&nat::Nat { limbs: vec![3, 0] }));
    }

    #[test]
    fn the_visited_set_is_shared_across_declarations() {
        // The same handle twice: the second walk is a probe hit, so the pass
        // is linear in the DAG and not in the tree.
        let shared = expr::app(expr::bvar(0), expr::bvar(1));
        let e = expr::app(expr::dup(&shared), expr::dup(&shared));
        let r = validate::validate_expr(validate::seen_new(), &e);
        assert!(r.0);
        assert!(validate::seen_hit(&r.1, expr::hash(&shared), &shared));
    }
}
