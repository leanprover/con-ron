//! `ConLeche/Kernel/Canon.lean` — the level-parameter canonical form the
//! pinned basis blocks are matched up to, and the lockstep comparisons built
//! on it.
//!
//! **Why this is in the verified core.**  Lean's exporter picks binder names,
//! binder annotations and level-parameter names freely, so a stream's `Nat`
//! block is the pinned one only *up to* renaming level parameters and erasing
//! binder metadata.  `canon` is that renaming.  Until con-leche task #293 the
//! matching was the parser's, and this family lived in
//! `ConLeche/Frontend/Export.lean` beside it (and, in the port, in the
//! unverified `con-ron` crate's `frontend::export`).  Task #293 moved the
//! recognition into the fold: the decoder emits the file's records and
//! nothing else, and it is `check_decl` that recognises a block as one of the
//! five pinned basis blocks (`basis_raw::basis_pin_hit`) and a `#QUOT` record
//! — or the `Quot.sound` axiom record — as the pinned quotient package's
//! (`basis_raw::quot_pin_hit`).  The comparison is therefore part of the
//! verdict, and belongs where the verdict is computed.
//!
//! **Only the lockstep twins are ported.**  con-leche spells each comparison
//! twice: `canonEq*`, which builds `ConstantInfo.canon` of BOTH sides, is the
//! SPECIFICATION, and `canonEq*Fast`, which descends the two terms together
//! and stops at the first disagreement, is what `@[csimp]` swaps in and what
//! runs.  The port carries the twins and cites both — the spec citation
//! beside the twin's, as the port does elsewhere; the `*_iff` theorems and
//! the `@[csimp]` lemmas that tie each pair together are `Prop`s, not code
//! (DESIGN.md §3.1), and are not ported.
//!
//! **Two performance invariants that must not be lost.**
//!
//! 1. *The `Fast` twins descend both sides together.*  `canonExpr` rebuilds
//!    every node, so building the canonical form of the STREAM side unshares
//!    its DAG: `vendor/con-leche/tests/e2e/tower_quot.ndjson` is a depth-60
//!    shared tower — `2^60` nodes unshared — and the specification exhausts
//!    memory on it.  Descending in lockstep, wherever the two sides agree
//!    they have the PIN's shape, so the walk is bounded by the pin's tree
//!    size (a few dozen nodes) however large the stream side, and where they
//!    disagree it stops there.  Same verdict on every input; only the work
//!    changes.  Nothing here may be rewritten to build a `canon` of the
//!    stream side.
//! 2. *The name pre-filter runs first.*  `basis_raw::basis_pin_hit` selects
//!    its candidate pin by comparing member NAMES before any canonical
//!    comparison happens (con-leche task #215): `canon` renames only level
//!    parameters and leaves every constant name alone, so a block can match a
//!    pin only when its members' names are the pin's, member for member, and
//!    that test is a handful of `Name` comparisons.  A block that is not one
//!    of the five must never reach `canon_eq_list`.
//!
//! `canon_level` and `canon_name_map` are ported as they stand: a level is a
//! handful of nodes, and `canon_expr_eq_fast`'s `sort`/`const` arms compare
//! *built* canonical levels, so there is nothing to fuse there.
//!
//! **`canonExpr` renames only level parameters** and resets the binder
//! metadata to the same constant on both sides; the name/annotation erasure
//! it also documents has been the identity on both sides since con-leche task
//! #203.  That is why the basis-pin match can pre-filter by NAME and why `pw`
//! never enters a comparison.

use crate::kernel::env;
use crate::kernel::env::{ConstantInfo, ConstantVal, RecRule};
use crate::kernel::expr;
use crate::kernel::expr::{Expr, ExprView};
use crate::kernel::level;
use crate::kernel::level::{Level, LevelKind};
use crate::kernel::name;
use crate::kernel::name::Name;

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// The level-parameter renaming a constant's own parameter list induces: the
/// `i`-th parameter becomes `⟨i⟩`, anything else is left alone.  Lean returns
/// the closure `Name → Name`; the port passes the list and the name together,
/// which is the same function applied (§3.4 forbids closures).
pub fn canon_name_map(ps: &Vec<Name>, n: &Name) -> Name {
    canon_name_map_from(ps, n, 0)
}

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// The index recursion behind `canon_name_map`, standing for the cited
/// `ps.findIdx? (fun p => p == n)` (§3.4 forbids closures and loops).
pub fn canon_name_map_from(ps: &Vec<Name>, n: &Name, i: usize) -> Name {
    if i >= ps.len() {
        name::dup(n)
    } else if name::beq(&ps[i], n) {
        name::mk_num(name::anonymous(), i as u64)
    } else {
        canon_name_map_from(ps, n, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel
/// Rename level parameters (for basis-block matching up to level-parameter
/// names).
pub fn canon_level(ps: &Vec<Name>, l: &Level) -> Level {
    match &l.0.kind {
        LevelKind::Zero => level::zero(),
        LevelKind::Succ(u) => level::succ(canon_level(ps, u)),
        LevelKind::Max(u, v) => level::max(canon_level(ps, u), canon_level(ps, v)),
        LevelKind::Imax(u, v) => level::imax(canon_level(ps, u), canon_level(ps, v)),
        LevelKind::Param(n) => level::param(canon_name_map(ps, n)),
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel
/// `us.map (canonLevel m)`, the `const` arm's list.
pub fn canon_level_list(ps: &Vec<Name>, ls: &Vec<Level>) -> Vec<Level> {
    canon_level_list_from(ps, ls, 0, Vec::new())
}

/// con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel
/// The index recursion behind `canon_level_list`'s `List.map` (§3.4 forbids
/// closures and loops); the accumulator is passed by value and returned.
pub fn canon_level_list_from(
    ps: &Vec<Name>,
    ls: &Vec<Level>,
    i: usize,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= ls.len() {
        out
    } else {
        let mut out = out;
        out.push(canon_level(ps, &ls[i]));
        canon_level_list_from(ps, ls, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// con-leche: ConLeche/Kernel/Canon.lean:36-65 canonExpr
/// Lockstep twin of `canonExpr m a == canonExpr m' b`.  `canonExpr` preserves
/// every node's constructor (it rewrites only levels, and resets the binder
/// metadata to the same constant on both sides), so the two canonical forms
/// are equal iff the originals agree constructor by constructor down to their
/// leaves — which is what this descent tests.  It must stay a descent: see
/// the module note's invariant 1.
pub fn canon_expr_eq_fast(ps: &Vec<Name>, ps2: &Vec<Name>, a: &Expr, b: &Expr) -> bool {
    match (expr::view(&a), expr::view(&b)) {
        (ExprView::Bvar(i), ExprView::Bvar(j)) => i == j,
        (ExprView::Fvar(i, t), ExprView::Fvar(j, t2)) => {
            i == j && canon_expr_eq_fast(ps, ps2, t, t2)
        }
        (ExprView::Sort(u), ExprView::Sort(v)) => {
            level::beq(&canon_level(ps, u), &canon_level(ps2, v))
        }
        (ExprView::Const(n, us), ExprView::Const(n2, us2)) => {
            name::beq(n, n2)
                && expr::levels_beq(&canon_level_list(ps, us), &canon_level_list(ps2, us2))
        }
        (ExprView::App(f, x), ExprView::App(f2, x2)) => {
            canon_expr_eq_fast(ps, ps2, f, f2) && canon_expr_eq_fast(ps, ps2, x, x2)
        }
        (ExprView::Lam(t, bd, _), ExprView::Lam(t2, bd2, _)) => {
            canon_expr_eq_fast(ps, ps2, t, t2) && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprView::ForallE(t, bd, _), ExprView::ForallE(t2, bd2, _)) => {
            canon_expr_eq_fast(ps, ps2, t, t2) && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprView::LetE(t, v, bd), ExprView::LetE(t2, v2, bd2)) => {
            canon_expr_eq_fast(ps, ps2, t, t2)
                && canon_expr_eq_fast(ps, ps2, v, v2)
                && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprView::Lit(l), ExprView::Lit(l2)) => expr::literal_beq(l, l2),
        (ExprView::Proj(s, i, e), ExprView::Proj(s2, i2, e2)) => {
            name::beq(s, s2) && i == i2 && canon_expr_eq_fast(ps, ps2, e, e2)
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:201-206 ConstantVal.canonEqFast
/// con-leche: ConLeche/Kernel/Canon.lean:195-199 ConstantVal.canonEq
/// con-leche: ConLeche/Kernel/Canon.lean:75-80 ConstantVal.canon
/// Two constants have the same canonical common data.  The numbered
/// level-parameter lists are equal exactly when they are equally long.
pub fn constant_val_canon_eq(cv: &ConstantVal, cv2: &ConstantVal) -> bool {
    name::beq(&cv.name, &cv2.name)
        && cv.level_params.len() == cv2.level_params.len()
        && canon_expr_eq_fast(&cv.level_params, &cv2.level_params, &cv.ty, &cv2.ty)
}

/// con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast
/// Rule lists compared through the canonical form of each rule's right-hand
/// side.  `{r with rhs := .bvar 0} == {r' with rhs := .bvar 0}` is every
/// field but `rhs` under Lean's derived equality, which is what
/// `rec_rule_eq_but_rhs` below spells out.
pub fn canon_rules_eq_fast(
    ps: &Vec<Name>,
    ps2: &Vec<Name>,
    rs: &Vec<RecRule>,
    rs2: &Vec<RecRule>,
) -> bool {
    canon_rules_eq_fast_from(ps, ps2, rs, rs2, 0)
}

/// con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast
/// The index recursion the cited `List` recursion becomes (§3.4 forbids
/// loops); the two `_, _ => false` arms are the length mismatch.
pub fn canon_rules_eq_fast_from(
    ps: &Vec<Name>,
    ps2: &Vec<Name>,
    rs: &Vec<RecRule>,
    rs2: &Vec<RecRule>,
    i: usize,
) -> bool {
    if i >= rs.len() && i >= rs2.len() {
        true
    } else if i >= rs.len() || i >= rs2.len() {
        false
    } else if rec_rule_eq_but_rhs(&rs[i], &rs2[i])
        && canon_expr_eq_fast(ps, ps2, &rs[i].rhs, &rs2[i].rhs)
    {
        canon_rules_eq_fast_from(ps, ps2, rs, rs2, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast
/// `{r with rhs := .bvar 0} == {r' with rhs := .bvar 0}`: the derived `RecRule`
/// equality with the right-hand sides forced to the same term, i.e. every
/// field but `rhs`.
pub fn rec_rule_eq_but_rhs(r: &RecRule, r2: &RecRule) -> bool {
    name::beq(&r.ctor, &r2.ctor)
        && r.nfields == r2.nfields
        && r.ctor_params == r2.ctor_params
        && env::rec_rule_fire_beq(&r.fire, &r2.fire)
        && r.k == r2.k
        && r.eta == r2.eta
        && r.params_blind == r2.params_blind
}

/// con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
/// con-leche: ConLeche/Kernel/Canon.lean:250-252 ConstantInfo.canonEq
/// con-leche: ConLeche/Kernel/Canon.lean:82-97 ConstantInfo.canon
/// Two stored constants have the same canonical form.  `indInfo`'s `IndCaps`
/// is reset on both sides by `canon`, so it is not compared; a `projInfo`
/// never occurs in parsed input and the arm keeps the match total.
pub fn constant_info_canon_eq(ci: &ConstantInfo, ci2: &ConstantInfo) -> bool {
    match (ci, ci2) {
        (ConstantInfo::AxiomInfo(cv), ConstantInfo::AxiomInfo(cv2)) => {
            constant_val_canon_eq(cv, cv2)
        }
        (ConstantInfo::DefnInfo(cv, v, h), ConstantInfo::DefnInfo(cv2, v2, h2)) => {
            constant_val_canon_eq(cv, cv2)
                && canon_expr_eq_fast(&cv.level_params, &cv2.level_params, v, v2)
                && env::reducibility_hint_beq(h, h2)
        }
        (ConstantInfo::ThmInfo(cv, v), ConstantInfo::ThmInfo(cv2, v2)) => {
            constant_val_canon_eq(cv, cv2)
                && canon_expr_eq_fast(&cv.level_params, &cv2.level_params, v, v2)
        }
        (ConstantInfo::IndInfo(cv, _), ConstantInfo::IndInfo(cv2, _)) => {
            constant_val_canon_eq(cv, cv2)
        }
        (ConstantInfo::CtorInfo(cv, np, nf), ConstantInfo::CtorInfo(cv2, np2, nf2)) => {
            constant_val_canon_eq(cv, cv2) && np == np2 && nf == nf2
        }
        (ConstantInfo::RecInfo(cv, mi, rp, rs), ConstantInfo::RecInfo(cv2, mi2, rp2, rs2)) => {
            constant_val_canon_eq(cv, cv2)
                && mi == mi2
                && rp == rp2
                && canon_rules_eq_fast(&cv.level_params, &cv2.level_params, rs, rs2)
        }
        (ConstantInfo::ProjInfo(t), ConstantInfo::ProjInfo(t2)) => env::proj_table_beq(t, t2),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:294-298 canonEqListFast
/// con-leche: ConLeche/Kernel/Canon.lean:289-292 canonEqList
/// Two blocks are the same, member for member, up to the canonical form.
pub fn canon_eq_list(xs: &[ConstantInfo], ys: &[ConstantInfo]) -> bool {
    canon_eq_list_from(xs, ys, 0)
}

/// con-leche: ConLeche/Kernel/Canon.lean:294-298 canonEqListFast
/// The index recursion the cited `List` recursion becomes (§3.4 forbids
/// loops); the two `_, _ => false` arms are the length mismatch.
pub fn canon_eq_list_from(xs: &[ConstantInfo], ys: &[ConstantInfo], i: usize) -> bool {
    if i >= xs.len() && i >= ys.len() {
        true
    } else if i >= xs.len() || i >= ys.len() {
        false
    } else if constant_info_canon_eq(&xs[i], &ys[i]) {
        canon_eq_list_from(xs, ys, i + 1)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::basis_builder::{bn, cnst, pi, srt};

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    /// The whole point: two constants that differ only in the NAMES of their
    /// level parameters are canonically equal, and two that differ in the
    /// parameters' ORDER are not.
    #[test]
    fn canon_eq_is_up_to_level_parameter_names() {
        let a = ConstantVal {
            name: nm("C"),
            level_params: vec![nm("u"), nm("v")],
            ty: pi(srt(level::param(nm("u"))), srt(level::param(nm("v")))),
        };
        let b = ConstantVal {
            name: nm("C"),
            level_params: vec![nm("x"), nm("y")],
            ty: pi(srt(level::param(nm("x"))), srt(level::param(nm("y")))),
        };
        let c = ConstantVal {
            name: nm("C"),
            level_params: vec![nm("x"), nm("y")],
            ty: pi(srt(level::param(nm("y"))), srt(level::param(nm("x")))),
        };
        assert!(constant_val_canon_eq(&a, &b));
        assert!(!constant_val_canon_eq(&a, &c));
    }

    /// `canon` renames level parameters and nothing else: a constant NAME is
    /// left alone, which is what the pin match's name pre-filter relies on.
    #[test]
    fn canon_eq_keeps_constant_names() {
        let ty = cnst(nm("Nat"), vec![]);
        let a = ConstantVal {
            name: nm("A"),
            level_params: vec![],
            ty: expr::dup(&ty),
        };
        let b = ConstantVal {
            name: nm("B"),
            level_params: vec![],
            ty,
        };
        assert!(!constant_val_canon_eq(&a, &b));
    }

    /// The list twin is length-sensitive in both directions.
    #[test]
    fn canon_eq_list_compares_member_for_member() {
        let cv = ConstantVal {
            name: nm("A"),
            level_params: vec![],
            ty: srt(level::zero()),
        };
        let one = vec![ConstantInfo::AxiomInfo(env::constant_val_dup(&cv))];
        let two = vec![
            ConstantInfo::AxiomInfo(env::constant_val_dup(&cv)),
            ConstantInfo::AxiomInfo(cv),
        ];
        assert!(canon_eq_list(&one, &one));
        assert!(!canon_eq_list(&one, &two));
        assert!(!canon_eq_list(&two, &one));
        assert!(canon_eq_list(&[], &[]));
    }
}
