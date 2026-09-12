//! `ConLeche/Frontend/Export.lean` — the representation-free half of the
//! parse: the level-parameter canonicalisation the basis and prelude matching
//! compare up to, the frontend's error type, the taint sentinel and the
//! driver's decline messages.
//!
//! **Only the lockstep twins are ported.**  con-leche spells each comparison
//! twice: `canonEq*`, which builds `ConstantInfo.canon` of BOTH sides, is the
//! SPECIFICATION, and `canonEq*Fast`, which descends the two terms together
//! and stops at the first disagreement, is what `@[csimp]` swaps in and what
//! runs.  The reason is the `tower_*` fixtures: `canonExpr` rebuilds every
//! node, so a depth-60 shared tower (2^60 nodes unshared) exhausts memory in
//! the specification and is a few dozen node visits in the twin.  This module
//! ports the twins and cites both — the spec citation is what the provenance
//! gate watches, the twin is what the port is.
//!
//! `canonLevel` and `canonNameMap` are ported as they stand: a level is a
//! handful of nodes, and `canonExprEqFast`'s `sort`/`const` arms compare
//! *built* canonical levels, so there is nothing to fuse there.
//!
//! **`canonExpr` renames only level parameters** and resets the binder
//! metadata to the same constant on both sides; the name/annotation erasure
//! it also documents has been the identity on both sides since con-leche task
//! #203.  That is why the basis-pin match can pre-filter by NAME (task #215)
//! and why `pw` never enters a comparison.
//!
//! Not ported, deliberately: the six `*_iff` theorems and the four `@[csimp]`
//! lemmas that tie each spec to its twin (§3.1 — a `Prop` is not code), the
//! retired tree-size budget (a `/-! … -/` section, not a declaration), and
//! `M`, which is `Except String` and becomes `Result<_, String>`.

use con_ron_core::kernel::env;
use con_ron_core::kernel::env::{ConstantInfo, ConstantVal, RecRule};
use con_ron_core::kernel::expr;
use con_ron_core::kernel::expr::{Expr, ExprKind};
use con_ron_core::kernel::level;
use con_ron_core::kernel::level::{Level, LevelKind};
use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;

/// con-leche: ConLeche/Frontend/Export.lean:405 M
/// The parse's error monad: a message, which the driver reports with the line
/// number.
pub type M<T> = Result<T, String>;

/// con-leche: ConLeche/Frontend/Export.lean:95-101 canonNameMap
/// The level-parameter renaming a constant's own parameter list induces: the
/// `i`-th parameter becomes `⟨i⟩`, anything else is left alone.  Lean returns
/// the closure `Name → Name`; the port passes the list and the name together,
/// which is the same function applied.
pub fn canon_name_map(ps: &Vec<Name>, n: &Name) -> Name {
    let mut i: u64 = 0;
    for p in ps {
        if name::beq(p, n) {
            return name::mk_num(name::anonymous(), i);
        }
        i += 1;
    }
    name::dup(n)
}

/// con-leche: ConLeche/Frontend/Export.lean:55-62 canonLevel
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

/// con-leche: ConLeche/Frontend/Export.lean:55-62 canonLevel
/// `us.map (canonLevel m)`, the `const` arm's list.
pub fn canon_level_list(ps: &Vec<Name>, ls: &Vec<Level>) -> Vec<Level> {
    ls.iter().map(|l| canon_level(ps, l)).collect()
}

/// con-leche: ConLeche/Frontend/Export.lean:154-174 canonExprEqFast
/// con-leche: ConLeche/Frontend/Export.lean:64-93 canonExpr
/// Lockstep twin of `canonExpr m a == canonExpr m' b`.  `canonExpr` preserves
/// every node's constructor (it rewrites only levels, and resets the binder
/// metadata to the same constant on both sides), so the two canonical forms
/// are equal iff the originals agree constructor by constructor down to their
/// leaves — which is what this descent tests.
pub fn canon_expr_eq_fast(ps: &Vec<Name>, ps2: &Vec<Name>, a: &Expr, b: &Expr) -> bool {
    match (&a.0.kind, &b.0.kind) {
        (ExprKind::Bvar(i), ExprKind::Bvar(j)) => i == j,
        (ExprKind::Fvar(i, t), ExprKind::Fvar(j, t2)) => {
            i == j && canon_expr_eq_fast(ps, ps2, t, t2)
        }
        (ExprKind::Sort(u), ExprKind::Sort(v)) => {
            level::beq(&canon_level(ps, u), &canon_level(ps2, v))
        }
        (ExprKind::Const(n, us), ExprKind::Const(n2, us2)) => {
            name::beq(n, n2)
                && expr::levels_beq(&canon_level_list(ps, us), &canon_level_list(ps2, us2))
        }
        (ExprKind::App(f, x), ExprKind::App(f2, x2)) => {
            canon_expr_eq_fast(ps, ps2, f, f2) && canon_expr_eq_fast(ps, ps2, x, x2)
        }
        (ExprKind::Lam(t, bd, _), ExprKind::Lam(t2, bd2, _)) => {
            canon_expr_eq_fast(ps, ps2, t, t2) && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprKind::ForallE(t, bd, _), ExprKind::ForallE(t2, bd2, _)) => {
            canon_expr_eq_fast(ps, ps2, t, t2) && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprKind::LetE(t, v, bd), ExprKind::LetE(t2, v2, bd2)) => {
            canon_expr_eq_fast(ps, ps2, t, t2)
                && canon_expr_eq_fast(ps, ps2, v, v2)
                && canon_expr_eq_fast(ps, ps2, bd, bd2)
        }
        (ExprKind::Lit(l), ExprKind::Lit(l2)) => expr::literal_beq(l, l2),
        (ExprKind::Proj(s, i, e), ExprKind::Proj(s2, i2, e2)) => {
            name::beq(s, s2) && i == i2 && canon_expr_eq_fast(ps, ps2, e, e2)
        }
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Export.lean:229-234 ConstantVal.canonEqFast
/// con-leche: ConLeche/Frontend/Export.lean:223-227 ConstantVal.canonEq
/// con-leche: ConLeche/Frontend/Export.lean:103-108 ConstantVal.canon
/// Two constants have the same canonical common data.  The numbered
/// level-parameter lists are equal exactly when they are equally long.
pub fn constant_val_canon_eq(cv: &ConstantVal, cv2: &ConstantVal) -> bool {
    name::beq(&cv.name, &cv2.name)
        && cv.level_params.len() == cv2.level_params.len()
        && canon_expr_eq_fast(&cv.level_params, &cv2.level_params, &cv.ty, &cv2.ty)
}

/// con-leche: ConLeche/Frontend/Export.lean:252-259 canonRulesEqFast
/// Rule lists compared through the canonical form of each rule's right-hand
/// side.  `{r with rhs := .bvar 0} == {r' with rhs := .bvar 0}` is every
/// field but `rhs` under Lean's derived equality, which is what the first
/// conjunct below spells out.
pub fn canon_rules_eq_fast(
    ps: &Vec<Name>,
    ps2: &Vec<Name>,
    rs: &Vec<RecRule>,
    rs2: &Vec<RecRule>,
) -> bool {
    if rs.len() != rs2.len() {
        return false;
    }
    for (r, r2) in rs.iter().zip(rs2.iter()) {
        let same_but_rhs = name::beq(&r.ctor, &r2.ctor)
            && r.nfields == r2.nfields
            && r.ctor_params == r2.ctor_params
            && env::rec_rule_fire_beq(&r.fire, &r2.fire)
            && r.k == r2.k
            && r.eta == r2.eta
            && r.params_blind == r2.params_blind;
        if !(same_but_rhs && canon_expr_eq_fast(ps, ps2, &r.rhs, &r2.rhs)) {
            return false;
        }
    }
    true
}

/// con-leche: ConLeche/Frontend/Export.lean:282-301 ConstantInfo.canonEqFast
/// con-leche: ConLeche/Frontend/Export.lean:278-280 ConstantInfo.canonEq
/// con-leche: ConLeche/Frontend/Export.lean:110-125 ConstantInfo.canon
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

/// con-leche: ConLeche/Frontend/Export.lean:322-326 canonEqListFast
/// con-leche: ConLeche/Frontend/Export.lean:317-320 canonEqList
/// Two blocks are the same, member for member, up to the canonical form.
pub fn canon_eq_list(xs: &[ConstantInfo], ys: &[ConstantInfo]) -> bool {
    xs.len() == ys.len()
        && xs
            .iter()
            .zip(ys.iter())
            .all(|(x, y)| constant_info_canon_eq(x, y))
}

/// con-leche: ConLeche/Frontend/Export.lean:347-351 FrontendError
/// Declaration kinds the checker cannot represent yet map to `Unsupported`,
/// which the driver turns into the arena's "declined" exit code — as opposed
/// to malformed input, which is a hard error.  A record that CONTRADICTS
/// ITSELF maps to `Invalid`, the arena's "rejected" code.
#[derive(Debug, Clone)]
pub enum FrontendError {
    ParseError(u64, String),
    Unsupported(String),
    Invalid(String),
}

/// con-leche: ConLeche/Frontend/Export.lean:353-361 RecordVerdict
/// What a declaration record can carry out of the parse when it does not
/// produce a state: a positive DECLINE (a feature the checker does not
/// support) or a REJECT (the record's redundant fields contradict the block's
/// own declarations, which official's replay regenerates and compares).
#[derive(Debug, Clone)]
pub enum RecordVerdict {
    Declined(String),
    Invalid(String),
}

/// con-leche: ConLeche/Frontend/Export.lean:363-366 RecordVerdict.toError
/// The frontend error a record verdict becomes.
pub fn record_verdict_to_error(v: RecordVerdict) -> FrontendError {
    match v {
        RecordVerdict::Declined(what) => FrontendError::Unsupported(what),
        RecordVerdict::Invalid(what) => FrontendError::Invalid(what),
    }
}

/// con-leche: ConLeche/Frontend/Export.lean:368-373 taintSentinel
/// Internal sentinel: a declaration-level expression lookup hit a tainted
/// entry.  Backstop only — `apply_decl_d`'s read-only pre-scan skips tainted
/// declarations before any parsing; if it fires anyway it is converted to a
/// decline at the record level.
pub const TAINT_SENTINEL: &str = "\u{0}uses-skipped-axiom";

/// con-leche: none — `Name.toString`, which DESIGN.md §3.7's skip list keeps
/// out of the verified core as driver-only rendering ("the theorem never
/// reads a message").  The frontend and the CLI *are* the driver, so the
/// rendering lives here: `anonymous` is `[anonymous]`, and a component is
/// appended after a dot.
pub fn name_str(n: &Name) -> String {
    match &n.0.kind {
        con_ron_core::kernel::name::NameKind::Anonymous => "[anonymous]".to_string(),
        con_ron_core::kernel::name::NameKind::Str(p, s) => {
            let tail: String = s.iter().filter_map(|c| char::from_u32(*c)).collect();
            match &p.0.kind {
                con_ron_core::kernel::name::NameKind::Anonymous => tail,
                _ => format!("{}.{}", name_str(p), tail),
            }
        }
        con_ron_core::kernel::name::NameKind::Num(p, k) => match &p.0.kind {
            con_ron_core::kernel::name::NameKind::Anonymous => format!("{}", k),
            _ => format!("{}.{}", name_str(p), k),
        },
    }
}

/// con-leche: ConLeche/Frontend/Export.lean:407-417 taintDetail
/// The taint skips WITHOUT the total: per-root counts and the first few
/// skipped names.  Used where the caller already states the count.
pub fn taint_detail(skips: &[(Name, Name)]) -> String {
    let mut per_root: Vec<String> = Vec::new();
    for r in con_ron_core::kernel::std_axioms::tolerated_axiom_names() {
        let c = skips.iter().filter(|p| name::beq(&p.1, &r)).count();
        if c != 0 {
            per_root.push(format!("{} via {}", c, name_str(&r)));
        }
    }
    let names: Vec<String> = skips.iter().take(8).map(|p| name_str(&p.0)).collect();
    let more = if skips.len() > 8 { ", …" } else { "" };
    format!(
        "{}; first skipped: {}{}",
        per_root.join("; "),
        names.join(", "),
        more
    )
}

/// con-leche: ConLeche/Frontend/Export.lean:419-422 taintSummary
/// Diagnostic summary of the taint skips: total, per-root counts, and the
/// first few skipped names.
pub fn taint_summary(skips: &[(Name, Name)]) -> String {
    format!(
        "skipped {} declarations that use a tolerated axiom ({})",
        skips.len(),
        taint_detail(skips)
    )
}

/// con-leche: none — `prop_when::names_beq` under a name the canon
/// comparisons read as a list equality; re-exported so this module's callers
/// need not reach into the core for it.
pub fn names_beq(a: &Vec<Name>, b: &Vec<Name>) -> bool {
    prop_when::names_beq(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_builder::{bn, cnst, pi, srt};

    fn nm(s: &str) -> Name {
        bn(s.chars().map(|c| c as u32).collect())
    }

    /// `canonNameMap` numbers the constant's own parameters and leaves
    /// anything else alone.
    #[test]
    fn canon_name_map_numbers_own_params() {
        let ps = vec![nm("u"), nm("v")];
        assert!(name::beq(
            &canon_name_map(&ps, &nm("u")),
            &name::mk_num(name::anonymous(), 0)
        ));
        assert!(name::beq(
            &canon_name_map(&ps, &nm("v")),
            &name::mk_num(name::anonymous(), 1)
        ));
        assert!(name::beq(&canon_name_map(&ps, &nm("w")), &nm("w")));
    }

    /// Two constants that differ ONLY in their level-parameter names are the
    /// same declaration up to the canonical form; one that differs in a
    /// constant name is not, and one with a different number of parameters is
    /// not either.
    #[test]
    fn canon_eq_is_level_parameter_renaming() {
        let mk = |p: &str, head: &str| ConstantVal {
            name: nm("T"),
            level_params: vec![nm(p)],
            ty: pi(srt(level::param(nm(p))), cnst(nm(head), vec![])),
        };
        assert!(constant_val_canon_eq(&mk("u", "X"), &mk("w", "X")));
        assert!(!constant_val_canon_eq(&mk("u", "X"), &mk("u", "Y")));
        let two = ConstantVal {
            name: nm("T"),
            level_params: vec![nm("u"), nm("v")],
            ty: pi(srt(level::param(nm("u"))), cnst(nm("X"), vec![])),
        };
        assert!(!constant_val_canon_eq(&mk("u", "X"), &two));
    }

    /// A block matches member for member, and a block of another length does
    /// not.
    #[test]
    fn canon_eq_list_is_member_for_member() {
        let a = ConstantInfo::AxiomInfo(ConstantVal {
            name: nm("A"),
            level_params: vec![nm("u")],
            ty: srt(level::param(nm("u"))),
        });
        let b = ConstantInfo::AxiomInfo(ConstantVal {
            name: nm("A"),
            level_params: vec![nm("x")],
            ty: srt(level::param(nm("x"))),
        });
        let c = ConstantInfo::AxiomInfo(ConstantVal {
            name: nm("B"),
            level_params: Vec::new(),
            ty: srt(level::zero()),
        });
        assert!(canon_eq_list(&[a], &[b]));
        assert!(!canon_eq_list(
            &[ConstantInfo::AxiomInfo(ConstantVal {
                name: nm("A"),
                level_params: vec![nm("u")],
                ty: srt(level::param(nm("u"))),
            })],
            &[c]
        ));
    }
}
