//! `arena::canon` — the level-parameter canonical form, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Canon.lean`, which is con-leche's
//! `Kernel/Canon.lean`: the canonical form a stream's block is matched against
//! a pinned basis block up to, and the lockstep comparisons built on it.
//!
//! ## One function per algorithm: the lockstep one
//!
//! con-leche carries each comparison TWICE — a SPECIFICATION that builds
//! `ConstantInfo.canon` of both sides and compares the results, and a `…Fast`
//! twin that descends both sides together — joined by `@[csimp]`, so the
//! executed comparison is the lockstep one.  The arena has ONE function per
//! algorithm and it is the LOCKSTEP one, so each item below carries a
//! `con-leche:` line per collapsed declaration; `con_ron_core::kernel::canon`
//! made the same collapse for the same reason.
//!
//! ## The renaming is two lists, not a function
//!
//! con-leche's `canonNameMap ps : Name → Name` sends the `i`-th level
//! parameter to `.num .anonymous i`.  Over handles "building a name" means
//! INTERNING one, so the map cannot be computed on demand — and DESIGN.md §3.4
//! forbids the function value anyway.  The numbered names are interned ONCE by
//! `canon_names`, and the renaming is the pure two-list lookup
//! `canon_name_map ps cs n`.  One `cs` serves both sides of every comparison,
//! because each comparison tests the two parameter lists for equal LENGTH
//! before it looks at a term and `canon_names` depends on the length alone.

use crate::arena::core::CORE_WALK_FUEL;
use crate::arena::env::{
    IConstantInfo, IConstantVal, IIndCaps, IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use crate::arena::monad::{fail, intern_n_node, view, view_l, view_ls, AState};
use crate::arena::store::{ENodeView, LNodeView, NNodeView};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env as cenv;
use crate::kernel::expr;
use crate::kernel::prop_when;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

// ---------------------------------------------------------------------------
// The messages of this module's declines
// ---------------------------------------------------------------------------

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: canonLevelEq"`, as code points.
pub const M_FUEL_CANON_LEVEL: [u32; 28] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 97,
    110, 111, 110, 76, 101, 118, 101, 108, 69, 113
];

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: canonExprEq"`, as code points.
pub const M_FUEL_CANON_EXPR: [u32; 27] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 99, 97,
    110, 111, 110, 69, 120, 112, 114, 69, 113
];

// ---------------------------------------------------------------------------
// The renaming (`Canon.lean:46-73` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// Lean twin: `proof/ConRon/Arena/Canon.lean:48-59 canonNamesGo` — the `n`
/// numbered names `⟨0⟩ … ⟨n-1⟩` the canonical form renames a constant's level
/// parameters to, interned.  The counter runs UP so the list comes out in
/// index order; no fuel, because the recursion is structural on the count.
pub fn canon_names_go(
    pers: &PersTier,
    st: &mut AState,
    i: u64,
    n: u64,
    out: Vec<NIdx>,
) -> Result<Vec<NIdx>, CheckError> {
    if n == 0 {
        Ok(out)
    } else {
        match intern_n_node(pers, st, NNodeView::Anonymous) {
            Err(e) => Err(e),
            Ok(a) => match intern_n_node(pers, st, NNodeView::Num(a, i)) {
                Err(e) => Err(e),
                Ok(h) => {
                    let mut out2 = out;
                    out2.push(h);
                    canon_names_go(pers, st, i + 1, n - 1, out2)
                }
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// Lean twin: `proof/ConRon/Arena/Canon.lean:61-63 canonNames` — the numbered
/// names for a level-parameter list of length `n`.
pub fn canon_names(pers: &PersTier, st: &mut AState, n: u64) -> Result<Vec<NIdx>, CheckError> {
    canon_names_go(pers, st, 0, n, Vec::new())
}

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// Lean twin: `proof/ConRon/Arena/Canon.lean:65-73 canonNameMap` — the
/// renaming a constant's own parameter list induces: the `i`-th parameter
/// becomes the `i`-th numbered name, anything else is left alone.  PURE (the
/// numerals are interned already) and a function of two lists rather than a
/// function VALUE (DESIGN.md §3.4).
pub fn canon_name_map(ps: &Vec<NIdx>, cs: &Vec<NIdx>, n: &NIdx) -> NIdx {
    canon_name_map_from(ps, cs, n, 0)
}

/// con-leche: ConLeche/Kernel/Canon.lean:67-73 canonNameMap
/// The cited `ps.findIdx?` as an index recursion (DESIGN.md §3.4 forbids the
/// closure), with the `cs.getD i n` fall-through of a short `cs` inlined.
pub fn canon_name_map_from(ps: &Vec<NIdx>, cs: &Vec<NIdx>, n: &NIdx, i: usize) -> NIdx {
    if i >= ps.len() {
        n.dup2()
    } else if ps[i].eq2(n) {
        if i < cs.len() {
            cs[i].dup2()
        } else {
            n.dup2()
        }
    } else {
        canon_name_map_from(ps, cs, n, i + 1)
    }
}

// ---------------------------------------------------------------------------
// Levels (`Canon.lean:75-117` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Canon.lean:27-34 canonLevel
/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:77-99 canonLevelEq` —
/// `canonLevel ps u == canonLevel ps' v`, decided in lockstep on the two level
/// handles.  `canonLevel` preserves every node's constructor (it rewrites only
/// the `.param` leaf), so the two canonical forms are equal iff the originals
/// agree constructor by constructor down to their leaves.
pub fn canon_level_eq(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    u: &LIdx,
    v: &LIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CANON_LEVEL)))
    } else {
        match view_l(pers, st, u) {
            Err(e) => Err(e),
            Ok(a) => match view_l(pers, st, v) {
                Err(e) => Err(e),
                Ok(b) => canon_level_eq_at(pers, st, ps, ps2, cs, fuel - 1, a, b),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:77-99 canonLevelEq` — the arms,
/// past the two views.  Split at the twin's own `match` boundary so the views'
/// borrows end before the recursion (task #97-P4c's rule).
pub fn canon_level_eq_at(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    a: LNodeView,
    b: LNodeView,
) -> Result<bool, CheckError> {
    match (a, b) {
        (LNodeView::Zero, LNodeView::Zero) => Ok(true),
        (LNodeView::Succ(x), LNodeView::Succ(y)) => {
            canon_level_eq(pers, st, ps, ps2, cs, fuel, &x, &y)
        }
        (LNodeView::Max(x, y), LNodeView::Max(x2, y2)) => {
            match canon_level_eq(pers, st, ps, ps2, cs, fuel, &x, &x2) {
                Err(e) => Err(e),
                Ok(r) => {
                    if r {
                        canon_level_eq(pers, st, ps, ps2, cs, fuel, &y, &y2)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        (LNodeView::Imax(x, y), LNodeView::Imax(x2, y2)) => {
            match canon_level_eq(pers, st, ps, ps2, cs, fuel, &x, &x2) {
                Err(e) => Err(e),
                Ok(r) => {
                    if r {
                        canon_level_eq(pers, st, ps, ps2, cs, fuel, &y, &y2)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        (LNodeView::Param(n), LNodeView::Param(n2)) => {
            Ok(canon_name_map(ps, cs, &n).eq2(&canon_name_map(ps2, cs, &n2)))
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:101-111 canonLevelListEq` — the
/// `.const` clause's `us.map (canonLevel m) == us'.map (canonLevel m')`, at
/// two universe-argument lists read out of the level-list store.  The cited
/// two-`List` recursion is one cursor.
pub fn canon_level_list_eq(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    us: &Vec<LIdx>,
    vs: &Vec<LIdx>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= us.len() && i >= vs.len() {
        Ok(true)
    } else if i >= us.len() || i >= vs.len() {
        Ok(false)
    } else {
        match canon_level_eq(pers, st, ps, ps2, cs, fuel, &us[i], &vs[i]) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    canon_level_list_eq(pers, st, ps, ps2, cs, fuel, us, vs, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:113-117 canonLevelsEq` — the same
/// at two interned universe-argument LIST handles.
pub fn canon_levels_eq(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    us: &LsIdx,
    vs: &LsIdx,
) -> Result<bool, CheckError> {
    match view_ls(pers, st, us) {
        Err(e) => Err(e),
        Ok(a) => match view_ls(pers, st, vs) {
            Err(e) => Err(e),
            Ok(b) => canon_level_list_eq(pers, st, ps, ps2, cs, fuel, &a, &b, 0),
        },
    }
}

// ---------------------------------------------------------------------------
// Terms (`Canon.lean:119-163` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Canon.lean:36-65 canonExpr
/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:121-163 canonExprEq` — **the
/// agreement for expressions**, in lockstep on two handles.  `canonExpr`
/// preserves every node's constructor (it rewrites only levels, and resets the
/// binder metadata to the same constant on both sides), so the two canonical
/// forms are equal iff the originals agree constructor by constructor down to
/// their leaves.  The binder metadata is NOT compared, exactly as the cited
/// clause does not: `canonExpr` writes `⟨.never⟩` on both sides.
pub fn canon_expr_eq(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_CANON_EXPR)))
    } else {
        match view(pers, st, a) {
            Err(e) => Err(e),
            Ok(va) => match view(pers, st, b) {
                Err(e) => Err(e),
                Ok(vb) => canon_expr_eq_at(pers, st, ps, ps2, cs, fuel - 1, va, vb),
            },
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:121-163 canonExprEq` — the ten
/// arms, past the two views.
pub fn canon_expr_eq_at(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    va: ENodeView,
    vb: ENodeView,
) -> Result<bool, CheckError> {
    match (va, vb) {
        (ENodeView::BVar(i), ENodeView::BVar(j)) => Ok(i == j),
        (ENodeView::FVar(i, t), ENodeView::FVar(j, t2)) => {
            if i == j {
                canon_expr_eq(pers, st, ps, ps2, cs, fuel, &t, &t2)
            } else {
                Ok(false)
            }
        }
        (ENodeView::Sort(u), ENodeView::Sort(v)) => {
            canon_level_eq(pers, st, ps, ps2, cs, fuel, &u, &v)
        }
        (ENodeView::Const(n, us), ENodeView::Const(n2, us2)) => {
            if n.eq2(&n2) {
                canon_levels_eq(pers, st, ps, ps2, cs, fuel, &us, &us2)
            } else {
                Ok(false)
            }
        }
        (ENodeView::App(f, x), ENodeView::App(f2, x2)) => {
            canon_expr_eq_two(pers, st, ps, ps2, cs, fuel, &f, &f2, &x, &x2)
        }
        (ENodeView::Lam(t, bd, _), ENodeView::Lam(t2, bd2, _)) => {
            canon_expr_eq_two(pers, st, ps, ps2, cs, fuel, &t, &t2, &bd, &bd2)
        }
        (ENodeView::ForallE(t, bd, _), ENodeView::ForallE(t2, bd2, _)) => {
            canon_expr_eq_two(pers, st, ps, ps2, cs, fuel, &t, &t2, &bd, &bd2)
        }
        (ENodeView::LetE(t, v, bd), ENodeView::LetE(t2, v2, bd2)) => {
            match canon_expr_eq(pers, st, ps, ps2, cs, fuel, &t, &t2) {
                Err(e) => Err(e),
                Ok(r) => {
                    if r {
                        canon_expr_eq_two(pers, st, ps, ps2, cs, fuel, &v, &v2, &bd, &bd2)
                    } else {
                        Ok(false)
                    }
                }
            }
        }
        (ENodeView::Lit(l), ENodeView::Lit(l2)) => Ok(expr::literal_beq(&l, &l2)),
        (ENodeView::Proj(s, i, e), ENodeView::Proj(s2, i2, e2)) => {
            if s.eq2(&s2) && i == i2 {
                canon_expr_eq(pers, st, ps, ps2, cs, fuel, &e, &e2)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:126-146 canonExprEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:121-163 canonExprEq` — the twin's
/// `if ← canonExprEq … then canonExprEq … else pure false`, which four of its
/// arms spell identically.  One function rather than four copies.
pub fn canon_expr_eq_two(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    a: &EIdx,
    a2: &EIdx,
    b: &EIdx,
    b2: &EIdx,
) -> Result<bool, CheckError> {
    match canon_expr_eq(pers, st, ps, ps2, cs, fuel, a, a2) {
        Err(e) => Err(e),
        Ok(r) => {
            if r {
                canon_expr_eq(pers, st, ps, ps2, cs, fuel, b, b2)
            } else {
                Ok(false)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Constants (`Canon.lean:165-238` of the twin)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Canon.lean:75-80 ConstantVal.canon
/// con-leche: ConLeche/Kernel/Canon.lean:195-199 ConstantVal.canonEq
/// con-leche: ConLeche/Kernel/Canon.lean:201-206 ConstantVal.canonEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:167-178 IConstantVal.canonEq` —
/// two constants have the same canonical common data.  The numbered
/// level-parameter lists are equal exactly when they are equally long, which
/// is why the length test stands in for comparing them — and why ONE
/// `canon_names` serves both sides.
pub fn i_constant_val_canon_eq(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    cv2: &IConstantVal,
) -> Result<bool, CheckError> {
    if cv.name.eq2(&cv2.name) && cv.level_params.len() == cv2.level_params.len() {
        match canon_names(pers, st, cv.level_params.len() as u64) {
            Err(e) => Err(e),
            Ok(cs) => canon_expr_eq(
                pers,
                st,
                &cv.level_params,
                &cv2.level_params,
                &cs,
                CORE_WALK_FUEL,
                &cv.ty,
                &cv2.ty,
            ),
        }
    } else {
        Ok(false)
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:193-237 RecRuleFire
/// Lean twin: `proof/ConRon/Arena/Canon.lean:180-194 canonRulesEq` — the
/// derived `BEq` on a rule's firing mode, which the record comparison below
/// needs and `arena::env` does not carry (it has the copy only).
pub fn i_rec_rule_fire_beq(a: &IRecRuleFire, b: &IRecRuleFire) -> bool {
    match (a, b) {
        (IRecRuleFire::Inert, IRecRuleFire::Inert) => true,
        (IRecRuleFire::Plain, IRecRuleFire::Plain) => true,
        (IRecRuleFire::Nested(l1, p1), IRecRuleFire::Nested(l2, p2)) => {
            lidx_vec_beq(l1, l2, 0) && eidx_vec_beq(p1, p2, 0)
        }
        _ => false,
    }
}

/// con-leche: none — handle-list equality; Lean twin: the `==` of `List LIdx`
/// A level-handle list compared elementwise (a handle comparison is word
/// equality, DESIGN.md §8.3).
pub fn lidx_vec_beq(a: &Vec<LIdx>, b: &Vec<LIdx>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if a[i].eq2(&b[i]) {
        lidx_vec_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: none — handle-list equality; Lean twin: the `==` of `List EIdx`
/// An expression-handle list compared elementwise.
pub fn eidx_vec_beq(a: &Vec<EIdx>, b: &Vec<EIdx>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if a[i].eq2(&b[i]) {
        eidx_vec_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: none — handle-list equality; Lean twin: the `==` of `List NIdx`
/// A name-handle list compared elementwise.
pub fn nidx_vec_beq(a: &Vec<NIdx>, b: &Vec<NIdx>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if a[i].eq2(&b[i]) {
        nidx_vec_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:180-194 canonRulesEq` — the
/// twin's `{ r with rhs := default } == { r' with rhs := default }`: every
/// field of the rule but its right-hand side.
pub fn i_rec_rule_eq_but_rhs(r: &IRecRule, r2: &IRecRule) -> bool {
    r.ctor.eq2(&r2.ctor)
        && r.nfields == r2.nfields
        && r.ctor_params == r2.ctor_params
        && i_rec_rule_fire_beq(&r.fire, &r2.fire)
        && r.k == r2.k
        && r.eta == r2.eta
        && r.params_blind == r2.params_blind
}

/// con-leche: ConLeche/Kernel/Canon.lean:224-231 canonRulesEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:180-194 canonRulesEq` — rule
/// lists compared through the canonical form of each rule's right-hand side.
/// The two `_, _ => false` arms of the twin are the length mismatch.
pub fn canon_rules_eq(
    pers: &PersTier,
    st: &AState,
    ps: &Vec<NIdx>,
    ps2: &Vec<NIdx>,
    cs: &Vec<NIdx>,
    fuel: u64,
    rs: &Vec<IRecRule>,
    rs2: &Vec<IRecRule>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= rs.len() && i >= rs2.len() {
        Ok(true)
    } else if i >= rs.len() || i >= rs2.len() {
        Ok(false)
    } else if !i_rec_rule_eq_but_rhs(&rs[i], &rs2[i]) {
        Ok(false)
    } else {
        match canon_expr_eq(pers, st, ps, ps2, cs, fuel, &rs[i].rhs, &rs2[i].rhs) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    canon_rules_eq(pers, st, ps, ps2, cs, fuel, rs, rs2, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:376-431 ProjTable
/// Lean twin: `proof/ConRon/Arena/Canon.lean:196-228 IConstantInfo.canonEq` —
/// the `t == t'` of the `.projInfo` arm, field by field.  `canon` is the
/// identity on a projection table (one never occurs in parsed input).
pub fn i_proj_table_beq(t: &IProjTable, t2: &IProjTable) -> bool {
    t.struct_name.eq2(&t2.struct_name)
        && t.table_name.eq2(&t2.table_name)
        && nidx_vec_beq(&t.level_params, &t2.level_params, 0)
        && t.num_params == t2.num_params
        && t.ctor.eq2(&t2.ctor)
        && t.num_fields == t2.num_fields
        && t.struct_sort.eq2(&t2.struct_sort)
        && eidx_vec_beq(&t.bodies, &t2.bodies, 0)
        && lidx_vec_beq(&t.guards, &t2.guards, 0)
        && t.off == t2.off
}

/// con-leche: ConLeche/Kernel/Canon.lean:82-97 ConstantInfo.canon
/// con-leche: ConLeche/Kernel/Canon.lean:250-252 ConstantInfo.canonEq
/// con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:196-228 IConstantInfo.canonEq` —
/// two stored constants have the same canonical form.  `.indInfo`'s
/// capabilities are not compared (`canon` resets both to `{}`), and a
/// projection table is compared as it stands.
pub fn i_constant_info_canon_eq(
    pers: &PersTier,
    st: &mut AState,
    ci: &IConstantInfo,
    ci2: &IConstantInfo,
) -> Result<bool, CheckError> {
    match (ci, ci2) {
        (IConstantInfo::AxiomInfo(cv), IConstantInfo::AxiomInfo(cv2)) => {
            i_constant_val_canon_eq(pers, st, cv, cv2)
        }
        (IConstantInfo::DefnInfo(cv, v, h), IConstantInfo::DefnInfo(cv2, v2, h2)) => {
            if cenv::reducibility_hint_beq(h, h2) {
                canon_eq_cv_and_value(pers, st, cv, cv2, v, v2)
            } else {
                Ok(false)
            }
        }
        (IConstantInfo::ThmInfo(cv, v), IConstantInfo::ThmInfo(cv2, v2)) => {
            canon_eq_cv_and_value(pers, st, cv, cv2, v, v2)
        }
        (IConstantInfo::IndInfo(cv, _), IConstantInfo::IndInfo(cv2, _)) => {
            i_constant_val_canon_eq(pers, st, cv, cv2)
        }
        (IConstantInfo::CtorInfo(cv, np, nf), IConstantInfo::CtorInfo(cv2, np2, nf2)) => {
            if np == np2 && nf == nf2 {
                i_constant_val_canon_eq(pers, st, cv, cv2)
            } else {
                Ok(false)
            }
        }
        (
            IConstantInfo::RecInfo(cv, mi, rp, rs),
            IConstantInfo::RecInfo(cv2, mi2, rp2, rs2),
        ) => {
            if mi == mi2 && rp == rp2 {
                canon_eq_cv_and_rules(pers, st, cv, cv2, rs, rs2)
            } else {
                Ok(false)
            }
        }
        (IConstantInfo::ProjInfo(t), IConstantInfo::ProjInfo(t2)) => {
            Ok(i_proj_table_beq(t, t2))
        }
        _ => Ok(false),
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:196-228 IConstantInfo.canonEq` —
/// the `.defnInfo`/`.thmInfo` arms' shared tail: the common data, then the
/// stored value at the same numbered names.  Split at the twin's own `let cs`
/// boundary, which is where the two arms coincide.
pub fn canon_eq_cv_and_value(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    cv2: &IConstantVal,
    v: &EIdx,
    v2: &EIdx,
) -> Result<bool, CheckError> {
    match i_constant_val_canon_eq(pers, st, cv, cv2) {
        Err(e) => Err(e),
        Ok(r) => {
            if !r {
                Ok(false)
            } else {
                match canon_names(pers, st, cv.level_params.len() as u64) {
                    Err(e) => Err(e),
                    Ok(cs) => canon_expr_eq(
                        pers,
                        st,
                        &cv.level_params,
                        &cv2.level_params,
                        &cs,
                        CORE_WALK_FUEL,
                        v,
                        v2,
                    ),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:254-273 ConstantInfo.canonEqFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:196-228 IConstantInfo.canonEq` —
/// the `.recInfo` arm's tail: the common data, then the rule list.
pub fn canon_eq_cv_and_rules(
    pers: &PersTier,
    st: &mut AState,
    cv: &IConstantVal,
    cv2: &IConstantVal,
    rs: &Vec<IRecRule>,
    rs2: &Vec<IRecRule>,
) -> Result<bool, CheckError> {
    match i_constant_val_canon_eq(pers, st, cv, cv2) {
        Err(e) => Err(e),
        Ok(r) => {
            if !r {
                Ok(false)
            } else {
                match canon_names(pers, st, cv.level_params.len() as u64) {
                    Err(e) => Err(e),
                    Ok(cs) => canon_rules_eq(
                        pers,
                        st,
                        &cv.level_params,
                        &cv2.level_params,
                        &cs,
                        CORE_WALK_FUEL,
                        rs,
                        rs2,
                        0,
                    ),
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Canon.lean:289-292 canonEqList
/// con-leche: ConLeche/Kernel/Canon.lean:294-298 canonEqListFast
/// Lean twin: `proof/ConRon/Arena/Canon.lean:230-237 canonEqList` — two blocks
/// are the same, member for member, up to the canonical form.
pub fn canon_eq_list(
    pers: &PersTier,
    st: &mut AState,
    xs: &Vec<IConstantInfo>,
    ys: &Vec<IConstantInfo>,
    i: usize,
) -> Result<bool, CheckError> {
    if i >= xs.len() && i >= ys.len() {
        Ok(true)
    } else if i >= xs.len() || i >= ys.len() {
        Ok(false)
    } else {
        match i_constant_info_canon_eq(pers, st, &xs[i], &ys[i]) {
            Err(e) => Err(e),
            Ok(r) => {
                if r {
                    canon_eq_list(pers, st, xs, ys, i + 1)
                } else {
                    Ok(false)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// The derived equality on a stored constant
//
// `Arena/DeclCheck.lean` and `Arena/Checker.lean` compare a stored constant
// with a pin by `==` (`fe.find? eqName == some eqA`), which in the twin is the
// `deriving DecidableEq` of `IConstantInfo`.  Rust has no derive (§3.4), so
// the instance is spelled out here, beside `i_proj_table_beq` which it needs.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Env.lean:186-191 ConstantVal
/// Lean twin: `proof/ConRon/Arena/Env.lean:66-72 IConstantVal` — the cited
/// `deriving DecidableEq`, field by field.
pub fn i_constant_val_beq(a: &IConstantVal, b: &IConstantVal) -> bool {
    a.name.eq2(&b.name) && nidx_vec_beq(&a.level_params, &b.level_params, 0) && a.ty.eq2(&b.ty)
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// Lean twin: `proof/ConRon/Arena/Env.lean:85-98 IRecRule` — the cited
/// `deriving DecidableEq`: `i_rec_rule_eq_but_rhs` and the right-hand side.
pub fn i_rec_rule_beq(a: &IRecRule, b: &IRecRule) -> bool {
    i_rec_rule_eq_but_rhs(a, b) && a.rhs.eq2(&b.rhs)
}

/// con-leche: ConLeche/Kernel/Env.lean:239-282 RecRule
/// A rule list compared elementwise.
pub fn i_rec_rules_beq(a: &Vec<IRecRule>, b: &Vec<IRecRule>, i: usize) -> bool {
    if i >= a.len() && i >= b.len() {
        true
    } else if i >= a.len() || i >= b.len() {
        false
    } else if i_rec_rule_beq(&a[i], &b[i]) {
        i_rec_rules_beq(a, b, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Kernel/Env.lean:347-374 IndCaps
/// Lean twin: `proof/ConRon/Arena/Env.lean:109-125 IIndCaps` — the cited
/// `deriving DecidableEq`; `sortZ` goes through `PropWhen`'s own.
pub fn i_ind_caps_beq(a: &IIndCaps, b: &IIndCaps) -> bool {
    a.eta == b.eta
        && a.eta_ctor.eq2(&b.eta_ctor)
        && a.eta_params == b.eta_params
        && a.eta_fields == b.eta_fields
        && a.unitlike == b.unitlike
        && a.unit_params == b.unit_params
        && a.rule_k == b.rule_k
        && prop_when::beq(&a.sort_z, &b.sort_z)
}

/// con-leche: ConLeche/Kernel/Env.lean:460-486 ConstantInfo
/// Lean twin: `proof/ConRon/Arena/Env.lean:173-183 IConstantInfo` — the cited
/// `deriving DecidableEq`, constructor for constructor.  This is the `==` of
/// `fe.find? eqName == some eqA`, the whole-constant comparison the pinned
/// `Eq` and `Nat` bases are recognised by.
pub fn i_constant_info_beq(a: &IConstantInfo, b: &IConstantInfo) -> bool {
    match (a, b) {
        (IConstantInfo::AxiomInfo(x), IConstantInfo::AxiomInfo(y)) => {
            i_constant_val_beq(x, y)
        }
        (IConstantInfo::DefnInfo(x, v, h), IConstantInfo::DefnInfo(y, w, h2)) => {
            i_constant_val_beq(x, y) && v.eq2(w) && cenv::reducibility_hint_beq(h, h2)
        }
        (IConstantInfo::ThmInfo(x, v), IConstantInfo::ThmInfo(y, w)) => {
            i_constant_val_beq(x, y) && v.eq2(w)
        }
        (IConstantInfo::IndInfo(x, c), IConstantInfo::IndInfo(y, d)) => {
            i_constant_val_beq(x, y) && i_ind_caps_beq(c, d)
        }
        (IConstantInfo::CtorInfo(x, p, f), IConstantInfo::CtorInfo(y, q, g)) => {
            i_constant_val_beq(x, y) && p == q && f == g
        }
        (IConstantInfo::RecInfo(x, m, p, rs), IConstantInfo::RecInfo(y, n, q, ss)) => {
            i_constant_val_beq(x, y) && m == n && p == q && i_rec_rules_beq(rs, ss, 0)
        }
        (IConstantInfo::ProjInfo(t), IConstantInfo::ProjInfo(u)) => i_proj_table_beq(t, u),
        _ => false,
    }
}
