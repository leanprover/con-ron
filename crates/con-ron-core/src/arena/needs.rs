//! `arena::needs` — **what a record reads**.
//!
//! The Rust twin of `proof/ConRon/Arena/Needs.lean`, which is con-leche's
//! `Cached/Needs.lean`: the names a term, a constant's laws and a projection
//! table read, as one memoised walk of each expression's DAG (`needs_go`).
//! Its reader is the solution's justification (`arena::justify`): the cone
//! walk follows these names from an axiom's type through everything they
//! read.
//!
//! **The walk's state** (con-leche's `NeedsSt`) is the pair of the compound
//! nodes walked (`seen`, keyed by the handle: hash-consing makes the handle the
//! node) and the names so far (`acc`), threaded through every call by value.
//! The walk recurses once per level of the expression with the core's walk
//! fuel, as `inductives::struct_parts::mentions_const_go`; a walk that runs
//! out is an internal error, never a verdict.

use crate::arena::core::{
    bool_false_name, bool_name, bool_true_name, lit_guard_names, nat_beq_name, nat_ble_name,
    nat_div_mod_names, nat_op_deps, nat_op_names, CORE_WALK_FUEL,
};
use crate::arena::env::{
    i_constant_info_name, i_constant_info_to_constant_val, nidx_vec_contains, IConstantInfo,
    IProjTable, IRecRule, IRecRuleFire,
};
use crate::arena::handle::{EIdx, NIdx};
use crate::arena::inductives::struct_parts::mc_probe;
use crate::arena::monad::{fail, view, AState};
use crate::arena::store::{ENodeView, PersTier};
use crate::arena::trust_axioms::{reduce_elem_name, reduce_op_names};
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr::Literal;
use crate::ron::hashmap::{Dup, Eq2};
use crate::ron::hashmap2::HashMap2 as HashMap;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `"fuel exhausted: needsGo"`, as code points.
pub const M_FUEL_NEEDS: [u32; 23] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 110, 101, 101,
    100, 115, 71, 111,
];

/// con-leche: ConLeche/Cached/Needs.lean:71-72 NeedsSt
/// Lean twin: `proof/ConRon/Arena/Needs.lean:24-28 NeedsSt` — the walk's state through
/// several expressions: the compound nodes walked, and the names so far.
pub struct NeedsSt {
    pub seen: HashMap<EIdx, bool>,
    pub acc: Vec<NIdx>,
}

/// con-leche: ConLeche/Cached/Needs.lean:71-72 NeedsSt
/// Lean twin: `proof/ConRon/Arena/Needs.lean:30-32 NeedsSt.empty` — the state of a
/// fresh walk, con-leche's `({}, #[])`.
pub fn needs_st_empty() -> NeedsSt {
    NeedsSt {
        seen: HashMap::new(),
        acc: Vec::new(),
    }
}

/// con-leche: none — `acc ++ ns.drop i` over name-handle lists
/// Lean twin: `proof/ConRon/Arena/Needs.lean:34-37 nidxAppend` — the names of `ns`
/// from cursor `i` to `stop`, pushed onto `acc` in order.
pub fn nidx_append(acc: Vec<NIdx>, ns: &Vec<NIdx>, i: usize, stop: usize) -> Vec<NIdx> {
    if i >= stop || i >= ns.len() {
        acc
    } else {
        let mut acc = acc;
        acc.push(ns[i].dup2());
        nidx_append(acc, ns, i + 1, stop)
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:24-29 litNeeds
/// Lean twin: `proof/ConRon/Arena/Needs.lean:39-46 litNeeds` — **the names a literal
/// reads**, pushed onto `acc`: the `Nat` basis, and for a string the
/// string-support constants.  They are the literal guards' ten names, in the
/// cited order (`core::lit_guard_names`): a numeral's are the first three.
pub fn lit_needs(st: &AState, l: &Literal, acc: Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    match lit_guard_names(st) {
        Err(e) => Err(e),
        Ok(ns) => match l {
            Literal::NatVal(_) => Ok(nidx_append(acc, &ns, 0, 3)),
            Literal::StrVal(_) => {
                let k: usize = ns.len();
                Ok(nidx_append(acc, &ns, 0, k))
            }
        },
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo
/// con-leche: ConLeche/Cached/Needs.lean:31-40 _root_.ConLeche.Expr.needs
/// Lean twin: `proof/ConRon/Arena/Needs.lean:48-84 needsGo` — **`Expr.needs`, one
/// memoised walk of the DAG**: `seen` the compound nodes walked, `acc` the
/// names so far.  A node is recorded after its children.  The fuel bounds the
/// depth.
pub fn needs_go(
    pers: &PersTier,
    st: &mut AState,
    seen: HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    fuel: u64,
    h: &EIdx,
) -> Result<(HashMap<EIdx, bool>, Vec<NIdx>), CheckError> {
    if fuel == 0 {
        fail(CheckError::Internal(code_points(&M_FUEL_NEEDS)))
    } else {
        match view(pers, st, h) {
            Err(e) => Err(e),
            Ok(ENodeView::BVar(_)) => Ok((seen, acc)),
            Ok(ENodeView::Sort(_)) => Ok((seen, acc)),
            Ok(ENodeView::Lit(l)) => match lit_needs(st, &l, acc) {
                Err(e) => Err(e),
                Ok(acc2) => Ok((seen, acc2)),
            },
            Ok(ENodeView::Const(n, _)) => {
                let mut acc = acc;
                acc.push(n);
                Ok((seen, acc))
            }
            Ok(v) => match mc_probe(&seen, h) {
                Some(_) => Ok((seen, acc)),
                None => match needs_node(pers, st, seen, acc, fuel - 1, v) {
                    Err(e) => Err(e),
                    Ok((s, a)) => {
                        let mut s2: HashMap<EIdx, bool> = s;
                        s2.insert(h.dup2(), true);
                        Ok((s2, a))
                    }
                },
            },
        }
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:42-69 needsGo
/// Lean twin: `proof/ConRon/Arena/Needs.lean:48-84 needsGo` — the walk's compound
/// arms, split off so that the `view`'s loans are dead at the memo's join
/// (extraction rule 5).
pub fn needs_node(
    pers: &PersTier,
    st: &mut AState,
    seen: HashMap<EIdx, bool>,
    acc: Vec<NIdx>,
    fuel: u64,
    v: ENodeView,
) -> Result<(HashMap<EIdx, bool>, Vec<NIdx>), CheckError> {
    match v {
        ENodeView::FVar(_, ty) => needs_go(pers, st, seen, acc, fuel, &ty),
        ENodeView::App(f, a) => match needs_go(pers, st, seen, acc, fuel, &f) {
            Err(e) => Err(e),
            Ok((s, c)) => needs_go(pers, st, s, c, fuel, &a),
        },
        ENodeView::Lam(ty, body) => match needs_go(pers, st, seen, acc, fuel, &ty) {
            Err(e) => Err(e),
            Ok((s, c)) => needs_go(pers, st, s, c, fuel, &body),
        },
        ENodeView::ForallE(ty, body) => match needs_go(pers, st, seen, acc, fuel, &ty) {
            Err(e) => Err(e),
            Ok((s, c)) => needs_go(pers, st, s, c, fuel, &body),
        },
        ENodeView::LetE(ty, val, body) => match needs_go(pers, st, seen, acc, fuel, &ty) {
            Err(e) => Err(e),
            Ok((s, c)) => match needs_go(pers, st, s, c, fuel, &val) {
                Err(e) => Err(e),
                Ok((s2, c2)) => needs_go(pers, st, s2, c2, fuel, &body),
            },
        },
        ENodeView::Proj(s, _, sub) => {
            let mut acc = acc;
            acc.push(s);
            needs_go(pers, st, seen, acc, fuel, &sub)
        }
        _ => Ok((seen, acc)),
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:74-75 NeedsSt.expr
/// Lean twin: `proof/ConRon/Arena/Needs.lean:86-89 NeedsSt.expr` — one more
/// expression's names.
pub fn needs_expr(pers: &PersTier, st: &mut AState, x: NeedsSt, e: &EIdx) -> Result<NeedsSt, CheckError> {
    match needs_go(pers, st, x.seen, x.acc, CORE_WALK_FUEL, e) {
        Err(er) => Err(er),
        Ok((seen, acc)) => Ok(NeedsSt { seen, acc }),
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names
/// Lean twin: `proof/ConRon/Arena/Needs.lean:91-93 NeedsSt.names` — some names.
pub fn needs_names(x: NeedsSt, ns: &Vec<NIdx>) -> NeedsSt {
    let k: usize = ns.len();
    NeedsSt {
        seen: x.seen,
        acc: nidx_append(x.acc, ns, 0, k),
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:77-78 NeedsSt.names
/// Lean twin: `proof/ConRon/Arena/Needs.lean:95-98 NeedsSt.name` — one name,
/// con-leche's `x.names [n]`.
pub fn needs_name(x: NeedsSt, n: &NIdx) -> NeedsSt {
    let mut acc = x.acc;
    acc.push(n.dup2());
    NeedsSt { seen: x.seen, acc }
}

/// con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule
/// Lean twin: `proof/ConRon/Arena/Needs.lean:100-106 NeedsSt.exprs` — the cited
/// `pins.foldl NeedsSt.expr`, from cursor `i`.
pub fn needs_exprs(
    pers: &PersTier,
    st: &mut AState,
    x: NeedsSt,
    es: &Vec<EIdx>,
    i: usize,
) -> Result<NeedsSt, CheckError> {
    if i >= es.len() {
        Ok(x)
    } else {
        match needs_expr(pers, st, x, &es[i]) {
            Err(e) => Err(e),
            Ok(x2) => needs_exprs(pers, st, x2, es, i + 1),
        }
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:80-85 NeedsSt.rule
/// Lean twin: `proof/ConRon/Arena/Needs.lean:108-115 NeedsSt.rule` — **what a
/// recursor rule reads**: its right-hand side, its constructor, a nested
/// datum's pins.
pub fn needs_rule(pers: &PersTier, st: &mut AState, x: NeedsSt, r: &IRecRule) -> Result<NeedsSt, CheckError> {
    match needs_expr(pers, st, x, &r.rhs) {
        Err(e) => Err(e),
        Ok(x1) => {
            let x2: NeedsSt = needs_name(x1, &r.ctor);
            match &r.fire {
                IRecRuleFire::Nested(_, pins) => needs_exprs(pers, st, x2, pins, 0),
                _ => Ok(x2),
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const
/// Lean twin: `proof/ConRon/Arena/Needs.lean:117-123 NeedsSt.rules` — the cited
/// `rules.foldl NeedsSt.rule`, from cursor `i`.
pub fn needs_rules(
    pers: &PersTier,
    st: &mut AState,
    x: NeedsSt,
    rs: &Vec<IRecRule>,
    i: usize,
) -> Result<NeedsSt, CheckError> {
    if i >= rs.len() {
        Ok(x)
    } else {
        match needs_rule(pers, st, x, &rs[i]) {
            Err(e) => Err(e),
            Ok(x2) => needs_rules(pers, st, x2, rs, i + 1),
        }
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint
/// Lean twin: `proof/ConRon/Arena/Needs.lean:147-156 pinFootprint` — **the names a
/// pinned constant's fast path reads**: a certified `Nat` operation's
/// dependencies and the `Nat` basis (and `Bool` for the comparisons and the
/// division), a compiler-trust operation's element type.
pub fn pin_footprint(st: &mut AState, n: &NIdx) -> Result<Vec<NIdx>, CheckError> {
    match nat_op_names(st) {
        Err(e) => Err(e),
        Ok(ops) => match nat_div_mod_names(st) {
            Err(e) => Err(e),
            Ok(dms) => {
                if nidx_vec_contains(&ops, n) || nidx_vec_contains(&dms, n) {
                    match pin_footprint_nat(st, n, &dms) {
                        Err(e) => Err(e),
                        Ok(xs) => pin_footprint_reduce(st, n, xs),
                    }
                } else {
                    pin_footprint_reduce(st, n, Vec::new())
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint
/// Lean twin: `proof/ConRon/Arena/Needs.lean:147-156 pinFootprint` — the first
/// summand: the operation's dependencies, the `Nat` basis, and `Bool` for
/// `Nat.beq`, `Nat.ble` and the division (`dms`, the cited
/// `natDivModNames`).
pub fn pin_footprint_nat(st: &mut AState, n: &NIdx, dms: &Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    match nat_op_deps(st, n) {
        Err(e) => Err(e),
        Ok(deps) => match lit_guard_names(st) {
            Err(e) => Err(e),
            Ok(lits) => {
                let xs: Vec<NIdx> = nidx_append(deps, &lits, 0, 3);
                match nat_beq_name(st) {
                    Err(e) => Err(e),
                    Ok(be) => match nat_ble_name(st) {
                        Err(e) => Err(e),
                        Ok(bl) => {
                            if n.eq2(&be) || n.eq2(&bl) || nidx_vec_contains(dms, n) {
                                match bool_name(st) {
                                    Err(e) => Err(e),
                                    Ok(b) => match bool_true_name(st) {
                                        Err(e) => Err(e),
                                        Ok(bt) => match bool_false_name(st) {
                                            Err(e) => Err(e),
                                            Ok(bf) => {
                                                let mut xs = xs;
                                                xs.push(b);
                                                xs.push(bt);
                                                xs.push(bf);
                                                Ok(xs)
                                            }
                                        },
                                    },
                                }
                            } else {
                                Ok(xs)
                            }
                        }
                    },
                }
            }
        },
    }
}

/// con-leche: ConLeche/Kernel/Install.lean:106-115 pinFootprint
/// Lean twin: `proof/ConRon/Arena/Needs.lean:147-156 pinFootprint` — the second
/// summand, pushed onto `xs`: a compiler-trust operation's element type.
pub fn pin_footprint_reduce(st: &mut AState, n: &NIdx, xs: Vec<NIdx>) -> Result<Vec<NIdx>, CheckError> {
    match reduce_op_names(st) {
        Err(e) => Err(e),
        Ok(rs) => {
            if nidx_vec_contains(&rs, n) {
                match reduce_elem_name(st, n) {
                    Err(e) => Err(e),
                    Ok(el) => {
                        let mut xs = xs;
                        xs.push(el);
                        Ok(xs)
                    }
                }
            } else {
                Ok(xs)
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:87-95 NeedsSt.const
/// Lean twin: `proof/ConRon/Arena/Needs.lean:158-169 NeedsSt.const` — **what a
/// constant's laws read**: its type, a definition's value, a recursor's rules,
/// a type former's block, and its pin's fast-path names.
pub fn needs_const(
    pers: &PersTier,
    st: &mut AState,
    x: NeedsSt,
    ci: &IConstantInfo,
) -> Result<NeedsSt, CheckError> {
    let cv = i_constant_info_to_constant_val(ci);
    match needs_expr(pers, st, x, &cv.ty) {
        Err(e) => Err(e),
        Ok(x1) => {
            let r: Result<NeedsSt, CheckError> = match ci {
                IConstantInfo::DefnInfo(_, v, _) => needs_expr(pers, st, x1, v),
                IConstantInfo::RecInfo(_, _, _, _, rules) => needs_rules(pers, st, x1, rules, 0),
                IConstantInfo::IndInfo(_, caps) => Ok(needs_names(x1, &caps.all)),
                _ => Ok(x1),
            };
            match r {
                Err(e) => Err(e),
                Ok(x2) => {
                    let n: NIdx = i_constant_info_name(ci);
                    match pin_footprint(st, &n) {
                        Err(e) => Err(e),
                        Ok(fp) => Ok(needs_names(x2, &fp)),
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/Needs.lean:97-99 NeedsSt.table
/// Lean twin: `proof/ConRon/Arena/Needs.lean:171-174 NeedsSt.table` — **what a table
/// reads**: its structure, its constructor, its bodies.
pub fn needs_table(
    pers: &PersTier,
    st: &mut AState,
    x: NeedsSt,
    t: &IProjTable,
) -> Result<NeedsSt, CheckError> {
    let x1: NeedsSt = needs_name(x, &t.struct_name);
    let x2: NeedsSt = needs_name(x1, &t.ctor);
    needs_exprs(pers, st, x2, &t.bodies, 0)
}
