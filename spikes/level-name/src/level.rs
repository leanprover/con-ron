//! Port of the `Level` part of `ConLeche/Kernel/Expr.lean` (lines 40-139) and
//! of `ConLeche/Kernel/Level.lean`, function by function, in source order.
//!
//! Conventions, as in `name.rs`: `Level`s are `Rc` trees with the
//! `@[computed_field] hashData` stored in the node; arguments come in by
//! shared reference and results go out owned; Lean's `List` becomes `Vec`
//! walked by an index (DESIGN.md §3.3, §3.4 — no loops).
//!
//! `leqCore`'s `diff : Int` becomes `i64`: it only ever moves by one per
//! `succ` peeled off a level, so overflow means a pathological input and, in
//! the Aeneas model, a `fail` — harmless for the accept direction.

use crate::name;
use crate::name::Name;
use std::rc::Rc;

/// ConLeche/Kernel/Expr.lean:40 — `inductive Level`.
pub enum LevelKind {
    Zero,
    Succ(Level),
    Max(Level, Level),
    Imax(Level, Level),
    Param(Name),
}

/// The heap node of a `Level`: the cached hash
/// (ConLeche/Kernel/Expr.lean:48) beside the constructor data.
pub struct LevelNode {
    pub hash: u64,
    pub kind: LevelKind,
}

/// ConLeche/Kernel/Expr.lean:40 — a universe level.
pub struct Level(pub Rc<LevelNode>);

/// ConLeche/Kernel/Expr.lean:48 — the cached hash, an `O(1)` field read.
pub fn hash_data(u: &Level) -> u64 {
    u.0.hash
}

/// ConLeche/Kernel/Expr.lean:49 — `Level.zero`, hash `1`.
pub fn zero() -> Level {
    Level(Rc::new(LevelNode { hash: 1, kind: LevelKind::Zero }))
}

/// ConLeche/Kernel/Expr.lean:50 — `Level.succ`, hash `mixHash 3 u.hashData`.
pub fn succ(u: Level) -> Level {
    let h: u64 = name::mix_hash(3, hash_data(&u));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Succ(u) }))
}

/// ConLeche/Kernel/Expr.lean:51 — `Level.max`,
/// hash `mixHash 5 (mixHash u.hashData v.hashData)`.
pub fn max(u: Level, v: Level) -> Level {
    let h: u64 = name::mix_hash(5, name::mix_hash(hash_data(&u), hash_data(&v)));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Max(u, v) }))
}

/// ConLeche/Kernel/Expr.lean:52 — `Level.imax`,
/// hash `mixHash 7 (mixHash u.hashData v.hashData)`.
pub fn imax(u: Level, v: Level) -> Level {
    let h: u64 = name::mix_hash(7, name::mix_hash(hash_data(&u), hash_data(&v)));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Imax(u, v) }))
}

/// ConLeche/Kernel/Expr.lean:53 — `Level.param`, hash `mixHash 11 (hash n)`.
pub fn param(n: Name) -> Level {
    let h: u64 = name::mix_hash(11, name::hash_data(&n));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Param(n) }))
}

/// Share a level (the `Rc` bump that Lean's value semantics hides).
pub fn dup(u: &Level) -> Level {
    Level(Rc::clone(&u.0))
}

/// The pointer test behind `withPtrEq` (ConLeche/Kernel/Expr.lean:65).
pub fn ptr_eq(a: &Level, b: &Level) -> bool {
    Rc::ptr_eq(&a.0, &b.0)
}

/// ConLeche/Kernel/Expr.lean:65 — `Level.beqPtr`, the *executed* `Level.beq`
/// (line 79, `@[csimp]`-substituted line 86): pointer, cached hash,
/// structural walk, with the pointer fast path kept at every level.
pub fn beq(a: &Level, b: &Level) -> bool {
    if ptr_eq(a, b) {
        true
    } else if hash_data(a) != hash_data(b) {
        false
    } else {
        match (&a.0.kind, &b.0.kind) {
            (LevelKind::Zero, LevelKind::Zero) => true,
            (LevelKind::Succ(u), LevelKind::Succ(v)) => beq(u, v),
            (LevelKind::Max(u1, v1), LevelKind::Max(u2, v2)) => beq(u1, u2) && beq(v1, v2),
            (LevelKind::Imax(u1, v1), LevelKind::Imax(u2, v2)) => beq(u1, u2) && beq(v1, v2),
            (LevelKind::Param(n), LevelKind::Param(m)) => name::beq(n, m),
            _ => false,
        }
    }
}

/// `l = .zero` as a constructor test.  Lean writes the decidable equality
/// (`Level.lean:69`, `:173`); on an `Rc` tree the constructor test is the
/// same predicate without an allocation.
pub fn is_zero_kind(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => true,
        _ => false,
    }
}

/// `l = .succ .zero` as a constructor test (ConLeche/Kernel/Level.lean:69).
pub fn is_one_kind(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Succ(v) => is_zero_kind(v),
        _ => false,
    }
}

/// ConLeche/Kernel/Expr.lean:118 — `levelHasParam`.
pub fn level_has_param(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Param(_) => true,
        LevelKind::Succ(v) => level_has_param(v),
        LevelKind::Max(a, b) => level_has_param(a) || level_has_param(b),
        LevelKind::Imax(a, b) => level_has_param(a) || level_has_param(b),
    }
}

/// ConLeche/Kernel/Expr.lean:125 — `levelsHaveParam`.
pub fn levels_have_param(us: &Vec<Level>) -> bool {
    levels_have_param_from(us, 0)
}

/// The index recursion behind `levels_have_param` (Lean's list recursion).
pub fn levels_have_param_from(us: &Vec<Level>, i: usize) -> bool {
    if i >= us.len() {
        false
    } else {
        level_has_param(&us[i]) || levels_have_param_from(us, i + 1)
    }
}

/// ConLeche/Kernel/Expr.lean:134 — `levelHash`.
pub fn level_hash(u: &Level) -> u64 {
    hash_data(u)
}

/// ConLeche/Kernel/Expr.lean:137 — `levelsHash`.
pub fn levels_hash(us: &Vec<Level>) -> u64 {
    levels_hash_from(us, 0)
}

/// The index recursion behind `levels_hash`.
pub fn levels_hash_from(us: &Vec<Level>, i: usize) -> u64 {
    if i >= us.len() {
        13
    } else {
        name::mix_hash(level_hash(&us[i]), levels_hash_from(us, i + 1))
    }
}

/// ConLeche/Kernel/Level.lean:28 — `Level.subst`.
pub fn subst(ks: &Vec<Name>, vs: &Vec<Level>, u: &Level) -> Level {
    match &u.0.kind {
        LevelKind::Zero => zero(),
        LevelKind::Succ(l) => succ(subst(ks, vs, l)),
        LevelKind::Max(l, r) => max(subst(ks, vs, l), subst(ks, vs, r)),
        LevelKind::Imax(l, r) => imax(subst(ks, vs, l), subst(ks, vs, r)),
        LevelKind::Param(n) => subst_go(ks, vs, 0, n),
    }
}

/// ConLeche/Kernel/Level.lean:35 — `Level.subst.go`, the parallel walk down
/// the two lists, here by a shared index.
pub fn subst_go(ks: &Vec<Name>, vs: &Vec<Level>, i: usize, n: &Name) -> Level {
    if i >= ks.len() || i >= vs.len() {
        param(name::dup(n))
    } else if name::beq(&ks[i], n) {
        dup(&vs[i])
    } else {
        subst_go(ks, vs, i + 1, n)
    }
}

/// ConLeche/Kernel/Level.lean:40 — `Level.allParamsDefined`.
pub fn all_params_defined(params: &Vec<Name>, u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => true,
        LevelKind::Succ(l) => all_params_defined(params, l),
        LevelKind::Max(l, r) => all_params_defined(params, l) && all_params_defined(params, r),
        LevelKind::Imax(l, r) => all_params_defined(params, l) && all_params_defined(params, r),
        LevelKind::Param(n) => name::contains(params, n),
    }
}

/// ConLeche/Kernel/Level.lean:50 — `Level.isNeverZero`.
pub fn is_never_zero(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Param(_) => false,
        LevelKind::Succ(_) => true,
        LevelKind::Max(l, r) => is_never_zero(l) || is_never_zero(r),
        LevelKind::Imax(_, r) => is_never_zero(r),
    }
}

/// ConLeche/Kernel/Level.lean:58 — `Level.combining`.
pub fn combining(l: &Level, r: &Level) -> Level {
    match (&l.0.kind, &r.0.kind) {
        (LevelKind::Zero, _) => dup(r),
        (_, LevelKind::Zero) => dup(l),
        (LevelKind::Succ(a), LevelKind::Succ(b)) => succ(combining(a, b)),
        _ => max(dup(l), dup(r)),
    }
}

/// ConLeche/Kernel/Level.lean:65 — `Level.simplify`.
pub fn simplify(u: &Level) -> Level {
    match &u.0.kind {
        LevelKind::Zero => zero(),
        LevelKind::Param(n) => param(name::dup(n)),
        LevelKind::Succ(l) => succ(simplify(l)),
        LevelKind::Max(l, r) => combining(&simplify(l), &simplify(r)),
        LevelKind::Imax(l, r) => {
            let ls: Level = simplify(l);
            let rs: Level = simplify(r);
            if is_zero_kind(&ls) || is_one_kind(&ls) {
                rs
            } else {
                match &rs.0.kind {
                    LevelKind::Zero => zero(),
                    LevelKind::Succ(_) => combining(&ls, &rs),
                    _ => imax(dup(&ls), dup(&rs)),
                }
            }
        }
    }
}

/// ConLeche/Kernel/Level.lean:82 — `Level.leqCore`.  Lean's `fuel + 1`
/// pattern is the `fuel == 0` test plus `fuel - 1`.
pub fn leq_core(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    if fuel == 0 {
        None
    } else if is_zero_kind(l) && diff >= 0 {
        Some(true)
    } else if is_zero_kind(r) && diff < 0 {
        Some(false)
    } else {
        rest(fuel - 1, l, r, diff)
    }
}

/// ConLeche/Kernel/Level.lean:91 — `Level.rest`, nanoda's case order.  Rust's
/// `match` is first-match like Lean's, so the arms are in the same order.
pub fn rest(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match (&l.0.kind, &r.0.kind) {
        (LevelKind::Param(a), LevelKind::Param(x)) => Some(name::beq(a, x) && diff >= 0),
        (LevelKind::Param(_), LevelKind::Zero) => Some(false),
        (LevelKind::Zero, LevelKind::Param(_)) => Some(diff >= 0),
        (LevelKind::Succ(s), _) => leq_core(fuel, s, r, diff - 1),
        (_, LevelKind::Succ(s)) => leq_core(fuel, l, s, diff + 1),
        (LevelKind::Max(a, b), _) => match leq_core(fuel, a, r, diff) {
            None => None,
            Some(false) => Some(false),
            Some(true) => leq_core(fuel, b, r, diff),
        },
        (LevelKind::Param(_), LevelKind::Max(x, y)) => match leq_core(fuel, l, x, diff) {
            None => None,
            Some(true) => Some(true),
            Some(false) => leq_core(fuel, l, y, diff),
        },
        (LevelKind::Zero, LevelKind::Max(x, y)) => match leq_core(fuel, l, x, diff) {
            None => None,
            Some(true) => Some(true),
            Some(false) => leq_core(fuel, l, y, diff),
        },
        (LevelKind::Imax(a, b), LevelKind::Imax(x, y)) => {
            if beq(a, x) && beq(b, y) && diff >= 0 {
                Some(true)
            } else {
                imax_rules(fuel, l, r, diff)
            }
        }
        _ => imax_rules(fuel, l, r, diff),
    }
}

/// Is this level `.imax _ (.param _)`?  Lean matches the nested constructor
/// directly; Rust cannot look through the `Rc`, so the pattern becomes this
/// predicate plus a re-destructuring helper below.
pub fn is_imax_param(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(_) => true,
            _ => false,
        },
        _ => false,
    }
}

/// ConLeche/Kernel/Level.lean:112 — `Level.imaxRules`.  The six arms are a
/// cascade because the Lean arms interleave the two sides (`_, .imax _
/// (.param p)` comes *before* `.imax a (.imax x y), _`).
pub fn imax_rules(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    if is_imax_param(l) {
        by_cases_left(fuel, l, r, diff)
    } else if is_imax_param(r) {
        by_cases_right(fuel, l, r, diff)
    } else {
        imax_rules_distrib(fuel, l, r, diff)
    }
}

/// `imaxRules` arm 1: `.imax _ (.param p), _ => byCases fuel p l r diff`.
pub fn by_cases_left(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &l.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(p) => by_cases(fuel, p, l, r, diff),
            _ => None,
        },
        _ => None,
    }
}

/// `imaxRules` arm 2: `_, .imax _ (.param p) => byCases fuel p l r diff`.
pub fn by_cases_right(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &r.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(p) => by_cases(fuel, p, l, r, diff),
            _ => None,
        },
        _ => None,
    }
}

/// `imaxRules` arms 3-7: distribute a nested `max`/`imax` under an `imax`.
pub fn imax_rules_distrib(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &l.0.kind {
        LevelKind::Imax(a, b) => match &b.0.kind {
            LevelKind::Imax(x, y) => {
                let nl: Level = max(imax(dup(a), dup(y)), imax(dup(x), dup(y)));
                leq_core(fuel, &nl, r, diff)
            }
            LevelKind::Max(x, y) => {
                let nl: Level = simplify(&max(imax(dup(a), dup(x)), imax(dup(a), dup(y))));
                leq_core(fuel, &nl, r, diff)
            }
            _ => imax_rules_distrib_right(fuel, l, r, diff),
        },
        _ => imax_rules_distrib_right(fuel, l, r, diff),
    }
}

/// `imaxRules` arms 5-7, on the right-hand side.
pub fn imax_rules_distrib_right(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &r.0.kind {
        LevelKind::Imax(x, y) => match &y.0.kind {
            LevelKind::Imax(j, k) => {
                let nr: Level = max(imax(dup(x), dup(k)), imax(dup(j), dup(k)));
                leq_core(fuel, l, &nr, diff)
            }
            LevelKind::Max(j, k) => {
                let nr: Level = simplify(&max(imax(dup(x), dup(j)), imax(dup(x), dup(k))));
                leq_core(fuel, l, &nr, diff)
            }
            _ => None,
        },
        _ => None,
    }
}

/// ConLeche/Kernel/Level.lean:123 — `Level.byCases`.
pub fn by_cases(fuel: u64, p: &Name, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    let ks: Vec<Name> = name::singleton(p);
    let vz: Vec<Level> = singleton(zero());
    let l0: Level = simplify(&subst(&ks, &vz, l));
    let r0: Level = simplify(&subst(&ks, &vz, r));
    match leq_core(fuel, &l0, &r0, diff) {
        None => None,
        Some(false) => Some(false),
        Some(true) => {
            let vp: Vec<Level> = singleton(succ(param(name::dup(p))));
            let ls: Level = simplify(&subst(&ks, &vp, l));
            let rs: Level = simplify(&subst(&ks, &vp, r));
            leq_core(fuel, &ls, &rs, diff)
        }
    }
}

/// A one-element level list (`[.zero]`, `[.succ (.param p)]` in `byCases`).
pub fn singleton(u: Level) -> Vec<Level> {
    let mut v: Vec<Level> = Vec::new();
    v.push(u);
    v
}

/// ConLeche/Kernel/Level.lean:136 — `Level.defaultFuel`.
pub fn default_fuel() -> u64 {
    10000
}

/// ConLeche/Kernel/Level.lean:139 — `Level.leq`.
pub fn leq(l: &Level, r: &Level) -> Option<bool> {
    leq_core(default_fuel(), &simplify(l), &simplify(r), 0)
}

/// ConLeche/Kernel/Level.lean:158 — `Level.isEquiv`.
pub fn is_equiv(l: &Level, r: &Level) -> Option<bool> {
    if beq(l, r) {
        Some(true)
    } else if beq(&simplify(l), &simplify(r)) {
        Some(true)
    } else {
        match leq(l, r) {
            None => None,
            Some(false) => Some(false),
            Some(true) => leq(r, l),
        }
    }
}

/// ConLeche/Kernel/Level.lean:165 — `Level.isEquivList`.
pub fn is_equiv_list(ls: &Vec<Level>, rs: &Vec<Level>) -> Option<bool> {
    is_equiv_list_from(ls, rs, 0)
}

/// The index recursion behind `is_equiv_list`; a length mismatch is `false`.
pub fn is_equiv_list_from(ls: &Vec<Level>, rs: &Vec<Level>, i: usize) -> Option<bool> {
    if i >= ls.len() && i >= rs.len() {
        Some(true)
    } else if i >= ls.len() || i >= rs.len() {
        Some(false)
    } else {
        match is_equiv(&ls[i], &rs[i]) {
            None => None,
            Some(false) => Some(false),
            Some(true) => is_equiv_list_from(ls, rs, i + 1),
        }
    }
}

/// ConLeche/Kernel/Level.lean:173 — `Level.isZero`.
pub fn is_zero(l: &Level) -> bool {
    is_zero_kind(&simplify(l))
}

/// ConLeche/Kernel/Level.lean:178 — `Level.isNonZero`.
pub fn is_non_zero(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Succ(_) => true,
        LevelKind::Max(a, b) => is_non_zero(a) || is_non_zero(b),
        LevelKind::Imax(_, b) => is_non_zero(b),
        LevelKind::Param(_) => false,
    }
}

/* Not ported here: `Level.zeronessOf` (Level.lean:190) and `Level.substPW`
   (:205) need `PropWhen`, and `Expr.instantiateLevelParams` (:234),
   `Expr.allLevelParamsDefined` (:256) and its memoized twin (:300) need
   `Expr` — neither type is in this spike. */

/// ConLeche/Kernel/Level.lean:214 — `Name.nodup`.
pub fn name_nodup(ns: &Vec<Name>) -> bool {
    name_nodup_from(ns, 0)
}

/// The index recursion behind `name_nodup`: Lean tests the *tail*.
pub fn name_nodup_from(ns: &Vec<Name>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if name::contains_from(ns, i + 1, &ns[i]) {
        false
    } else {
        name_nodup_from(ns, i + 1)
    }
}

/// ConLeche/Kernel/Level.lean:219 — `Name.isModelSuffix`, i.e. `.str _
/// "_model"`.  String literals become explicit code-point tests (no loop, no
/// allocation).
pub fn name_is_model_suffix(n: &Name) -> bool {
    match &n.0.kind {
        name::NameKind::Str(_, s) => is_model_str(s),
        _ => false,
    }
}

/// `s == "_model"` on code points.
pub fn is_model_str(s: &Vec<u32>) -> bool {
    s.len() == 6
        && s[0] == 95
        && s[1] == 109
        && s[2] == 111
        && s[3] == 100
        && s[4] == 101
        && s[5] == 108
}

/// `s == "proj"` on code points.
pub fn is_proj_str(s: &Vec<u32>) -> bool {
    s.len() == 4 && s[0] == 112 && s[1] == 114 && s[2] == 111 && s[3] == 106
}

/// `s == "projTable"` on code points.
pub fn is_proj_table_str(s: &Vec<u32>) -> bool {
    s.len() == 9
        && s[0] == 112
        && s[1] == 114
        && s[2] == 111
        && s[3] == 106
        && s[4] == 84
        && s[5] == 97
        && s[6] == 98
        && s[7] == 108
        && s[8] == 101
}

/// ConLeche/Kernel/Level.lean:227 — `Name.isProjFnShape`, i.e.
/// `.num (.str _ "proj") _` or `.num (.str _ "projTable") _`.
pub fn name_is_proj_fn_shape(n: &Name) -> bool {
    match &n.0.kind {
        name::NameKind::Num(p, _) => match &p.0.kind {
            name::NameKind::Str(_, s) => is_proj_str(s) || is_proj_table_str(s),
            _ => false,
        },
        _ => false,
    }
}
