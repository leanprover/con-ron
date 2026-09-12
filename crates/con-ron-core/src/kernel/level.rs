//! Port of the `Level` part of `ConLeche/Kernel/Expr.lean` (lines 40-139) and
//! of `ConLeche/Kernel/Level.lean`, function by function, in source order.
//!
//! Brought into the crate at task #9 from `spikes/level-name/src/level.rs`,
//! which stays untouched as task #3's recorded evidence; this copy is the
//! living code, and it additionally carries the `crate::ron::hashmap`
//! dictionaries (`Hashable`, `Eq2`) at the end of the file.
//!
//! Conventions, as in `name.rs`: `Level`s are `Rc` trees with the
//! `@[computed_field] hashData` stored in the node; arguments come in by
//! shared reference and results go out owned; Lean's `List` becomes `Vec`
//! walked by an index (DESIGN.md §3.3, §3.4 — no loops).
//!
//! `leqCore`'s `diff : Int` becomes `i64`: it only ever moves by one per
//! `succ` peeled off a level, so overflow means a pathological input and, in
//! the Aeneas model, a `fail` — harmless for the accept direction.

use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::prop_when;
use crate::kernel::prop_when::PropWhen;
use std::rc::Rc;

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// The five constructors of `inductive Level`; the cached hash sits in
/// `LevelNode` (DESIGN.md §3.2).
pub enum LevelKind {
    Zero,
    Succ(Level),
    Max(Level, Level),
    Imax(Level, Level),
    Param(Name),
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// The heap node of a `Level`: the cited inductive's `@[computed_field]
/// hashData` beside the constructor data.
pub struct LevelNode {
    pub hash: u64,
    pub kind: LevelKind,
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// A universe level, as an `Rc` tree.
pub struct Level(pub Rc<LevelNode>);

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// The cached hash, an `O(1)` field read.
pub fn hash_data(u: &Level) -> u64 {
    u.0.hash
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// `Level.zero`, hash `1`.
pub fn zero() -> Level {
    Level(Rc::new(LevelNode { hash: 1, kind: LevelKind::Zero }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// `Level.succ`, hash `mixHash 3 u.hashData`.
pub fn succ(u: Level) -> Level {
    let h: u64 = name::mix_hash(3, hash_data(&u));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Succ(u) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// `Level.max`, hash `mixHash 5 (mixHash u.hashData v.hashData)`.
pub fn max(u: Level, v: Level) -> Level {
    let h: u64 = name::mix_hash(5, name::mix_hash(hash_data(&u), hash_data(&v)));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Max(u, v) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// `Level.imax`, hash `mixHash 7 (mixHash u.hashData v.hashData)`.
pub fn imax(u: Level, v: Level) -> Level {
    let h: u64 = name::mix_hash(7, name::mix_hash(hash_data(&u), hash_data(&v)));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Imax(u, v) }))
}

/// con-leche: ConLeche/Kernel/Expr.lean:35-54 Level
/// `Level.param`, hash `mixHash 11 (hash n)`.
pub fn param(n: Name) -> Level {
    let h: u64 = name::mix_hash(11, name::hash_data(&n));
    Level(Rc::new(LevelNode { hash: h, kind: LevelKind::Param(n) }))
}

/// con-leche: none — the `Rc` bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a level.
pub fn dup(u: &Level) -> Level {
    Level(Rc::clone(&u.0))
}

/// con-leche: ConLeche/Kernel/Expr.lean:60-67 Level.beqPtr
/// The pointer test behind the cited `withPtrEq`; modeled as `false` in
/// the generated Lean (DESIGN.md §3.2).
pub fn ptr_eq(a: &Level, b: &Level) -> bool {
    Rc::ptr_eq(&a.0, &b.0)
}

/// con-leche: ConLeche/Kernel/Expr.lean:60-67 Level.beqPtr
/// con-leche: ConLeche/Kernel/Expr.lean:76-79 Level.beq
/// `Level.beqPtr` is the *executed* `Level.beq` (`@[csimp]`-substituted):
/// pointer, cached hash, structural walk.  Deviation: the pointer fast
/// path is kept at every level of the descent.
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

/// con-leche: ConLeche/Kernel/Level.lean:64-77 simplify
/// `l = .zero` as a constructor test: Lean writes the decidable equality
/// inline in the cited `imax` arm (and in `isZero`); on an `Rc` tree the
/// constructor test is the same predicate without an allocation.
pub fn is_zero_kind(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:64-77 simplify
/// `l = .succ .zero` as a constructor test, from the same `imax` arm.
pub fn is_one_kind(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Succ(v) => is_zero_kind(v),
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:114-122 levelHasParam
/// con-leche: ConLeche/Kernel/ExprOps.lean:2399-2406 Level.hasParam
/// `levelHasParam`.  The second citation is the same recurrence written as
/// the *spec* function `Level.hasParam` in `ExprOps.lean`; the cited file's
/// `levelHasParam_eq` (`:2524-2527`) is the equation between them, so one
/// Rust function stands for both (task #13).
pub fn level_has_param(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Param(_) => true,
        LevelKind::Succ(v) => level_has_param(v),
        LevelKind::Max(a, b) => level_has_param(a) || level_has_param(b),
        LevelKind::Imax(a, b) => level_has_param(a) || level_has_param(b),
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:124-127 levelsHaveParam
/// `levelsHaveParam`.
pub fn levels_have_param(us: &Vec<Level>) -> bool {
    levels_have_param_from(us, 0)
}

/// con-leche: ConLeche/Kernel/Expr.lean:124-127 levelsHaveParam
/// The index recursion the cited `List` recursion becomes (DESIGN.md §3.3).
pub fn levels_have_param_from(us: &Vec<Level>, i: usize) -> bool {
    if i >= us.len() {
        false
    } else {
        level_has_param(&us[i]) || levels_have_param_from(us, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:129-134 levelHash
/// `levelHash`.
pub fn level_hash(u: &Level) -> u64 {
    hash_data(u)
}

/// con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash
/// `levelsHash`.
pub fn levels_hash(us: &Vec<Level>) -> u64 {
    levels_hash_from(us, 0)
}

/// con-leche: ConLeche/Kernel/Expr.lean:136-139 levelsHash
/// The index recursion the cited `List` recursion becomes.
pub fn levels_hash_from(us: &Vec<Level>, i: usize) -> u64 {
    if i >= us.len() {
        13
    } else {
        name::mix_hash(level_hash(&us[i]), levels_hash_from(us, i + 1))
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst
/// `Level.subst`.
pub fn subst(ks: &Vec<Name>, vs: &Vec<Level>, u: &Level) -> Level {
    match &u.0.kind {
        LevelKind::Zero => zero(),
        LevelKind::Succ(l) => succ(subst(ks, vs, l)),
        LevelKind::Max(l, r) => max(subst(ks, vs, l), subst(ks, vs, r)),
        LevelKind::Imax(l, r) => imax(subst(ks, vs, l), subst(ks, vs, r)),
        LevelKind::Param(n) => subst_go(ks, vs, 0, n),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:26-37 subst.go
/// The cited `where go` clause: the parallel walk down the two lists,
/// here by a shared index.
pub fn subst_go(ks: &Vec<Name>, vs: &Vec<Level>, i: usize, n: &Name) -> Level {
    if i >= ks.len() || i >= vs.len() {
        param(name::dup(n))
    } else if name::beq(&ks[i], n) {
        dup(&vs[i])
    } else {
        subst_go(ks, vs, i + 1, n)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:39-44 allParamsDefined
/// `Level.allParamsDefined`.
pub fn all_params_defined(params: &Vec<Name>, u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => true,
        LevelKind::Succ(l) => all_params_defined(params, l),
        LevelKind::Max(l, r) => all_params_defined(params, l) && all_params_defined(params, r),
        LevelKind::Imax(l, r) => all_params_defined(params, l) && all_params_defined(params, r),
        LevelKind::Param(n) => name::contains(params, n),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:46-55 isNeverZero
/// `Level.isNeverZero`.
pub fn is_never_zero(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Param(_) => false,
        LevelKind::Succ(_) => true,
        LevelKind::Max(l, r) => is_never_zero(l) || is_never_zero(r),
        LevelKind::Imax(_, r) => is_never_zero(r),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:57-62 combining
/// `Level.combining`.
pub fn combining(l: &Level, r: &Level) -> Level {
    match (&l.0.kind, &r.0.kind) {
        (LevelKind::Zero, _) => dup(r),
        (_, LevelKind::Zero) => dup(l),
        (LevelKind::Succ(a), LevelKind::Succ(b)) => succ(combining(a, b)),
        _ => max(dup(l), dup(r)),
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:64-77 simplify
/// `Level.simplify`.
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

/// con-leche: ConLeche/Kernel/Level.lean:81-88 leqCore
/// `Level.leqCore`.  Deviation: Lean's `fuel + 1` pattern is the
/// `fuel == 0` test plus `fuel - 1`, and its `diff : Int` is an `i64`.
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

/// con-leche: ConLeche/Kernel/Level.lean:90-108 rest
/// `Level.rest`, nanoda's case order.  Rust's `match` is first-match like
/// Lean's, so the arms are in the same order.
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

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// Is this level `.imax _ (.param _)`?  Deviation: Lean matches the nested
/// constructor directly; Rust cannot look through the `Rc`, so the cited
/// pattern becomes this predicate plus a re-destructuring helper below.
pub fn is_imax_param(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(_) => true,
            _ => false,
        },
        _ => false,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// `Level.imaxRules`.  Deviation: the six arms are a cascade of four Rust
/// functions because the Lean arms interleave the two sides (`_, .imax _
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

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// Arm 1: `.imax _ (.param p), _ => byCases fuel p l r diff`.
pub fn by_cases_left(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &l.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(p) => by_cases(fuel, p, l, r, diff),
            _ => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// Arm 2: `_, .imax _ (.param p) => byCases fuel p l r diff`.
pub fn by_cases_right(fuel: u64, l: &Level, r: &Level, diff: i64) -> Option<bool> {
    match &r.0.kind {
        LevelKind::Imax(_, b) => match &b.0.kind {
            LevelKind::Param(p) => by_cases(fuel, p, l, r, diff),
            _ => None,
        },
        _ => None,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// Arms 3-7: distribute a nested `max`/`imax` under an `imax`.
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

/// con-leche: ConLeche/Kernel/Level.lean:110-120 imaxRules
/// Arms 5-7, on the right-hand side.
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

/// con-leche: ConLeche/Kernel/Level.lean:122-130 byCases
/// `Level.byCases`.
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

/// con-leche: none — a one-element `Vec` for the `[.zero]` / `[.succ (.param p)]` literals in `byCases`
/// A one-element level list.
pub fn singleton(u: Level) -> Vec<Level> {
    let mut v: Vec<Level> = Vec::new();
    v.push(u);
    v
}

/// con-leche: ConLeche/Kernel/Level.lean:134-136 defaultFuel
/// `Level.defaultFuel`.
pub fn default_fuel() -> u64 {
    10000
}

/// con-leche: ConLeche/Kernel/Level.lean:138-140 leq
/// `Level.leq`.
pub fn leq(l: &Level, r: &Level) -> Option<bool> {
    leq_core(default_fuel(), &simplify(l), &simplify(r), 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:142-161 isEquiv
/// `Level.isEquiv`.
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

/// con-leche: ConLeche/Kernel/Level.lean:163-169 isEquivList
/// `Level.isEquivList`.
pub fn is_equiv_list(ls: &Vec<Level>, rs: &Vec<Level>) -> Option<bool> {
    is_equiv_list_from(ls, rs, 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:163-169 isEquivList
/// The index recursion the cited `List` recursion becomes; a length
/// mismatch is `false`.
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

/// con-leche: ConLeche/Kernel/Level.lean:171-173 isZero
/// `Level.isZero`.
pub fn is_zero(l: &Level) -> bool {
    is_zero_kind(&simplify(l))
}

/// con-leche: ConLeche/Kernel/Level.lean:175-183 isNonZero
/// `Level.isNonZero`.
pub fn is_non_zero(u: &Level) -> bool {
    match &u.0.kind {
        LevelKind::Zero => false,
        LevelKind::Succ(_) => true,
        LevelKind::Max(a, b) => is_non_zero(a) || is_non_zero(b),
        LevelKind::Imax(_, b) => is_non_zero(b),
        LevelKind::Param(_) => false,
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:185-195 zeronessOf
/// `Level.zeronessOf`: the zero-ness datum of a level — a `max` is zero iff
/// both sides are (`inter`), an `imax` iff its right side is.  Filled in at
/// task #13: task #3 deferred it only because `PropWhen` did not exist yet.
pub fn zeroness_of(l: &Level) -> PropWhen {
    match &l.0.kind {
        LevelKind::Zero => prop_when::if_all_zero(Vec::new()),
        LevelKind::Succ(_) => prop_when::never(),
        LevelKind::Param(n) => {
            let mut ps: Vec<Name> = Vec::new();
            ps.push(name::dup(n));
            prop_when::if_all_zero(ps)
        }
        LevelKind::Max(a, b) => prop_when::inter(&zeroness_of(a), &zeroness_of(b)),
        LevelKind::Imax(_, b) => zeroness_of(b),
    }
}

/// con-leche: none — replaces the `fun n => zeronessOf (subst.go ks vs n)` of `substPW`
/// The one-method dictionary that stands for `substPW`'s function argument
/// (task #9's pattern 1; DESIGN.md §3.4 forbids closures).  It captures the
/// two substitution lists by shared reference, which is what Lean's closure
/// captures by value.
pub struct SubstZ<'a> {
    pub ks: &'a Vec<Name>,
    pub vs: &'a Vec<Level>,
}

/// con-leche: none — the `fun n => zeronessOf (subst.go ks vs n)` of `substPW`
/// The cited closure's body.
impl<'a> prop_when::NameToPw for SubstZ<'a> {
    /// con-leche: none — the `fun n => zeronessOf (subst.go ks vs n)` of `substPW`
    fn apply(&self, n: &Name) -> PropWhen {
        zeroness_of(&subst_go(self.ks, self.vs, 0, n))
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:197-207 substPW
/// `Level.substPW`: push a level-parameter substitution through a zero-ness
/// datum.  Canonical on output, because `PropWhen.bindZ` is.  Filled in at
/// task #13 alongside `zeroness_of`; `crate::kernel::expr_ops`'s
/// `instantiate_level_params` is its one caller, as con-leche's
/// `instantiateLevelParams` is.
pub fn subst_pw(ks: &Vec<Name>, vs: &Vec<Level>, pw: &PropWhen) -> PropWhen {
    prop_when::bind_z(&SubstZ { ks: ks, vs: vs }, pw)
}

/* Not ported here: `Expr.instantiateLevelParams` (Level.lean:234) and
   `Expr.allLevelParamsDefined` (:256) with its memoized twin (:300) are
   `Expr` operations spelled in this file for import order; all three are in
   `crate::kernel::expr_ops` (the first at task #13, the other two at task
   #24, where `checkConstantVal` first needed them). */

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// `Name.nodup`.
pub fn name_nodup(ns: &Vec<Name>) -> bool {
    name_nodup_from(ns, 0)
}

/// con-leche: ConLeche/Kernel/Level.lean:213-216 Name.nodup
/// The index recursion the cited `List` recursion becomes: Lean tests the
/// *tail*, so this one starts at `i + 1`.
pub fn name_nodup_from(ns: &Vec<Name>, i: usize) -> bool {
    if i >= ns.len() {
        true
    } else if name::contains_from(ns, i + 1, &ns[i]) {
        false
    } else {
        name_nodup_from(ns, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Level.lean:218-221 Name.isModelSuffix
/// `Name.isModelSuffix`, i.e. `.str _ "_model"`.  Deviation: string
/// literals become explicit code-point tests (no loop, no allocation).
pub fn name_is_model_suffix(n: &Name) -> bool {
    match &n.0.kind {
        name::NameKind::Str(_, s) => is_model_str(s),
        _ => false,
    }
}

/// con-leche: none — the `"_model"` string literal of `Name.isModelSuffix`, spelled out over code points
/// `s == "_model"`.
pub fn is_model_str(s: &Vec<u32>) -> bool {
    s.len() == 6
        && s[0] == 95
        && s[1] == 109
        && s[2] == 111
        && s[3] == 100
        && s[4] == 101
        && s[5] == 108
}

/// con-leche: none — the `"proj"` string literal of `Name.isProjFnShape`
/// `s == "proj"` on code points.
pub fn is_proj_str(s: &Vec<u32>) -> bool {
    s.len() == 4 && s[0] == 112 && s[1] == 114 && s[2] == 111 && s[3] == 106
}

/// con-leche: none — the `"projTable"` string literal of `Name.isProjFnShape`
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

/// con-leche: ConLeche/Kernel/Level.lean:223-230 Name.isProjFnShape
/// `Name.isProjFnShape`, i.e. `.num (.str _ "proj") _` or
/// `.num (.str _ "projTable") _`.
pub fn name_is_proj_fn_shape(n: &Name) -> bool {
    match &n.0.kind {
        name::NameKind::Num(p, _) => match &p.0.kind {
            name::NameKind::Str(_, s) => is_proj_str(s) || is_proj_table_str(s),
            _ => false,
        },
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// The hash-map dictionaries (`crate::ron::hashmap`'s own traits, task #7)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Kernel/Expr.lean:55-57 _
/// The cited `instance : Hashable Level := ⟨Level.hashData⟩`, as the key
/// dictionary of `crate::ron::hashmap` — this is what the `lsimpC`, `lnzC` and
/// `eqvC` memo tables will probe with.
impl Hashable for Level {
    /// con-leche: ConLeche/Kernel/Expr.lean:55-57 _
    /// The stored word, an `O(1)` field read.
    fn hash64(&self) -> u64 {
        hash_data(self)
    }
}

/// con-leche: ConLeche/Kernel/Expr.lean:86 _
/// The cited `instance : BEq Level := ⟨Level.beq⟩`, as the key dictionary of
/// `crate::ron::hashmap`.  Deviation: `Eq2` is our own one-method trait, so the
/// instance is `beq` with its pointer and hash fast paths (DESIGN.md §3.2).
impl Eq2 for Level {
    /// con-leche: ConLeche/Kernel/Expr.lean:76-79 Level.beq
    /// `Level.beq`, i.e. the `@[csimp]`-substituted `Level.beqPtr`.
    fn eq2(&self, other: &Self) -> bool {
        beq(self, other)
    }
}

#[cfg(test)]
mod tests {
    use crate::ron::hashmap::Eq2;
    use crate::ron::hashmap::Hashable;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;

    /// A single `str` component under `anonymous`.
    fn nm(s: &str) -> Name {
        let cs: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cs)
    }

    fn p(s: &str) -> Level {
        level::param(nm(s))
    }

    #[test]
    fn name_num_and_shapes() {
        let projty = name::mk_num(nm("proj"), 3);
        assert!(level::name_is_proj_fn_shape(&projty));
        let tbl = name::mk_num(nm("projTable"), 0);
        assert!(level::name_is_proj_fn_shape(&tbl));
        assert!(!level::name_is_proj_fn_shape(&nm("proj")));
        assert!(level::name_is_model_suffix(&nm("_model")));
        assert!(!level::name_is_model_suffix(&nm("_models")));
    }

    #[test]
    fn name_nodup() {
        let mut ns: Vec<Name> = Vec::new();
        ns.push(nm("u"));
        ns.push(nm("v"));
        assert!(level::name_nodup(&ns));
        ns.push(nm("u"));
        assert!(!level::name_nodup(&ns));
    }

    #[test]
    fn level_beq_and_hash() {
        let a = level::max(p("u"), level::succ(level::zero()));
        let b = level::max(p("u"), level::succ(level::zero()));
        assert!(!level::ptr_eq(&a, &b));
        assert!(level::beq(&a, &b));
        assert_eq!(level::hash_data(&a), level::hash_data(&b));
        assert!(!level::beq(&a, &level::imax(p("u"), level::succ(level::zero()))));
    }

    #[test]
    fn the_hash_map_dictionaries_are_hash_data_and_beq() {
        let a = level::max(p("u"), level::succ(level::zero()));
        let b = level::max(p("u"), level::succ(level::zero()));
        assert!(a.eq2(&b));
        assert!(!a.eq2(&p("u")));
        assert_eq!(a.hash64(), level::hash_data(&b));
    }

    /// `max u v ≥ u` and `max u v ≥ v`.
    fn leq_max(u: &Level, v: &Level) {
        let m = level::max(level::dup(u), level::dup(v));
        assert_eq!(level::leq(u, &m), Some(true));
        assert_eq!(level::leq(v, &m), Some(true));
    }

    #[test]
    fn max_is_an_upper_bound() {
        leq_max(&p("u"), &p("v"));
        leq_max(&level::zero(), &p("v"));
        leq_max(&level::succ(p("u")), &level::succ(level::succ(p("u"))));
    }

    #[test]
    fn succ_chain_is_ordered() {
        let z = level::zero();
        let one = level::succ(level::zero());
        let two = level::succ(level::succ(level::zero()));
        assert_eq!(level::leq(&z, &one), Some(true));
        assert_eq!(level::leq(&one, &two), Some(true));
        assert_eq!(level::leq(&two, &one), Some(false));
        assert_eq!(level::leq(&p("u"), &level::succ(p("u"))), Some(true));
        assert_eq!(level::leq(&level::succ(p("u")), &p("u")), Some(false));
    }

    /// `imax u 0` normalises to `0`, `imax 0 v` to `v`, `imax u (succ v)` to
    /// `max u (succ v)`.
    #[test]
    fn imax_normalisations() {
        let a = level::simplify(&level::imax(p("u"), level::zero()));
        assert!(level::is_zero_kind(&a));
        assert!(level::is_zero(&level::imax(p("u"), level::zero())));

        let b = level::simplify(&level::imax(level::zero(), p("v")));
        assert!(level::beq(&b, &p("v")));

        let c = level::simplify(&level::imax(p("u"), level::succ(p("v"))));
        assert!(level::beq(&c, &level::max(p("u"), level::succ(p("v")))));
    }

    #[test]
    fn simplify_is_idempotent() {
        let terms: Vec<Level> = {
            let mut v: Vec<Level> = Vec::new();
            v.push(level::zero());
            v.push(p("u"));
            v.push(level::max(level::zero(), p("u")));
            v.push(level::imax(p("u"), level::imax(p("v"), p("w"))));
            v.push(level::max(level::succ(p("u")), level::succ(level::zero())));
            v.push(level::imax(level::succ(level::zero()), p("v")));
            v.push(level::succ(level::max(p("u"), level::imax(p("v"), level::zero()))));
            v
        };
        let mut i = 0;
        while i < terms.len() {
            let s1 = level::simplify(&terms[i]);
            let s2 = level::simplify(&s1);
            assert!(level::beq(&s1, &s2), "simplify not idempotent at {}", i);
            i += 1;
        }
    }

    #[test]
    fn is_equiv_and_lists() {
        let a = level::max(p("u"), level::zero());
        assert_eq!(level::is_equiv(&a, &p("u")), Some(true));
        assert_eq!(level::is_equiv(&p("u"), &p("v")), Some(false));

        let mut ls: Vec<Level> = Vec::new();
        ls.push(level::max(level::zero(), p("u")));
        ls.push(level::succ(level::zero()));
        let mut rs: Vec<Level> = Vec::new();
        rs.push(p("u"));
        rs.push(level::imax(level::succ(level::zero()), level::succ(level::zero())));
        assert_eq!(level::is_equiv_list(&ls, &rs), Some(true));
        rs.push(level::zero());
        assert_eq!(level::is_equiv_list(&ls, &rs), Some(false));
    }

    #[test]
    fn subst_and_params() {
        let ks = name::singleton(&nm("u"));
        let vs = level::singleton(level::succ(level::zero()));
        let l = level::max(p("u"), p("v"));
        let s = level::subst(&ks, &vs, &l);
        assert!(level::beq(&s, &level::max(level::succ(level::zero()), p("v"))));

        assert!(level::level_has_param(&l));
        assert!(!level::level_has_param(&level::succ(level::zero())));

        let mut params: Vec<Name> = Vec::new();
        params.push(nm("u"));
        assert!(!level::all_params_defined(&params, &l));
        params.push(nm("v"));
        assert!(level::all_params_defined(&params, &l));
    }

    #[test]
    fn never_zero_and_non_zero() {
        assert!(level::is_never_zero(&level::succ(p("u"))));
        assert!(!level::is_never_zero(&level::imax(level::succ(p("u")), p("v"))));
        assert!(level::is_never_zero(&level::max(level::zero(), level::succ(p("u")))));
        assert!(level::is_non_zero(&level::imax(p("u"), level::succ(p("v")))));
        assert!(!level::is_non_zero(&p("u")));
    }

    /// The fueled `leqCore` reports exhaustion as `none`, never as a verdict.
    #[test]
    fn out_of_fuel_is_none() {
        let l = level::imax(p("u"), p("v"));
        let r = level::succ(level::zero());
        assert_eq!(level::leq_core(0, &l, &r, 0), None);
    }

    /// The `imax` by-cases rule (nanoda cases 10-15) terminates on the shapes
    /// the checker actually meets.
    #[test]
    fn imax_by_cases() {
        let l = level::imax(p("u"), p("v"));
        let r = level::max(p("u"), p("v"));
        assert_eq!(level::leq(&l, &r), Some(true));
        assert_eq!(level::leq(&r, &l), Some(false));
        let nested = level::imax(p("u"), level::imax(p("v"), p("w")));
        assert_eq!(level::is_equiv(&nested, &nested), Some(true));
        assert_eq!(
            level::leq(&nested, &level::max(p("u"), level::max(p("v"), p("w")))),
            Some(true)
        );
    }
}
