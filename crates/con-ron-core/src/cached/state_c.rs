//! `ConLeche/Cached/StateC.lean`: the cached checker's per-declaration state
//! and the state-only operation wrappers.
//!
//! ## `ExprC` is `Expr`
//!
//! con-leche's task #198 removed the cached tier's second expression type:
//! `ExprC` *is* `ConLeche.Expr`, one node type with one `BEq` and one
//! `Hashable` (task #10, surprise 1).  So every `ExprC`-typed field below is
//! `crate::kernel::expr::Expr`, and DESIGN.md §3.1's "one Rust module per Lean file"
//! must not be read as licensing a second expression module.
//!
//! ## The monad
//!
//! `CheckCM α = StateT CState CheckM α` becomes `fn(…, &mut CState) ->
//! Result<A, CheckError>` (`core_types`'s module note).  `CState` is *the*
//! state parameter §3.4 reserves `&mut` for.  Two consequences:
//!
//! * a `CheckCM` action whose body is `pure e` is the plain Rust function
//!   `e` — the state argument would be dead weight and dead Lean.  That is
//!   what `peel_fuel` and `subst_level_trees` are below;
//! * con-leche's **linear-update discipline** — `let mp := s.instC; let s :=
//!   { s with instC := {} }; … { s with instC := mp.insert … }`, which
//!   detaches a component before mutating it so that Lean's runtime sees a
//!   unique reference — has no Rust counterpart: `s.inst_c.insert(…)` on a
//!   `&mut CState` *is* the in-place update the dance is there to obtain.
//!   The port therefore drops the detach/reattach and keeps the insertions,
//!   which is the same state transformer.
//!
//! ## Memo key discipline
//!
//! Pointer identity is not available as a key, so the `Expr`-keyed maps are
//! keyed on values with `Hashable Expr` = the cached hash field (`O(1)`, no
//! traversal) and `Eq2 Expr` = pointer identity, then the cached hashes, then
//! structural descent (`expr::beq`, task #11).  The `Level`- and `Name`-keyed
//! caches are the one place structural hashing survives.
//!
//! The **tuple** keys (`(Name, List Level)`, `(Name, Name, List Level)`,
//! `(ExprC × ExprC)`, `(Level × Level)`, `(ExprC × List ExprC × Nat)`) use
//! Lean's *derived* instances, and the port spells them out:
//!
//! * `Hashable (α × β)` is `mixHash (hash a) (hash b)`
//!   (`Init/Data/Hashable.lean:18-19`), and a Lean triple is `(a, (b, c))`,
//!   so a three-component key is `mixHash (hash a) (mixHash (hash b) (hash
//!   c))` — right-nested, not a flat fold;
//! * `Hashable (List α)` is `as.foldl (fun r a => mixHash r (hash a)) 7`
//!   (`Init/Data/Hashable.lean:37-38`) — seed `7`, folded *left*.  Note this
//!   is **not** con-leche's own `levelsHash` (`Expr.lean:136`, seed 13 and a
//!   right fold), which hashes a `.const` node's level list; the memo key
//!   uses the derived instance, so the port does too;
//! * `Hashable Nat` is `UInt64.ofNat n` (`Init/Data/Hashable.lean:14-15`),
//!   i.e. the identity on the `u64` of §3.3 — which is exactly
//!   `hashmap.rs`'s `impl Hashable for u64`;
//! * `BEq (α × β)` is componentwise, `BEq (List α)` is `List.beq`.
//!
//! None of this is load-bearing for the proof: §3.2's abstract-map relation
//! does not see bucket placement, and `mixHash` is opaque in Lean.  It is
//! spelled faithfully anyway so that a hit here is a hit there.
//!
//! ## What is *not* here
//!
//! Everything in the file that touches `ConLeche/Kernel/ExprOps.lean` or
//! `Kernel/Basis.lean`, which are not ported yet: the seven environment-index
//! guards (`isUnitLikeTyC`, `isCtorAppC`, `headHintC`, `unfoldableHeadC`,
//! `sameConstHeadsC`, `rawNatLitC?`, `etaCtorShapeC` — `ExprC.getAppFn`, the
//! pinned basis names), `bvarBoundM` (`Expr.bvarB`, the exact accessor), the
//! nine syntactic wrappers `inst1M`, `instListM`, `instListRevM`,
//! `abstract1M`, `abstractRangeM`, `mkAppNM`, `instSpineM`, `piResidualM`,
//! `instLevelParamsM`, the three lazy stored-constant conversions
//! `storedTyIdxM`, `storedValIdxM` (`Expr.exprPtrBEq`) and with them
//! `constTyAtM`, `constValAtM`, `ruleRhsAtM`, and the memoized DAG walk
//! `constsResolveFCGo`/`constsResolveFC`.  `instCCapC` and the `instC` map
//! itself *are* here, because they are state.

use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::expr::Expr;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::HashMap;
use crate::ron::hashmap::Hashable;
use crate::kernel::level;
use crate::kernel::level::Level;
use crate::kernel::name;
use crate::kernel::name::Name;
use std::vec::Vec;

/// con-leche: ConLeche/Cached/StateC.lean:166 CheckCM
/// `abbrev CheckCM := StateT CState CheckM`, the cached checker's monad, as
/// Rust's `Result` over a `&mut CState` parameter: a `CheckCM A` action is a
/// function `fn(…, &mut CState) -> CheckCM<A>` (the module note above).  Like
/// `core_types::CheckM` this alias is erased before Charon sees anything; it
/// is here so a ported signature can say what con-leche says.
pub type CheckCM<T> = Result<T, CheckError>;

// ---------------------------------------------------------------------------
// The derived dictionaries for the tuple and list memo keys
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Lean's derived `Hashable (List α)` over `Level` — `foldl mixHash 7`
/// (`Init/Data/Hashable.lean:37-38`), which is what the cited fields'
/// `(Name × List Level)` keys hash their list component with.
pub fn levels_list_hash(us: &Vec<Level>) -> u64 {
    levels_list_hash_from(us, 0, 7)
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The index recursion behind `levels_list_hash`; the fold is a *left* one,
/// so the accumulator is carried forward.
pub fn levels_list_hash_from(us: &Vec<Level>, i: usize, acc: u64) -> u64 {
    if i >= us.len() {
        acc
    } else {
        levels_list_hash_from(us, i + 1, name::mix_hash(acc, level::hash_data(&us[i])))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Lean's derived `Hashable (List α)` over `ExprC`, for the `instC` key's
/// argument list.
pub fn exprs_list_hash(es: &Vec<Expr>) -> u64 {
    exprs_list_hash_from(es, 0, 7)
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The index recursion behind `exprs_list_hash`.
pub fn exprs_list_hash_from(es: &Vec<Expr>, i: usize, acc: u64) -> u64 {
    if i >= es.len() {
        acc
    } else {
        exprs_list_hash_from(es, i + 1, name::mix_hash(acc, expr::hash(&es[i])))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Lean's `BEq (List ExprC)` (`List.beq` over `BEq ExprC`), the twin of
/// `expr::levels_beq` for the `instC` key's argument list.
pub fn exprs_beq(ls: &Vec<Expr>, rs: &Vec<Expr>) -> bool {
    if ls.len() != rs.len() {
        false
    } else {
        exprs_beq_from(ls, rs, 0)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The index recursion behind `exprs_beq`.
pub fn exprs_beq_from(ls: &Vec<Expr>, rs: &Vec<Expr>, i: usize) -> bool {
    if i >= ls.len() {
        true
    } else if expr::beq(&ls[i], &rs[i]) {
        exprs_beq_from(ls, rs, i + 1)
    } else {
        false
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key dictionary of `constTyAt`/`constValAt`: Lean's derived
/// `Hashable (Name × List Level)`.
impl Hashable for (Name, Vec<Level>) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `mixHash (hash n) (List.hash us)`, the derived product instance.
    fn hash64(&self) -> u64 {
        name::mix_hash(name::hash_data(&self.0), levels_list_hash(&self.1))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key equality of `constTyAt`/`constValAt`: Lean's derived
/// `BEq (Name × List Level)`, componentwise.
impl Eq2 for (Name, Vec<Level>) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// The derived product equality, componentwise.
    fn eq2(&self, other: &Self) -> bool {
        name::beq(&self.0, &other.0) && expr::levels_beq(&self.1, &other.1)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key dictionary of `ruleRhsAt`.  A Lean triple is `(a, (b, c))`, so
/// the derived hash is right-nested.
impl Hashable for (Name, Name, Vec<Level>) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `mixHash (hash c) (mixHash (hash j) (List.hash us))`.
    fn hash64(&self) -> u64 {
        name::mix_hash(
            name::hash_data(&self.0),
            name::mix_hash(name::hash_data(&self.1), levels_list_hash(&self.2)),
        )
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key equality of `ruleRhsAt`, componentwise.
impl Eq2 for (Name, Name, Vec<Level>) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// The derived triple equality, componentwise.
    fn eq2(&self, other: &Self) -> bool {
        name::beq(&self.0, &other.0)
            && name::beq(&self.1, &other.1)
            && expr::levels_beq(&self.2, &other.2)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key dictionary of `defeqC`.
impl Hashable for (Expr, Expr) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `mixHash (hash a) (hash b)` over the two stored `Expr` words.
    fn hash64(&self) -> u64 {
        name::mix_hash(expr::hash(&self.0), expr::hash(&self.1))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key equality of `defeqC`: `Expr.beq` on both components, with its
/// pointer and computed-word fast paths (§3.2).
impl Eq2 for (Expr, Expr) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `Expr.beq` on both components, with its fast paths (§3.2).
    fn eq2(&self, other: &Self) -> bool {
        expr::beq(&self.0, &other.0) && expr::beq(&self.1, &other.1)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key dictionary of `eqvC`.
impl Hashable for (Level, Level) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `mixHash (hash l) (hash r)` over the two stored `Level` words.
    fn hash64(&self) -> u64 {
        name::mix_hash(level::hash_data(&self.0), level::hash_data(&self.1))
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key equality of `eqvC`.
impl Eq2 for (Level, Level) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `Level.beq` on both components.
    fn eq2(&self, other: &Self) -> bool {
        level::beq(&self.0, &other.0) && level::beq(&self.1, &other.1)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key dictionary of `instC`, the persistent bulk-instantiation memo:
/// the whole argument tuple `(e, vs, d)`, hashed right-nested.
impl Hashable for (Expr, Vec<Expr>, u64) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// `mixHash (hash e) (mixHash (List.hash vs) (UInt64.ofNat d))`.
    fn hash64(&self) -> u64 {
        name::mix_hash(
            expr::hash(&self.0),
            name::mix_hash(exprs_list_hash(&self.1), self.2),
        )
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// The key equality of `instC`, componentwise.
impl Eq2 for (Expr, Vec<Expr>, u64) {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// The derived triple equality, componentwise.
    fn eq2(&self, other: &Self) -> bool {
        expr::beq(&self.0, &other.0) && exprs_beq(&self.1, &other.1) && self.2 == other.2
    }
}

// ---------------------------------------------------------------------------
// The state (`StateC.lean:122-172`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:122-126 CConstE
/// One cached-environment entry: a stored constant's annotated type and (for
/// definitions/theorems/opaques) value, each tagged with the very `Expr`
/// object it came from.  Deviations: `ExprC` is `Expr` (the module note), and
/// the Lean's `val := none` field default is `cconst_e_new`.
pub struct CConstE {
    pub ty_e: Expr,
    pub ty: Expr,
    pub val: Option<(Expr, Expr)>,
}

/// con-leche: ConLeche/Cached/StateC.lean:122-126 CConstE
/// The cited structure at its one field default, `val := none`.
pub fn cconst_e_new(ty_e: Expr, ty: Expr) -> CConstE {
    CConstE {
        ty_e,
        ty,
        val: None,
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Per-declaration state: the converted-constant cache `ienv`, the memo
/// caches for the five entry points, the lazy caches for level-instantiated
/// stored constants, the level-operation memos, and the persistent
/// bulk-instantiation memo.  Fourteen maps, in the cited field order and at
/// the cited key types (§3.1: the same memo tables with the same keys,
/// inserted and cleared at the same points).
pub struct CState {
    pub ienv: HashMap<Name, CConstE>,
    pub const_ty_at: HashMap<(Name, Vec<Level>), Expr>,
    pub const_val_at: HashMap<(Name, Vec<Level>), Expr>,
    pub rule_rhs_at: HashMap<(Name, Name, Vec<Level>), Expr>,
    pub whnf_core_c: HashMap<Expr, Expr>,
    pub whnf_c: HashMap<Expr, Expr>,
    pub infer_c: HashMap<Expr, Expr>,
    /// The io-grade inference memo, kept apart from `infer_c` per con-leche's
    /// task-#170 memo ruling: an io entry witnesses fewer checks than the
    /// full-infer claims consume.
    pub infer_io_c: HashMap<Expr, Expr>,
    pub defeq_c: HashMap<(Expr, Expr), bool>,
    pub annot_c: HashMap<Expr, Expr>,
    pub lsimp_c: HashMap<Level, Level>,
    pub lnz_c: HashMap<Level, bool>,
    pub eqv_c: HashMap<(Level, Level), bool>,
    pub inst_c: HashMap<(Expr, Vec<Expr>, u64), Expr>,
}

/// con-leche: ConLeche/Cached/StateC.lean:158 _
/// The cited `instance : Inhabited CState := ⟨{}⟩`: every field at its `{}`
/// default.  This is the state a declaration starts from.
pub fn cstate_new() -> CState {
    CState {
        ienv: HashMap::new(),
        const_ty_at: HashMap::new(),
        const_val_at: HashMap::new(),
        rule_rhs_at: HashMap::new(),
        whnf_core_c: HashMap::new(),
        whnf_c: HashMap::new(),
        infer_c: HashMap::new(),
        infer_io_c: HashMap::new(),
        defeq_c: HashMap::new(),
        annot_c: HashMap::new(),
        lsimp_c: HashMap::new(),
        lnz_c: HashMap::new(),
        eqv_c: HashMap::new(),
        inst_c: HashMap::new(),
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:162 instCCapC
/// Entry bound for the persistent bulk-instantiation memo: 32 000 000.
/// `usize`, because the one thing it is compared with is `instC.size`.
pub fn inst_c_cap_c() -> usize {
    32000000
}

/// con-leche: ConLeche/Cached/StateC.lean:172 peelFuel
/// con-leche: ConLeche/Cached/StateC.lean:174 peelFuelM
/// Peel fuel of the binder-telescope loops: a constant beyond any real
/// binder chain.  The fuel is semantically transparent — on exhaustion the
/// leaf phase hands the residual chain back to the knot.
///
/// The second citation is `peelFuelM`, whose body is `pure peelFuel`: a
/// `CheckCM` action with a pure body is the plain Rust function (the module
/// note on the monad).
pub fn peel_fuel() -> u64 {
    16777216
}

// ---------------------------------------------------------------------------
// Level operations (`StateC.lean:235-308`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:235-237 substLevelTreesM
/// `ls.map (Level.subst ks us)`.  Pure, so no state parameter (the module
/// note); the `map` is the index recursion below.
pub fn subst_level_trees(ks: &Vec<Name>, us: &Vec<Level>, ls: &Vec<Level>) -> Vec<Level> {
    subst_level_trees_from(ks, us, ls, 0, Vec::new())
}

/// con-leche: ConLeche/Cached/StateC.lean:235-237 substLevelTreesM
/// The index recursion the cited `List.map` becomes; the accumulator is
/// passed by value and returned (task #6's rule).
pub fn subst_level_trees_from(
    ks: &Vec<Name>,
    us: &Vec<Level>,
    ls: &Vec<Level>,
    i: usize,
    out: Vec<Level>,
) -> Vec<Level> {
    if i >= ls.len() {
        out
    } else {
        let mut out = out;
        out.push(level::subst(ks, us, &ls[i]));
        subst_level_trees_from(ks, us, ls, i + 1, out)
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:240-248 simplifyLM
/// The cited `s.lsimpC[u]?` probe, as its own function over a *shared*
/// state borrow: the hit is copied out, so the borrow of the map ends before
/// the miss branch writes to the state.
pub fn lsimp_probe(s: &CState, u: &Level) -> Option<Level> {
    match s.lsimp_c.get(u) {
        Some(r) => Some(level::dup(r)),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:240-248 simplifyLM
/// `Level.simplify`, persistently memoized in `lsimpC`.
pub fn simplify_l_m(s: &mut CState, u: &Level) -> Level {
    match lsimp_probe(s, u) {
        Some(r) => r,
        None => {
            let r = level::simplify(u);
            s.lsimp_c.insert(level::dup(u), level::dup(&r));
            r
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:251-259 isNonZeroLM
/// The cited `s.lnzC[u]?` probe (see `lsimp_probe`).
pub fn lnz_probe(s: &CState, u: &Level) -> Option<bool> {
    match s.lnz_c.get(u) {
        Some(r) => Some(*r),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:251-259 isNonZeroLM
/// `Level.isNonZero`, persistently memoized in `lnzC`.
pub fn is_non_zero_l_m(s: &mut CState, u: &Level) -> bool {
    match lnz_probe(s, u) {
        Some(r) => r,
        None => {
            let r = level::is_non_zero(u);
            s.lnz_c.insert(level::dup(u), r);
            r
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:270-298 isEquivLM
/// The cited `s.eqvC[(l, r)]?` probe (see `lsimp_probe`).
pub fn eqv_probe(s: &CState, key: &(Level, Level)) -> Option<bool> {
    match s.eqv_c.get(key) {
        Some(b) => Some(*b),
        None => None,
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:270-298 isEquivLM
/// Level equivalence with a persistent result cache: the `l == r` head test
/// (official's `is_equivalent` disjunct, which writes no cache entry), then
/// the `eqvC` probe, then simplify both sides through `lsimpC`, compare, and
/// run the `leqCore` cascade both ways.
///
/// The cited function's `lsimpC` updates survive every branch, including the
/// two that answer `none` and leave `eqvC` untouched; so do these.
pub fn is_equiv_l_m(s: &mut CState, l: &Level, r: &Level) -> Option<bool> {
    if level::beq(l, r) {
        Some(true)
    } else {
        let key = (level::dup(l), level::dup(r));
        match eqv_probe(s, &key) {
            Some(b) => Some(b),
            None => {
                let ls = simplify_l_m(s, l);
                let rs = simplify_l_m(s, r);
                if level::beq(&ls, &rs) {
                    s.eqv_c.insert(key, true);
                    Some(true)
                } else {
                    match level::leq_core(level::default_fuel(), &ls, &rs, 0) {
                        Some(false) => {
                            s.eqv_c.insert(key, false);
                            Some(false)
                        }
                        Some(true) => {
                            match level::leq_core(level::default_fuel(), &rs, &ls, 0) {
                                Some(b) => {
                                    s.eqv_c.insert(key, b);
                                    Some(b)
                                }
                                None => None,
                            }
                        }
                        None => None,
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:301-308 isEquivListLM
/// Pointwise `isEquivLM`.
pub fn is_equiv_list_l_m(s: &mut CState, ls: &Vec<Level>, rs: &Vec<Level>) -> Option<bool> {
    is_equiv_list_l_m_from(s, ls, rs, 0)
}

/// con-leche: ConLeche/Cached/StateC.lean:301-308 isEquivListLM
/// The index recursion the cited three-arm `List` recursion becomes.  The
/// arm order matters and is kept: a length mismatch answers `some false`
/// only *after* the common prefix has been walked, so a `none` from an
/// earlier pair still wins.
pub fn is_equiv_list_l_m_from(
    s: &mut CState,
    ls: &Vec<Level>,
    rs: &Vec<Level>,
    i: usize,
) -> Option<bool> {
    if i >= ls.len() && i >= rs.len() {
        Some(true)
    } else if i < ls.len() && i < rs.len() {
        match is_equiv_l_m(s, &ls[i], &rs[i]) {
            None => None,
            Some(false) => Some(false),
            Some(true) => is_equiv_list_l_m_from(s, ls, rs, i + 1),
        }
    } else {
        Some(false)
    }
}

// ---------------------------------------------------------------------------
// The flush and the converted-constant record (`StateC.lean:394-460`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:394-398 CState.flushed
/// Drop the environment-dependent caches (an environment transition).  The
/// environment-independent components — the converted-constant cache `ienv`
/// (self-certified by its `Expr` tags) and the three level-operation memos —
/// survive.
///
/// Deviation: the cited function is `CState → CState`; here it mutates the
/// state in place, because `CState` is the `&mut` state parameter of §3.4
/// and `clear` keeps the bucket allocation (`hashmap.rs`'s `clear` is
/// documented as exactly this `{ s with … := {} }`).  Same state
/// transformer, no reallocation.
pub fn flushed(s: &mut CState) {
    s.const_ty_at.clear();
    s.const_val_at.clear();
    s.rule_rhs_at.clear();
    s.whnf_core_c.clear();
    s.whnf_c.clear();
    s.infer_c.clear();
    s.infer_io_c.clear();
    s.defeq_c.clear();
    s.annot_c.clear();
    s.inst_c.clear();
}

/// con-leche: ConLeche/Cached/StateC.lean:400 flushC
/// `modify (·.flushed)`, i.e. the state action of `flushed`.
pub fn flush_c(s: &mut CState) {
    flushed(s)
}

/// con-leche: ConLeche/Cached/StateC.lean:455-460 recordCConst
/// Record an accepted constant's converted type/value, tagged with the very
/// `Expr` objects pushed into the environment.
pub fn record_c_const(
    s: &mut CState,
    n: Name,
    ty_e: Expr,
    ty: Expr,
    val: Option<(Expr, Expr)>,
) {
    s.ienv.insert(n, CConstE { ty_e, ty, val });
}

#[cfg(test)]
mod tests {
    use crate::kernel::expr;
    use crate::kernel::expr::Expr;
    use crate::ron::hashmap::Eq2;
    use crate::ron::hashmap::HashMap;
    use crate::ron::hashmap::Hashable;
    use crate::kernel::level;
    use crate::kernel::level::Level;
    use crate::kernel::name;
    use crate::kernel::name::Name;
    use crate::cached::state_c;

    fn nm(s: &str) -> Name {
        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
        name::mk_str(name::anonymous(), cps)
    }

    fn lp(s: &str) -> Level {
        level::param(nm(s))
    }

    /// A tuple-keyed map round trip, on all five key shapes.
    #[test]
    fn tuple_keys_round_trip() {
        // (Name, Vec<Level>)
        let mut m1: HashMap<(Name, Vec<Level>), Expr> = HashMap::new();
        let k1 = (nm("f"), vec![lp("u"), lp("v")]);
        let k1b = (nm("f"), vec![lp("u"), lp("v")]);
        let k1c = (nm("f"), vec![lp("v"), lp("u")]);
        assert!(k1.eq2(&k1b));
        assert_eq!(k1.hash64(), k1b.hash64());
        assert!(!k1.eq2(&k1c));
        assert!(m1.insert(k1, expr::bvar(3)).is_none());
        match m1.get(&k1b) {
            Some(e) => assert!(expr::beq(e, &expr::bvar(3))),
            None => panic!("structurally equal key missed"),
        }
        assert!(m1.get(&k1c).is_none());
        assert!(m1.get(&(nm("g"), vec![lp("u"), lp("v")])).is_none());
        assert!(m1.get(&(nm("f"), vec![lp("u")])).is_none());

        // (Name, Name, Vec<Level>) — the triple hashes right-nested
        let mut m2: HashMap<(Name, Name, Vec<Level>), Expr> = HashMap::new();
        let k2 = (nm("R"), nm("C"), vec![lp("u")]);
        let k2b = (nm("R"), nm("C"), vec![lp("u")]);
        assert_eq!(
            k2.hash64(),
            name::mix_hash(
                name::hash_data(&nm("R")),
                name::mix_hash(name::hash_data(&nm("C")), state_c::levels_list_hash(&vec![lp("u")]))
            )
        );
        m2.insert(k2, expr::bvar(1));
        assert!(m2.get(&k2b).is_some());
        assert!(m2.get(&(nm("C"), nm("R"), vec![lp("u")])).is_none());

        // (Expr, Expr)
        let mut m3: HashMap<(Expr, Expr), bool> = HashMap::new();
        let a = expr::app(expr::bvar(0), expr::bvar(1));
        let b = expr::bvar(2);
        m3.insert((expr::dup(&a), expr::dup(&b)), true);
        assert_eq!(
            m3.get(&(expr::app(expr::bvar(0), expr::bvar(1)), expr::bvar(2))),
            Some(&true)
        );
        assert!(m3.get(&(expr::dup(&b), expr::dup(&a))).is_none());

        // (Level, Level)
        let mut m4: HashMap<(Level, Level), bool> = HashMap::new();
        m4.insert((lp("u"), level::zero()), false);
        assert_eq!(m4.get(&(lp("u"), level::zero())), Some(&false));
        assert!(m4.get(&(level::zero(), lp("u"))).is_none());

        // (Expr, Vec<Expr>, u64) — the `instC` key
        let mut m5: HashMap<(Expr, Vec<Expr>, u64), Expr> = HashMap::new();
        let k5 = (expr::bvar(0), vec![expr::bvar(1), expr::bvar(2)], 3u64);
        let k5b = (expr::bvar(0), vec![expr::bvar(1), expr::bvar(2)], 3u64);
        assert!(k5.eq2(&k5b));
        assert_eq!(k5.hash64(), k5b.hash64());
        m5.insert(k5, expr::bvar(9));
        assert!(m5.get(&k5b).is_some());
        // the depth is part of the key
        assert!(m5
            .get(&(expr::bvar(0), vec![expr::bvar(1), expr::bvar(2)], 4u64))
            .is_none());
        // and so is the argument list
        assert!(m5.get(&(expr::bvar(0), vec![expr::bvar(1)], 3u64)).is_none());
    }

    /// The derived list hash is the left fold from seed 7, and is *not*
    /// con-leche's own `levelsHash` (seed 13, right fold).
    #[test]
    fn list_hash_is_the_derived_one() {
        let us = vec![lp("u"), lp("v")];
        assert_eq!(
            state_c::levels_list_hash(&us),
            name::mix_hash(
                name::mix_hash(7, level::hash_data(&us[0])),
                level::hash_data(&us[1])
            )
        );
        assert_eq!(state_c::levels_list_hash(&Vec::new()), 7);
        assert_ne!(state_c::levels_list_hash(&us), level::levels_hash(&us));
        let es = vec![expr::bvar(0), expr::bvar(1)];
        assert_eq!(state_c::exprs_list_hash(&Vec::new()), 7);
        assert_eq!(
            state_c::exprs_list_hash(&es),
            name::mix_hash(name::mix_hash(7, expr::hash(&es[0])), expr::hash(&es[1]))
        );
        assert!(state_c::exprs_beq(&es, &vec![expr::bvar(0), expr::bvar(1)]));
        assert!(!state_c::exprs_beq(&es, &vec![expr::bvar(0)]));
        assert!(!state_c::exprs_beq(&es, &vec![expr::bvar(1), expr::bvar(0)]));
    }

    /// `CState.flushed` drops the ten environment-dependent caches and keeps
    /// the four environment-independent ones.
    #[test]
    fn flush_keeps_ienv_and_the_level_memos() {
        let mut s = state_c::cstate_new();
        let e = expr::bvar(0);
        s.const_ty_at.insert((nm("a"), Vec::new()), expr::dup(&e));
        s.const_val_at.insert((nm("a"), Vec::new()), expr::dup(&e));
        s.rule_rhs_at
            .insert((nm("a"), nm("b"), Vec::new()), expr::dup(&e));
        s.whnf_core_c.insert(expr::dup(&e), expr::dup(&e));
        s.whnf_c.insert(expr::dup(&e), expr::dup(&e));
        s.infer_c.insert(expr::dup(&e), expr::dup(&e));
        s.infer_io_c.insert(expr::dup(&e), expr::dup(&e));
        s.defeq_c.insert((expr::dup(&e), expr::dup(&e)), true);
        s.annot_c.insert(expr::dup(&e), expr::dup(&e));
        s.inst_c
            .insert((expr::dup(&e), Vec::new(), 0), expr::dup(&e));
        s.lsimp_c.insert(lp("u"), lp("u"));
        s.lnz_c.insert(lp("u"), true);
        s.eqv_c.insert((lp("u"), lp("v")), false);
        state_c::record_c_const(&mut s, nm("c"), expr::dup(&e), expr::dup(&e), None);
        assert_eq!(s.ienv.len(), 1);

        state_c::flush_c(&mut s);

        assert_eq!(s.const_ty_at.len(), 0);
        assert_eq!(s.const_val_at.len(), 0);
        assert_eq!(s.rule_rhs_at.len(), 0);
        assert_eq!(s.whnf_core_c.len(), 0);
        assert_eq!(s.whnf_c.len(), 0);
        assert_eq!(s.infer_c.len(), 0);
        assert_eq!(s.infer_io_c.len(), 0);
        assert_eq!(s.defeq_c.len(), 0);
        assert_eq!(s.annot_c.len(), 0);
        assert_eq!(s.inst_c.len(), 0);
        // survivors
        assert_eq!(s.ienv.len(), 1);
        assert_eq!(s.lsimp_c.len(), 1);
        assert_eq!(s.lnz_c.len(), 1);
        assert_eq!(s.eqv_c.len(), 1);
        // and the entry is intact
        match s.ienv.get(&nm("c")) {
            Some(ent) => {
                assert!(expr::beq(&ent.ty, &e));
                assert!(ent.val.is_none());
            }
            None => panic!("ienv lost its entry"),
        }
        let fresh = state_c::cconst_e_new(expr::dup(&e), expr::dup(&e));
        assert!(fresh.val.is_none());
    }

    /// The level memo wrappers agree with the unmemoized functions, and a
    /// second call is a hit.
    #[test]
    fn level_memos_agree_and_hit() {
        let mut s = state_c::cstate_new();
        let u = level::max(level::zero(), level::succ(level::zero()));
        let r1 = state_c::simplify_l_m(&mut s, &u);
        assert!(level::beq(&r1, &level::simplify(&u)));
        assert_eq!(s.lsimp_c.len(), 1);
        let r2 = state_c::simplify_l_m(&mut s, &u);
        assert!(level::beq(&r2, &r1));
        assert_eq!(s.lsimp_c.len(), 1);

        assert_eq!(
            state_c::is_non_zero_l_m(&mut s, &u),
            level::is_non_zero(&u)
        );
        assert_eq!(s.lnz_c.len(), 1);
        assert_eq!(state_c::is_non_zero_l_m(&mut s, &u), level::is_non_zero(&u));
        assert_eq!(s.lnz_c.len(), 1);

        // `l == r` answers `some true` and writes no cache entry
        let before = s.eqv_c.len();
        assert_eq!(state_c::is_equiv_l_m(&mut s, &u, &level::dup(&u)), Some(true));
        assert_eq!(s.eqv_c.len(), before);
        // an honest pair does write one, and agrees with `Level.isEquiv`
        let a = level::max(lp("u"), level::zero());
        let b = lp("u");
        assert_eq!(state_c::is_equiv_l_m(&mut s, &a, &b), level::is_equiv(&a, &b));
        assert_eq!(s.eqv_c.len(), before + 1);
        assert_eq!(state_c::is_equiv_l_m(&mut s, &a, &b), level::is_equiv(&a, &b));
        assert_eq!(s.eqv_c.len(), before + 1);
        let c = level::succ(lp("u"));
        assert_eq!(state_c::is_equiv_l_m(&mut s, &a, &c), level::is_equiv(&a, &c));

        // the pointwise version, including the length mismatch
        let ls = vec![level::dup(&a), level::dup(&c)];
        let rs = vec![level::dup(&b), level::dup(&c)];
        assert_eq!(
            state_c::is_equiv_list_l_m(&mut s, &ls, &rs),
            level::is_equiv_list(&ls, &rs)
        );
        assert_eq!(
            state_c::is_equiv_list_l_m(&mut s, &ls, &vec![level::dup(&b)]),
            Some(false)
        );
        assert_eq!(
            state_c::is_equiv_list_l_m(&mut s, &Vec::new(), &Vec::new()),
            Some(true)
        );

        // the pure wrappers
        assert_eq!(state_c::peel_fuel(), 16777216);
        assert_eq!(state_c::inst_c_cap_c(), 32000000);
        let ks = vec![nm("u")];
        let vs = vec![level::zero()];
        let out = state_c::subst_level_trees(&ks, &vs, &vec![lp("u"), lp("w")]);
        assert_eq!(out.len(), 2);
        assert!(level::beq(&out[0], &level::zero()));
        assert!(level::beq(&out[1], &lp("w")));
    }
}
