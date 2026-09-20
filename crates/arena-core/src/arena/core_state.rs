//! `arena::core_state` — the checker-level caches of (C).
//!
//! The Rust twin of `proof/ConRon/Arena/CoreState.lean`, field for field.
//! `arena::monad`'s `Memos` holds the **per-call** tables of the `ExprOps`
//! twins — cleared at every top-level entry, because their answers depend on
//! the substituted term.  This module holds the **per-declaration** ones,
//! which the checker keeps for the whole of one declaration's check and drops
//! at its boundary (DESIGN.md §8.3, "Caches", second and third bullets):
//!
//! * the five unary entry-point memos `whnf_core`, `whnf`, `infer`,
//!   `infer_io`, `annotate` : `EIdx ↦ EIdx` — *three separate infer grades*,
//!   because con-leche's lesson 9 is that a hit in one grade must never serve
//!   another;
//! * `defeq` on the ORDERED pair with the `bool` verdict, both signs;
//! * the two level-verdict caches (`(LIdx, LIdx)`, `(LsIdx, LsIdx)`);
//! * the three lazy instantiated-constant caches (`const_ty_at` /
//!   `const_val_at` / `rule_rhs_at`, con-leche's arena task #26).
//!
//! **A cap, not an eviction policy** (DESIGN.md §8.3, lesson 10): past
//! `CACHE_CAP` entries a table is dropped whole and starts again.  One
//! `len()` test per insert, which is what the twin's `mp.size < cacheCap`
//! says.
//!
//! ## The one deviation from the twin, and it is `ron::HashMap`'s
//!
//! The twin's `Caches.dropScratchEntries` is eleven `Std.HashMap.filter`
//! calls, and its own doc says "the Rust spelling is `HashMap::retain` per
//! table".  **`ron::hashmap::HashMap` has no `retain` and no iteration API at
//! all** — `new`, `with_capacity`, `len`, `get`, `contains_key`, `insert`,
//! `remove`, `clear`, `dup` is the whole surface, and adding one belongs to
//! `con-ron-core` rather than to this task.  So each table carries a
//! **journal**: a `Vec` of the keys whose row was NOT keepable at the moment
//! it was written (`keep_e` and its five siblings below).  At the drop the
//! journal is walked, each journalled key's *current* value is re-tested, and
//! the row is removed exactly when the test says so.
//!
//! That is `filter keep` and not an approximation of it, by two invariants:
//!
//! 1. a key absent from the journal was keepable when it was last written,
//!    and a row is only ever rewritten through `*_set` (which journals it
//!    again if the new row is not keepable) — so every non-keepable row's key
//!    IS in the journal;
//! 2. the drop re-tests, so a journalled key whose row has since become
//!    keepable survives.
//!
//! The journal costs one `Vec` push per *scratch-touching* insert, i.e. per
//! row the drop is going to delete anyway, and nothing at all for the rows
//! that survive.  A `ron::HashMap::retain` would retire it; that is a P6
//! item, noted in DESIGN.md's task #97-P4c section.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use con_ron_core::ron::hashmap::{Dup, Eq2, HashMap, Hashable};
use con_ron_core::kernel::name;
use std::vec::Vec;

// ---------------------------------------------------------------------------
// The composite keys
//
// Lean's `Prod` carries derived `BEq`/`Hashable` instances; the port writes
// the dictionaries by hand, exactly as `arena::monad`'s `EIdxNat` does for
// `(EIdx × Nat)` and `con_ron_core::kernel::expr_ops::ExprNatKey` for
// `(Expr × Nat)`.  A handle IS its own hash (DESIGN.md §8.3's identity
// hashing), mixed pairwise as Lean's `instHashableProd` mixes.
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:71-73 Caches.defeqC` — the
/// ORDERED pair of expression handles the `defeq` verdict is stored at.
pub struct EIdxPair {
    pub a: EIdx,
    pub b: EIdx,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
impl Hashable for EIdxPair {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.a.hash64(), self.b.hash64())
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
impl Eq2 for EIdxPair {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &EIdxPair) -> bool {
        if self.a.eq2(&other.a) {
            self.b.eq2(&other.b)
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for EIdxPair {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> EIdxPair {
        EIdxPair { a: self.a.dup2(), b: self.b.dup2() }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/CoreState.lean:71-73 Caches.defeqC
/// Build a `defeq` key, copying the two handle words.
pub fn eidx_pair(a: &EIdx, b: &EIdx) -> EIdxPair {
    EIdxPair { a: a.dup2(), b: b.dup2() }
}

/// con-leche: ConLeche/Kernel/Level.lean:158-163 isEquiv
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:74-75 Caches.lvlEqC` — the
/// pair of level handles a `Level.isEquiv` verdict is cached at.
pub struct LIdxPair {
    pub a: LIdx,
    pub b: LIdx,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
impl Hashable for LIdxPair {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.a.hash64(), self.b.hash64())
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
impl Eq2 for LIdxPair {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &LIdxPair) -> bool {
        if self.a.eq2(&other.a) {
            self.b.eq2(&other.b)
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LIdxPair {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LIdxPair {
        LIdxPair { a: self.a.dup2(), b: self.b.dup2() }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/CoreState.lean:74-75 Caches.lvlEqC
/// Build a level-verdict key.
pub fn lidx_pair(a: &LIdx, b: &LIdx) -> LIdxPair {
    LIdxPair { a: a.dup2(), b: b.dup2() }
}

/// con-leche: ConLeche/Kernel/Level.lean:165-172 isEquivList
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:76-77 Caches.lvlsEqC` — the
/// pair of universe-argument lists a pairwise verdict is cached at.
pub struct LsIdxPair {
    pub a: LsIdx,
    pub b: LsIdx,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
impl Hashable for LsIdxPair {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.a.hash64(), self.b.hash64())
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
impl Eq2 for LsIdxPair {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &LsIdxPair) -> bool {
        if self.a.eq2(&other.a) {
            self.b.eq2(&other.b)
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for LsIdxPair {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> LsIdxPair {
        LsIdxPair { a: self.a.dup2(), b: self.b.dup2() }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/CoreState.lean:76-77 Caches.lvlsEqC
/// Build a level-list-verdict key.
pub fn lsidx_pair(a: &LsIdx, b: &LsIdx) -> LsIdxPair {
    LsIdxPair { a: a.dup2(), b: b.dup2() }
}

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:78-81 Caches.constTyC` — a
/// stored constant's name together with a universe-argument list: the key of
/// the two instantiated-constant caches.
pub struct NLsKey {
    pub n: NIdx,
    pub us: LsIdx,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
impl Hashable for NLsKey {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(self.n.hash64(), self.us.hash64())
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
impl Eq2 for NLsKey {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &NLsKey) -> bool {
        if self.n.eq2(&other.n) {
            self.us.eq2(&other.us)
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for NLsKey {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> NLsKey {
        NLsKey { n: self.n.dup2(), us: self.us.dup2() }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/CoreState.lean:78-81 Caches.constTyC
/// Build an instantiated-constant key.
pub fn nls_key(n: &NIdx, us: &LsIdx) -> NLsKey {
    NLsKey { n: n.dup2(), us: us.dup2() }
}

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:82-85 Caches.ruleRhsC` — the
/// TRIPLE a rule's right-hand side is determined by: the recursor, the rule's
/// constructor and the levels.
pub struct NNLsKey {
    pub rec_name: NIdx,
    pub ctor: NIdx,
    pub us: LsIdx,
}

/// con-leche: none — Lean's `instHashableProd`, `mixHash` over the components
impl Hashable for NNLsKey {
    /// con-leche: none — Lean's `instHashableProd`
    fn hash64(&self) -> u64 {
        name::mix_hash(
            self.rec_name.hash64(),
            name::mix_hash(self.ctor.hash64(), self.us.hash64()),
        )
    }
}

/// con-leche: none — Lean's `instBEqProd`, componentwise
impl Eq2 for NNLsKey {
    /// con-leche: none — Lean's `instBEqProd`
    fn eq2(&self, other: &NNLsKey) -> bool {
        if self.rec_name.eq2(&other.rec_name) {
            if self.ctor.eq2(&other.ctor) {
                self.us.eq2(&other.us)
            } else {
                false
            }
        } else {
            false
        }
    }
}

/// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
impl Dup for NNLsKey {
    /// con-leche: none — the value copy that Lean's value semantics hides (DESIGN.md §3.2)
    fn dup2(&self) -> NNLsKey {
        NNLsKey {
            rec_name: self.rec_name.dup2(),
            ctor: self.ctor.dup2(),
            us: self.us.dup2(),
        }
    }
}

/// con-leche: none — arena infrastructure; Lean twin: proof/ConRon/Arena/CoreState.lean:82-85 Caches.ruleRhsC
/// Build an iota-rule right-hand-side key.
pub fn nnls_key(rec_name: &NIdx, ctor: &NIdx, us: &LsIdx) -> NNLsKey {
    NNLsKey {
        rec_name: rec_name.dup2(),
        ctor: ctor.dup2(),
        us: us.dup2(),
    }
}

// ---------------------------------------------------------------------------
// The record (`CoreState.lean:50-85`)
// ---------------------------------------------------------------------------

/// con-leche: ConLeche/Cached/StateC.lean:127-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:50-85 Caches` — the
/// per-declaration caches of the arena checker, in one record beside
/// `arena::monad`'s per-call `Memos`.  Keeping the two apart is deliberate:
/// the per-call clear and the per-declaration drop are different operations
/// on different lifetimes.
///
/// Each of the eleven tables is followed by its **journal** (the module
/// note): the keys whose row was not keepable when it was written.
pub struct Caches {
    /// `whnfCore` at the node (con-leche `CState.whnfCoreC`).  The depth is
    /// NOT in the key: a handle carries its own typing context, because an
    /// `fvar` node carries its type (DESIGN.md §8.3, "Free variables").
    pub whnf_core_c: HashMap<EIdx, EIdx>,
    pub whnf_core_j: Vec<EIdx>,
    /// The full reduction loop at the node (`CState.whnfC`).
    pub whnf_c: HashMap<EIdx, EIdx>,
    pub whnf_j: Vec<EIdx>,
    /// Full-grade inference (`CState.inferC`).
    pub infer_c: HashMap<EIdx, EIdx>,
    pub infer_j: Vec<EIdx>,
    /// **The io grade's own table** (`CState.inferIOC`): a hit here never
    /// serves a full-`infer` query, and a full-`infer` hit never serves this
    /// one.
    pub infer_io_c: HashMap<EIdx, EIdx>,
    pub infer_io_j: Vec<EIdx>,
    /// The annotation pass at the node (`CState.annotC`).
    pub annot_c: HashMap<EIdx, EIdx>,
    pub annot_j: Vec<EIdx>,
    /// Definitional equality at the ORDERED pair, with the verdict — both
    /// signs, as con-leche's `defeqC` stores them.
    pub defeq_c: HashMap<EIdxPair, bool>,
    pub defeq_j: Vec<EIdxPair>,
    /// `Level.isEquiv`'s verdict at a pair of level handles.
    pub lvl_eq_c: HashMap<LIdxPair, bool>,
    pub lvl_eq_j: Vec<LIdxPair>,
    /// `Level.isEquivList`'s verdict at a pair of universe-argument lists.
    pub lvls_eq_c: HashMap<LsIdxPair, bool>,
    pub lvls_eq_j: Vec<LsIdxPair>,
    /// A stored constant's TYPE at a universe instantiation.
    pub const_ty_c: HashMap<NLsKey, EIdx>,
    pub const_ty_j: Vec<NLsKey>,
    /// A stored definition's VALUE at a universe instantiation.
    pub const_val_c: HashMap<NLsKey, EIdx>,
    pub const_val_j: Vec<NLsKey>,
    /// An iota rule's right-hand side at the recursor's universe
    /// instantiation, keyed by the recursor, the rule's constructor and the
    /// levels — the three data that determine it.
    pub rule_rhs_c: HashMap<NNLsKey, EIdx>,
    pub rule_rhs_j: Vec<NNLsKey>,
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty` — the
/// empty cache set: what a fresh run and every capped table start from.
/// `ron::HashMap::new` allocates nothing (task #35), and so does
/// `Vec::new`, so eleven empty tables and eleven empty journals cost
/// twenty-two headers.
impl Caches {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty`.
    pub fn empty() -> Caches {
        Caches {
            whnf_core_c: HashMap::new(),
            whnf_core_j: Vec::new(),
            whnf_c: HashMap::new(),
            whnf_j: Vec::new(),
            infer_c: HashMap::new(),
            infer_j: Vec::new(),
            infer_io_c: HashMap::new(),
            infer_io_j: Vec::new(),
            annot_c: HashMap::new(),
            annot_j: Vec::new(),
            defeq_c: HashMap::new(),
            defeq_j: Vec::new(),
            lvl_eq_c: HashMap::new(),
            lvl_eq_j: Vec::new(),
            lvls_eq_c: HashMap::new(),
            lvls_eq_j: Vec::new(),
            const_ty_c: HashMap::new(),
            const_ty_j: Vec::new(),
            const_val_c: HashMap::new(),
            const_val_j: Vec::new(),
            rule_rhs_c: HashMap::new(),
            rule_rhs_j: Vec::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// The cap (`CoreState.lean:93-99`)
// ---------------------------------------------------------------------------

/// con-leche: none — DESIGN.md §8.3's cap (lesson 10, "a cap, not an eviction
/// policy"): a table that reaches this many entries is dropped whole.  Lean
/// twin: `proof/ConRon/Arena/CoreState.lean:99 cacheCap` — a top-level `def`
/// there so that the Rust is a `const` and the Lean never inlines a `Nat`
/// literal into a comparison (DESIGN.md §8.4, lesson 7).
pub const CACHE_CAP: usize = 4194304;

// ---------------------------------------------------------------------------
// The scratch-tier drop (`CoreState.lean:101-153`)
// ---------------------------------------------------------------------------

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:106-107 keepE` — a memo entry
/// survives the scratch tier exactly when BOTH its key and its value are
/// persistent handles.  One tier-bit test each, no denotation.
pub fn keep_e(k: &EIdx, v: &EIdx) -> bool {
    if k.is_persistent() {
        v.is_persistent()
    } else {
        false
    }
}

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:111-112 keepEE` — the `defeq`
/// table's survival test: both handles of the key are persistent (the value
/// is a `bool` and names no tier).
pub fn keep_ee(k: &EIdxPair, _v: bool) -> bool {
    if k.a.is_persistent() {
        k.b.is_persistent()
    } else {
        false
    }
}

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:115-116 keepLL` — the
/// level-verdict tables' survival test.
pub fn keep_ll(k: &LIdxPair, _v: bool) -> bool {
    if k.a.is_persistent() {
        k.b.is_persistent()
    } else {
        false
    }
}

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:119-120 keepLsLs` — the
/// level-list-verdict table's survival test.
pub fn keep_ls_ls(k: &LsIdxPair, _v: bool) -> bool {
    if k.a.is_persistent() {
        k.b.is_persistent()
    } else {
        false
    }
}

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:124-125 keepNLs` — the
/// instantiated-constant tables' survival test: the name, the
/// universe-argument list and the instantiated term.
pub fn keep_n_ls(k: &NLsKey, v: &EIdx) -> bool {
    if k.n.is_persistent() {
        if k.us.is_persistent() {
            v.is_persistent()
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: none — DESIGN.md §8.3, "Drop"
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:128-130 keepNNLs` —
/// `ruleRhsC`'s survival test.
pub fn keep_nn_ls(k: &NNLsKey, v: &EIdx) -> bool {
    if k.rec_name.is_persistent() {
        if k.ctor.is_persistent() {
            if k.us.is_persistent() {
                v.is_persistent()
            } else {
                false
            }
        } else {
            false
        }
    } else {
        false
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:142-153 Caches.dropScratchEntries`
/// — `Std.HashMap.filter keepE` over one handle-valued table, spelled as the
/// journal re-test the module note describes.  The journal is a superset of
/// the table's non-keepable keys, so removing exactly the keys that fail
/// `keep_e` *now* is the cited filter.
pub fn filter_e(m: &mut HashMap<EIdx, EIdx>, j: &Vec<EIdx>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_e(&j[i], v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_e(m, j, i + 1)
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:148 defeqC.filter keepEE`.
pub fn filter_ee(m: &mut HashMap<EIdxPair, bool>, j: &Vec<EIdxPair>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_ee(&j[i], *v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_ee(m, j, i + 1)
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:149 lvlEqC.filter keepLL`.
pub fn filter_ll(m: &mut HashMap<LIdxPair, bool>, j: &Vec<LIdxPair>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_ll(&j[i], *v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_ll(m, j, i + 1)
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:150 lvlsEqC.filter keepLsLs`.
pub fn filter_ls_ls(m: &mut HashMap<LsIdxPair, bool>, j: &Vec<LsIdxPair>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_ls_ls(&j[i], *v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_ls_ls(m, j, i + 1)
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:151-152 constTyC/constValC.filter keepNLs`.
pub fn filter_n_ls(m: &mut HashMap<NLsKey, EIdx>, j: &Vec<NLsKey>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_n_ls(&j[i], v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_n_ls(m, j, i + 1)
    }
}

/// con-leche: none — the journal walk behind `Caches::drop_scratch_entries`
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:153 ruleRhsC.filter keepNNLs`.
pub fn filter_nn_ls(m: &mut HashMap<NNLsKey, EIdx>, j: &Vec<NNLsKey>, i: usize) {
    if i >= j.len() {
        ()
    } else {
        let drop = match m.get(&j[i]) {
            Some(v) => !keep_nn_ls(&j[i], v),
            None => false,
        };
        if drop {
            let _ = m.remove(&j[i]);
        }
        filter_nn_ls(m, j, i + 1)
    }
}

/// con-leche: none — **the per-declaration bracket's cache half**
/// (DESIGN.md §8.3, "Drop")
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:142-153 Caches.dropScratchEntries`
/// — every entry whose key or value names a scratch handle goes with the
/// tier, everything persistent stays.  `arena::core::drop_scratch` calls this
/// beside `EStore::drop_scratch` at each declaration boundary, so that the
/// two halves of the drop are one operation on the state.
impl Caches {
    /// con-leche: none — DESIGN.md §8.3, "Drop"
    /// Lean twin: `proof/ConRon/Arena/CoreState.lean:142-153 Caches.dropScratchEntries`.
    pub fn drop_scratch_entries(&mut self) {
        filter_e(&mut self.whnf_core_c, &self.whnf_core_j, 0);
        self.whnf_core_j = Vec::new();
        filter_e(&mut self.whnf_c, &self.whnf_j, 0);
        self.whnf_j = Vec::new();
        filter_e(&mut self.infer_c, &self.infer_j, 0);
        self.infer_j = Vec::new();
        filter_e(&mut self.infer_io_c, &self.infer_io_j, 0);
        self.infer_io_j = Vec::new();
        filter_e(&mut self.annot_c, &self.annot_j, 0);
        self.annot_j = Vec::new();
        filter_ee(&mut self.defeq_c, &self.defeq_j, 0);
        self.defeq_j = Vec::new();
        filter_ll(&mut self.lvl_eq_c, &self.lvl_eq_j, 0);
        self.lvl_eq_j = Vec::new();
        filter_ls_ls(&mut self.lvls_eq_c, &self.lvls_eq_j, 0);
        self.lvls_eq_j = Vec::new();
        filter_n_ls(&mut self.const_ty_c, &self.const_ty_j, 0);
        self.const_ty_j = Vec::new();
        filter_n_ls(&mut self.const_val_c, &self.const_val_j, 0);
        self.const_val_j = Vec::new();
        filter_nn_ls(&mut self.rule_rhs_c, &self.rule_rhs_j, 0);
        self.rule_rhs_j = Vec::new();
    }
}
