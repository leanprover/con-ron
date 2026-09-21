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
//! ## The one deviation from the twin, and it is the RESET
//!
//! The twin's per-declaration bracket assigns `Caches.empty`; the port calls
//! `Caches::reset`, which empties the eleven tables **in place**
//! (`reset_map`, below) and keeps their bucket arrays.  Same value, one
//! allocation fewer per declaration — task #97-P6-1's first lever, and the
//! reason is measured in `reset_map`'s own note.
//!
//! Until task #97-P6-1 each table also carried a **journal** of the keys
//! whose row was not keepable, so that `Caches::drop_scratch_entries` could
//! spell DESIGN.md §8.3's survivor policy with a `ron::HashMap` that has no
//! `retain`.  Task #97f replaced that policy with con-leche's own `flushC`
//! (the caches go whole at the declaration boundary), which left the journals
//! and the walk dead: eleven `Vec`s carried through every `astate_dup`, a
//! `keep_*` test and a `dup2` and a push per cache write, and no reader.
//! They are gone.  The survivor predicate itself stays below — `keep_e` and
//! its five siblings are the SPECIFICATION of a surviving row, which is what
//! P3 needs to state that flushing is sound (`flushed ⊑ dropScratchEntries`),
//! and the twin's `Caches.dropScratchEntries` is where it is stated.

use crate::arena::handle::{EIdx, LIdx, LsIdx, NIdx};
use con_ron_core::ron::hashmap::{Dup, Eq2, Hashable};
// The arena's tables are the epoch-stamped open-addressed map
// (DESIGN.md's `Task #97-P6-4b`), aliased so that every use site below
// reads as it did.  `ron::hashmap::HashMap` is still what `crates/con-ron`
// uses, and is still the one with proofs.
use con_ron_core::ron::hashmap2::HashMap2 as HashMap;
use con_ron_core::kernel::name;

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
pub struct Caches {
    /// `whnfCore` at the node (con-leche `CState.whnfCoreC`).  The depth is
    /// NOT in the key: a handle carries its own typing context, because an
    /// `fvar` node carries its type (DESIGN.md §8.3, "Free variables").
    pub whnf_core_c: HashMap<EIdx, EIdx>,
    /// The full reduction loop at the node (`CState.whnfC`).
    pub whnf_c: HashMap<EIdx, EIdx>,
    /// Full-grade inference (`CState.inferC`).
    pub infer_c: HashMap<EIdx, EIdx>,
    /// **The io grade's own table** (`CState.inferIOC`): a hit here never
    /// serves a full-`infer` query, and a full-`infer` hit never serves this
    /// one.
    pub infer_io_c: HashMap<EIdx, EIdx>,
    /// The annotation pass at the node (`CState.annotC`).
    pub annot_c: HashMap<EIdx, EIdx>,
    /// Definitional equality at the ORDERED pair, with the verdict — both
    /// signs, as con-leche's `defeqC` stores them.
    pub defeq_c: HashMap<EIdxPair, bool>,
    /// `Level.isEquiv`'s verdict at a pair of level handles.
    pub lvl_eq_c: HashMap<LIdxPair, bool>,
    /// `Level.isEquivList`'s verdict at a pair of universe-argument lists.
    pub lvls_eq_c: HashMap<LsIdxPair, bool>,
    /// A stored constant's TYPE at a universe instantiation.
    pub const_ty_c: HashMap<NLsKey, EIdx>,
    /// A stored definition's VALUE at a universe instantiation.
    pub const_val_c: HashMap<NLsKey, EIdx>,
    /// An iota rule's right-hand side at the recursor's universe
    /// instantiation, keyed by the recursor, the rule's constructor and the
    /// levels — the three data that determine it.
    pub rule_rhs_c: HashMap<NNLsKey, EIdx>,
}

/// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty` — the
/// empty cache set: what a fresh run and every capped table start from.
/// `ron::HashMap::new` allocates nothing (task #35), so eleven empty tables
/// cost eleven headers.  This is what a fresh run and every capped table
/// start from; the per-declaration flush is `Caches::reset` below, which
/// reaches the same value without freeing the buckets.
impl Caches {
    /// con-leche: ConLeche/Cached/StateC.lean:131-156 CState
    /// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty`.
    pub fn empty() -> Caches {
        Caches {
            whnf_core_c: HashMap::new(),
            whnf_c: HashMap::new(),
            infer_c: HashMap::new(),
            infer_io_c: HashMap::new(),
            annot_c: HashMap::new(),
            defeq_c: HashMap::new(),
            lvl_eq_c: HashMap::new(),
            lvls_eq_c: HashMap::new(),
            const_ty_c: HashMap::new(),
            const_val_c: HashMap::new(),
            rule_rhs_c: HashMap::new(),
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

// ---------------------------------------------------------------------------
// The per-declaration reset (`CoreState.lean:87-89 Caches.empty`), in place
// ---------------------------------------------------------------------------

/// con-leche: none — arena infrastructure (task #97-P6-1, rewritten by #97-P6-4b)
/// Lean twin: none — the RESULT is `Std.HashMap.empty`, which is what the
/// twin's `Caches.empty`/`Memos.empty` assign; this is a representation
/// choice with the same denotation (DESIGN.md §3.2).
///
/// **It is one line again, because the map's `clear` is O(1) now.**  The
/// checker empties these tables per declaration (`flush_caches`,
/// `enter_scratch`, `drop_scratch`) and per top-level call (`inst1_clear` and
/// its ten siblings) — 36 053 620 times on `Init`.  Against
/// `ron::hashmap`'s chained map that cost `O(capacity)` a call, and task
/// #97-P6-1 had to buy the lever back with three guards (leave an empty table
/// alone; hand the array back when the last round used less than a sixteenth
/// of it; and not below 64 buckets) to get −5.7 % out of it at all.
///
/// `ron::hashmap2::HashMap2::clear` is an **epoch bump** (DESIGN.md's `Task
/// #97-P6-4b`), so there is nothing left to weigh: the walk it used to save
/// does not exist, and the shrink it used to perform is now pure loss,
/// because giving the array back means allocating it again.  Measured on
/// `Init` with `HashMap2` underneath, the same binary either way:
///
/// | `reset_map` | instructions:u | cycles:u | wall |
/// |---|---:|---:|---:|
/// | task #97-P6-1's three guards | 642.16 G | 305.4 G | 69.4 / 69.6 s |
/// | **`m.clear()`** | **525.22 G** | 291.4 / 303.4 G | 66.2 / 69.0 s |
///
/// `RESET_KEEP_FLOOR` and `RESET_KEEP_SLACK` are gone with the guards; the
/// numbers task #97-P6-1's section records for them stand as the measurement
/// of the map they were measured against.
pub fn reset_map<K, V>(m: &mut HashMap<K, V>) {
    m.clear()
}

/// con-leche: ConLeche/Cached/StateC.lean:394-398 CState.flushed
/// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty` — the
/// per-declaration flush, as an in-place reset of the eleven tables rather
/// than eleven fresh records.  `Caches::empty` stays for `AState::init`.
impl Caches {
    /// con-leche: ConLeche/Cached/StateC.lean:394-398 CState.flushed
    /// Lean twin: `proof/ConRon/Arena/CoreState.lean:87-89 Caches.empty`.
    pub fn reset(&mut self) {
        reset_map(&mut self.whnf_core_c);
        reset_map(&mut self.whnf_c);
        reset_map(&mut self.infer_c);
        reset_map(&mut self.infer_io_c);
        reset_map(&mut self.annot_c);
        reset_map(&mut self.defeq_c);
        reset_map(&mut self.lvl_eq_c);
        reset_map(&mut self.lvls_eq_c);
        reset_map(&mut self.const_ty_c);
        reset_map(&mut self.const_val_c);
        reset_map(&mut self.rule_rhs_c)
    }
}
