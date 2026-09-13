//! con-leche: none — replaces `Std.HashMap`; no Lean source to cite.
//!
//! `ron::HashMap<K, V>` — the port's replacement for `Std.HashMap` (DESIGN.md
//! §3.3).  Aeneas has no model of `std::collections`, so the memo tables of
//! `ConLeche/Cached/StateC.lean` (`whnfC`, `inferC`, `instC`, …) are backed by
//! this map instead.
//!
//! Structure and naming follow the Aeneas tutorial's *verified* hash map,
//! `vendor/aeneas/tests/src/hashmap.rs`, whose proofs live in
//! `vendor/aeneas/tests/lean/Hashmap/Properties.lean`: chained buckets
//! (`AList`) over a `Vec` of slots, a `num_entries` counter, a `max_load`
//! threshold and a `saturated` flag.  Staying close to it is what lets that
//! proof strategy (the `slot_t_inv` / `al_v` / `lookup` development) transfer.
//!
//! Deviations from the tutorial's file, all forced by DESIGN.md §3.4:
//!
//! * every `while`/`loop` is an explicit index- or structure-carrying
//!   recursion (`allocate_slots`, `clear_slots`, `move_elements`,
//!   `list_get`, `list_insert`, `list_remove`, `pow2_at_least`);
//! * `remove` is a *by-value* list function returning `(AList, Option<V>)`
//!   instead of the tutorial's `&mut` walk, which needs an `unreachable!()`
//!   in an impossible arm (§3.4 forbids it);
//! * the map is generic in the key, through the two traits below, and
//!   `insert` has replace semantics (`Option<V>`), as `Std.HashMap.insert`
//!   does;
//! * bucket counts are powers of two and grow by doubling.
//!
//! **Lazy allocation** (task #35, a fifth deviation from the tutorial's file).
//! `new` allocates *nothing*: `slots` is the empty `Vec`, and the first
//! `insert` calls `ensure_slots` to put `MIN_CAPACITY` buckets there.  The
//! checker builds thousands of memo tables per declaration that never see an
//! insert — the `*Fast` walks' tables, `beq`'s pair memo, the per-record
//! `CState`s — and a 32-bucket array each made `HashMap::allocate_slots` 17 %
//! of `Init`'s instructions (task #34's profile).  `get`, `contains_key` and
//! `remove` therefore carry a `slots.len() == 0` guard: they answer `None`
//! without computing a bucket index (which would divide by zero), and `len`,
//! `is_empty` and `clear` are already correct on an empty `slots`.  This is
//! **not** a memo-policy change in the sense of DESIGN.md §3.1: the abstract
//! map of a fresh table is `∅` either way, so it is the same table
//! con-leche's `{}` denotes — exactly as `with_capacity`'s larger table is
//! (task #34's pre-sizing).  What it does change is the *model*: the
//! invariant of `ConRon/Refine/HashMap.lean` gained an unallocated case
//! (`Inv.pow2`/`Inv.min_cap` are now conditional on `0 < slots.length`).
//!
//! **The tail of a bucket is optional** (task #41, a sixth deviation from the
//! tutorial's file).  `AList::Cons`' third field is an
//! `Option<Box<AList<K, V>>>` where the tutorial's is a `Box<AList<K, V>>`.
//! The tutorial's shape ends every chain in `Cons(.., Box::new(Nil))`, i.e.
//! **one heap block per entry whose whole content is `Nil`** — the port's
//! single biggest port artefact by cycles: `core`'s profile spent 11 % of its
//! cycles allocating, freeing and walking those blocks (the index rebuild of
//! `fenv::mk_fenv_go` inserts ~176k of them per `fenv::dup`, and every memo
//! insert makes one).  With an optional tail a one-entry bucket allocates
//! nothing at all — the entry sits inline in the slot, as it already did —
//! and a chain of `m` entries costs `m - 1` blocks instead of `m`.  Nothing
//! else moves: the slot type, the bucket a key lands in, the order within a
//! bucket and the abstract map are all unchanged, and `Option<Box<T>>` is one
//! word (the null-pointer niche), so no type grew.  In the model the field is
//! `Option (AList K V)` (`Box` erases, §3.2), which makes `AList` a *nested*
//! inductive: `ConRon/Refine/HashMap.lean` therefore carries its own
//! induction principle `AList.recTail` (Lean's `induction` tactic declines a
//! nested type), and `alv` and the three `list_*` specs gained the third
//! case.  Measured on `core`: −10.1 % instructions, −11.3 % wall.
//!
//! **The bucket index is a mask** (task #41).  `bucket_index` is
//! `h & (n - 1)` where it was `h % n`.  `Inv` says a non-empty slot vector's
//! length is a power of two, and for those the two are the *same number* —
//! not merely the same bucket — so no key moves.  The proof did not need a
//! line: `ConRon/Refine/HashMap.lean` treats `bucket_index` as a black box
//! (`bucketAt`, "the proofs never look inside it"), the invariant says only
//! that a key sits where *this* function puts it, and the `i < len` a slot
//! access needs comes from the access having succeeded.  A 64-bit `div`
//! costs ~20 stalled cycles and sat on every `get`, `insert` and `remove` of
//! the hottest tables; measured on `core`: −0.8 % instructions, −2.3 % wall.
//! Both operations fail on `n = 0` (a division by zero there, an underflow
//! here), which is why the callers' `slots.len() == 0` guard stays.
//!
//! **Recursion depth.**  Nothing here recurses once per bucket: the three
//! walks over the slot vector (`allocate_slots`, `clear_slots`,
//! `move_elements`) split their index range in half, so they are `log2 n`
//! deep.  A linear walk overflows the stack in an unoptimised build well
//! before the 2^26 buckets a 32M-entry `instC` needs (measured: the
//! differential test at ~16k buckets did).  The per-bucket recursions
//! (`list_get`, `list_insert`, `list_remove`) are as deep as the bucket is
//! long, i.e. O(1) under any hash that spreads; the `differential_constant_hash`
//! test is the degenerate case and is deliberately kept small.
//!
//! No iteration API: con-leche never iterates a memo table.  `grep -n
//! "fold\|toList\|keys\|forM" ConLeche/Cached/*.lean ConLeche/Kernel/FEnv.lean`
//! finds only `List`/`Array` folds over declarations; the only memo-table
//! operations in the whole checker are `getElem?`, `insert`, one `size` (the
//! 32M `instCCapC` cap, `Cached/StateC.lean:197`) and a reset to `{}`.

use std::vec::Vec;

/// The hash of a key.  The hash word of a `Name`/`Level`/`ExprC` is stored in
/// the node (DESIGN.md §3.2), so this is a field read, not a traversal.
pub trait Hashable {
    fn hash64(&self) -> u64;
}

/// Key equality.  Deliberately *our own* trait rather than
/// `core::cmp::PartialEq`: Aeneas models `PartialEq` as a two-parameter,
/// two-method structure (`core.cmp.PartialEq Self Rhs` with `eq` and `ne`,
/// `Aeneas/Std/Core/Cmp.lean:12`), `#[derive(PartialEq)]` additionally emits a
/// `core::marker::StructuralPartialEq` impl, and the derived `eq` for the real
/// key types would descend into `P` and `Vec` through std impls we would then
/// have to model.  `Eq2` is a one-parameter, one-method structure whose
/// instance we write ourselves — including the pointer/hash fast paths of
/// §3.2.  (Measured on a spike: `Eq2 K` + `Eq2Inst.eq2` versus
/// `core.cmp.PartialEq K K` + `corecmpPartialEqInst.eq` plus a
/// `StructuralPartialEq` instance item per key type.)
pub trait Eq2 {
    fn eq2(&self, other: &Self) -> bool;
}

impl Hashable for u64 {
    /// Identity: `u64` keys are already hashes (the stored hash words).
    fn hash64(&self) -> u64 {
        *self
    }
}

impl Eq2 for u64 {
    fn eq2(&self, other: &Self) -> bool {
        *self == *other
    }
}

/// A bucket: an association list whose **tail is optional**, so that a
/// one-entry bucket owns no heap block at all (the module note has the
/// measurement; the tutorial's `Box<AList<K, V>>` ends every chain in a block
/// holding `Nil`).  `Nil` is still the empty bucket, which lives inline in
/// the slot vector.
/// Source: `vendor/aeneas/tests/src/hashmap.rs:24` (`AList`).
pub enum AList<K, V> {
    Cons(K, V, Option<Box<AList<K, V>>>),
    Nil,
}

/// A hash map with chained buckets.  Invariants (the Lean side of them is
/// `ConRon/Refine/HashMap.lean`'s `Inv`): `slots.len()` is *either zero* — the
/// unallocated table `new` returns, see the note on lazy allocation at the top
/// of the file — or a power of two and at least `MIN_CAPACITY`; every key sits
/// in the bucket its hash selects; keys are pairwise distinct; `num_entries`
/// is the total number of pairs.
/// Source: `vendor/aeneas/tests/src/hashmap.rs:46` (`HashMap`).
pub struct HashMap<K, V> {
    /// The number of entries in the table.
    num_entries: usize,
    /// `num_entries > max_load` triggers a resize.
    max_load: usize,
    /// `true` once the table cannot grow any further.
    saturated: bool,
    /// The buckets; `slots.len()` is a power of two.
    slots: Vec<AList<K, V>>,
}

/// The smallest *allocated* bucket count (`new`'s table has none at all; see
/// the note on lazy allocation at the top of the file).  A power of two, and a
/// multiple of `LOAD_DEN`, so `max_load_for` never rounds.
const MIN_CAPACITY: usize = 32;

/// The load factor, `LOAD_NUM / LOAD_DEN` = 3/4.
const LOAD_NUM: usize = 3;
const LOAD_DEN: usize = 4;

/// Fuel for `pow2_at_least`: a `usize` has at most 64 bits, so doubling from
/// `MIN_CAPACITY` reaches the maximum in fewer than this many steps.
const POW2_FUEL: usize = 64;

/// The bucket a hash selects, among `n` buckets (`n > 0`, a power of two).
///
/// `h & (n - 1)` is `h % n` for a power-of-two `n` (the module note has the
/// measurement that replaced the `%`), and `Inv` gives every allocated table
/// that shape — though the proof never needs the equation: it reads this
/// function only through itself.  The callers' `slots.len() == 0` guard is
/// what keeps `n - 1` from underflowing, as it kept `%` from dividing by
/// zero.
///
/// Both casts are exact: `n as u64` widens (a `usize` has at most 64 bits)
/// and `h & (n as u64 - 1) < n <= usize::MAX`, so the truncation back to
/// `usize` is the identity.  Computing `(h as usize) & (n - 1)` instead would
/// need "`n` is a power of two dividing `2^usize::BITS`" to say the same
/// thing.
fn bucket_index(h: u64, n: usize) -> usize {
    let n64 = n as u64;
    let i = h & (n64 - 1);
    i as usize
}

/// The resize threshold for a given bucket count.  `capacity` is a power of
/// two and at least `MIN_CAPACITY`, hence a multiple of `LOAD_DEN`, so
/// dividing first is exact and cannot overflow.
fn max_load_for(capacity: usize) -> usize {
    let q = capacity / LOAD_DEN;
    q * LOAD_NUM
}

/// The smallest power of two that is `>= n`, starting from `cap` (itself a
/// power of two) and doubling.  Saturates instead of overflowing.
/// Replaces the `while` a `n.next_power_of_two()` would be.
fn pow2_at_least(n: usize, cap: usize, fuel: usize) -> usize {
    if fuel == 0 {
        cap
    } else if cap >= n {
        cap
    } else if cap > usize::MAX / 2 {
        cap
    } else {
        pow2_at_least(n, cap * 2, fuel - 1)
    }
}

/// Look a key up in a bucket.
/// Source: `vendor/aeneas/tests/src/hashmap.rs:236` (`get_in_list`).
fn list_get<'a, K, V>(ls: &'a AList<K, V>, key: &K) -> Option<&'a V>
where
    K: Eq2,
{
    match ls {
        AList::Nil => None,
        AList::Cons(ckey, cvalue, tl) => {
            if ckey.eq2(key) {
                Some(cvalue)
            } else {
                match tl {
                    None => None,
                    Some(b) => list_get(&**b, key),
                }
            }
        }
    }
}

/// Insert into a bucket, replacing an existing binding and returning the old
/// value (`None` means a pair was added, so the caller bumps the counter).
/// Source: `vendor/aeneas/tests/src/hashmap.rs:110` (`insert_in_list`).
fn list_insert<K, V>(ls: &mut AList<K, V>, key: K, value: V) -> Option<V>
where
    K: Eq2,
{
    match ls {
        AList::Nil => {
            *ls = AList::Cons(key, value, None);
            None
        }
        AList::Cons(ckey, cvalue, tl) => {
            if ckey.eq2(&key) {
                let old = core::mem::replace(cvalue, value);
                Some(old)
            } else {
                match tl {
                    None => {
                        *tl = Some(Box::new(AList::Cons(key, value, None)));
                        None
                    }
                    Some(b) => list_insert(&mut **b, key, value),
                }
            }
        }
    }
}

/// Remove a key from a bucket: returns the bucket without it and the value.
/// With the optional tail (task #41) the found-entry arm hands back the tail
/// itself (`Nil` if there is none), and the walk arm rebuilds the node around
/// the shortened rest — which may be `Cons(.., Some(Nil))`, a shape `alv`
/// does not distinguish from `Cons(.., None)`; nothing normalises it, because
/// the checker never removes (see the note on the missing iteration API).
/// Taken and returned by value, unlike
/// `vendor/aeneas/tests/src/hashmap.rs:265` (`remove_from_list`), whose
/// `&mut` walk needs `std::mem::replace` and an `unreachable!()` arm.
fn list_remove<K, V>(ls: AList<K, V>, key: &K) -> (AList<K, V>, Option<V>)
where
    K: Eq2,
{
    match ls {
        AList::Nil => (AList::Nil, None),
        AList::Cons(ckey, cvalue, tl) => {
            if ckey.eq2(key) {
                match tl {
                    None => (AList::Nil, Some(cvalue)),
                    Some(b) => (*b, Some(cvalue)),
                }
            } else {
                match tl {
                    None => (AList::Cons(ckey, cvalue, None), None),
                    Some(b) => {
                        let (rest, removed) = list_remove(*b, key);
                        (AList::Cons(ckey, cvalue, Some(Box::new(rest))), removed)
                    }
                }
            }
        }
    }
}

impl<K, V> HashMap<K, V> {
    /// Push `n` empty buckets onto `slots`.  Split in half rather than
    /// peeled one at a time, so the recursion is `log2 n` deep: a bucket
    /// count of 2^26 would otherwise blow the stack in an unoptimised build
    /// (see the note on recursion depth at the top of the file).
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:62` (`allocate_slots`).
    fn allocate_slots(mut slots: Vec<AList<K, V>>, n: usize) -> Vec<AList<K, V>> {
        if n == 0 {
            slots
        } else if n == 1 {
            slots.push(AList::Nil);
            slots
        } else {
            let half = n / 2;
            let slots = HashMap::allocate_slots(slots, half);
            HashMap::allocate_slots(slots, n - half)
        }
    }

    /// A fresh table with exactly `capacity` buckets; `capacity` must be a
    /// power of two `>= MIN_CAPACITY`.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:71` (`new_with_capacity`).
    fn new_with_capacity_pow2(capacity: usize) -> HashMap<K, V> {
        let slots = HashMap::allocate_slots(Vec::with_capacity(capacity), capacity);
        HashMap {
            num_entries: 0,
            max_load: max_load_for(capacity),
            saturated: false,
            slots,
        }
    }

    /// An empty map that has **not allocated its buckets yet**: `slots` is the
    /// empty `Vec`, and the first `insert` calls `ensure_slots` (task #35).
    /// Unlike the tutorial's `new`, this allocates nothing at all — the
    /// checker creates thousands of memo tables per declaration that never see
    /// an insert (`*Fast` walks, `beq`'s pair memo, the per-record `CState`s),
    /// and a `MIN_CAPACITY` bucket array each was 17 % of `Init`'s
    /// `allocate_slots` bill.  The abstract map is `∅` either way, so this is
    /// not a memo-policy change (DESIGN.md §3.1).
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:85` (`new`).
    pub fn new() -> HashMap<K, V> {
        HashMap {
            num_entries: 0,
            max_load: 0,
            saturated: false,
            slots: Vec::new(),
        }
    }

    /// Give an unallocated table (`new`'s) its initial `MIN_CAPACITY` buckets;
    /// a no-op on a table that already has some.  Called by `insert`, which is
    /// the only operation that needs a bucket to write into: `get`,
    /// `contains_key` and `remove` answer `None` on an unallocated table
    /// without touching `slots`.
    /// Source: none in the tutorial's file (it allocates in `new`).
    fn ensure_slots(&mut self) {
        if self.slots.len() == 0 {
            let table = HashMap::new_with_capacity_pow2(MIN_CAPACITY);
            self.max_load = table.max_load;
            self.slots = table.slots;
        }
    }

    /// An empty map sized so that `capacity` buckets are available (rounded
    /// up to a power of two, at least `MIN_CAPACITY`).
    pub fn with_capacity(capacity: usize) -> HashMap<K, V> {
        let c = pow2_at_least(capacity, MIN_CAPACITY, POW2_FUEL);
        HashMap::new_with_capacity_pow2(c)
    }

    /// The number of entries.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:105` (`len`).
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// Whether the map holds no entry.
    pub fn is_empty(&self) -> bool {
        self.num_entries == 0
    }

    /// Empty every bucket, keeping the allocation.  This is con-leche's
    /// `{ s with instC := {} }` (`Cached/StateC.lean:196`).
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:95` (`clear`).
    pub fn clear(&mut self) {
        self.num_entries = 0;
        let n = self.slots.len();
        HashMap::clear_slots(&mut self.slots, 0, n);
    }

    /// `clear`'s bucket walk over `[lo, hi)`, halving (see `allocate_slots`).
    fn clear_slots(slots: &mut Vec<AList<K, V>>, lo: usize, hi: usize) {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                slots[lo] = AList::Nil
            } else {
                let mid = lo + n / 2;
                HashMap::clear_slots(slots, lo, mid);
                HashMap::clear_slots(slots, mid, hi)
            }
        }
    }
}

impl<K, V> HashMap<K, V>
where
    K: Hashable + Eq2,
{
    /// The value bound to `key`, if any.  The guard is the unallocated table
    /// of `new`: it binds nothing, and `bucket_index` would divide by zero.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:248` (`get`).
    pub fn get(&self, key: &K) -> Option<&V> {
        if self.slots.len() == 0 {
            None
        } else {
            let i = bucket_index(key.hash64(), self.slots.len());
            list_get(&self.slots[i], key)
        }
    }

    /// Whether `key` is bound.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:211` (`contains_key`).
    pub fn contains_key(&self, key: &K) -> bool {
        match self.get(key) {
            None => false,
            Some(_) => true,
        }
    }

    /// Bind `key` to `value`, returning the previous value if there was one.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:140` (`insert`).
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.ensure_slots();
        let old = self.insert_no_resize(key, value);
        if self.num_entries > self.max_load {
            if !self.saturated {
                self.try_resize()
            }
        }
        old
    }

    /// `insert` without the load check.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:129` (`insert_no_resize`).
    fn insert_no_resize(&mut self, key: K, value: V) -> Option<V> {
        let i = bucket_index(key.hash64(), self.slots.len());
        let old = list_insert(&mut self.slots[i], key, value);
        match old {
            None => {
                self.num_entries += 1;
                None
            }
            Some(v) => Some(v),
        }
    }

    /// Double the bucket count and rehash, or mark the table saturated.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:151` (`try_resize`).
    fn try_resize(&mut self) {
        let capacity = self.slots.len();
        if capacity <= usize::MAX / 2 {
            let mut ntable = HashMap::new_with_capacity_pow2(capacity * 2);
            HashMap::move_elements(&mut ntable, &mut self.slots, 0, capacity);
            self.max_load = ntable.max_load;
            self.slots = ntable.slots;
        } else {
            self.saturated = true;
        }
    }

    /// Move the buckets `[lo, hi)` into `ntable`, halving (see
    /// `allocate_slots`).
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:174` (`move_elements`).
    fn move_elements(
        ntable: &mut HashMap<K, V>,
        slots: &mut Vec<AList<K, V>>,
        lo: usize,
        hi: usize,
    ) {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let ls = core::mem::replace(&mut slots[lo], AList::Nil);
                HashMap::move_elements_from_list(ntable, ls)
            } else {
                let mid = lo + n / 2;
                HashMap::move_elements(ntable, slots, lo, mid);
                HashMap::move_elements(ntable, slots, mid, hi)
            }
        }
    }

    /// Move one bucket's pairs into `ntable`.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:187`
    /// (`move_elements_from_list`).
    fn move_elements_from_list(ntable: &mut HashMap<K, V>, ls: AList<K, V>) {
        match ls {
            AList::Nil => (),
            AList::Cons(k, v, tl) => {
                let _ = ntable.insert_no_resize(k, v);
                match tl {
                    None => (),
                    Some(bx) => HashMap::move_elements_from_list(ntable, *bx),
                }
            }
        }
    }

    /// Unbind `key`, returning the value it was bound to.  The guard is
    /// `get`'s: an unallocated table binds nothing.
    /// Source: `vendor/aeneas/tests/src/hashmap.rs:296` (`remove`).
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if self.slots.len() == 0 {
            None
        } else {
            let i = bucket_index(key.hash64(), self.slots.len());
            // One `&mut` on the slot, held across the call: indexing twice
            // would generate two `Vec.index_mut` round trips in the Lean.
            let slot = &mut self.slots[i];
            let ls = core::mem::replace(slot, AList::Nil);
            let (rest, removed) = list_remove(ls, key);
            *slot = rest;
            match removed {
                None => None,
                Some(v) => {
                    self.num_entries -= 1;
                    Some(v)
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Copying a table (task #67)
// ---------------------------------------------------------------------------
//
// `CheckerOps.orElse` (`ConLeche/Kernel/CheckerBase.lean:36-53`) continues its
// error arm from the **pre-attempt** state, `k (some e) s`: whatever memo
// entries the failed attempt wrote are discarded.  Lean gets that for free —
// `s` is a value — while the port threads one `&mut CState`, so it needs a
// snapshot to restore from, and a snapshot of a `CState` is a copy of its
// fourteen tables.  Since there is no iteration API (the module note), the
// copy is *structural*: the three scalar fields, then a rebuilt `slots`.

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// A value that can be copied into an independent one.  Deliberately our own
/// trait rather than `core::clone::Clone`, for `Eq2`'s reasons (see its doc
/// comment) and DESIGN.md §3.4's ban on `derive(Clone)` for the core types:
/// the copy of a `Name`/`Level`/`Expr` is the `P` bump `kernel::name::dup` and
/// friends already spell, and nothing here may descend into a node.
///
/// The method is `dup2`, not `dup`, so that it never collides with the
/// free-function `dup`s the modules already export.
pub trait Dup {
    fn dup2(&self) -> Self;
}

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// A `u64` key or value (`instC`'s offset) is copied by reading it.
impl Dup for u64 {
    fn dup2(&self) -> u64 {
        *self
    }
}

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// The value type of `lnzC`, `eqvC` and `defeqC`.
impl Dup for bool {
    fn dup2(&self) -> bool {
        *self
    }
}

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// The pair keys of `constTyAt`, `constValAt`, `defeqC` and `eqvC`.  Charon
/// and Aeneas do take a user trait impl on a tuple type: the generated
/// instance is `Pair.Insts.<...>` applied to the component instances
/// (checked by the `dup-tuple` spike, retired at task #76).
impl<A: Dup, B: Dup> Dup for (A, B) {
    fn dup2(&self) -> (A, B) {
        (self.0.dup2(), self.1.dup2())
    }
}

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// The triple keys of `ruleRhsAt` and `instC`; `TupleABC.Insts.<...>` on the
/// Lean side.
impl<A: Dup, B: Dup, C: Dup> Dup for (A, B, C) {
    fn dup2(&self) -> (A, B, C) {
        (self.0.dup2(), self.1.dup2(), self.2.dup2())
    }
}

/// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
/// Copy one bucket, entry by entry, rebuilding the optional tail (task #41's
/// shape: a one-entry bucket allocates nothing).  As deep as the bucket is
/// long, i.e. `O(1)` under any hash that spreads — the same bound `list_get`
/// and `list_insert` run under.
fn dup_alist<K, V>(ls: &AList<K, V>) -> AList<K, V>
where
    K: Dup,
    V: Dup,
{
    match ls {
        AList::Nil => AList::Nil,
        AList::Cons(ckey, cvalue, tl) => match tl {
            None => AList::Cons(ckey.dup2(), cvalue.dup2(), None),
            Some(b) => {
                let rest = dup_alist(&**b);
                AList::Cons(ckey.dup2(), cvalue.dup2(), Some(Box::new(rest)))
            }
        },
    }
}

impl<K, V> HashMap<K, V>
where
    K: Dup,
    V: Dup,
{
    /// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
    /// A copy of the table that shares nothing with it: inserting into one
    /// leaves the other alone.  The three scalar fields are carried over and
    /// the buckets are rebuilt in place, so the copy has the same capacity,
    /// the same load threshold and every key in the same bucket — it is the
    /// same table, not merely the same abstract map.
    ///
    /// `O(size)`, like `kernel::fenv::dup`, and for the same reason: there is
    /// no iteration API to be cleverer with.  That is affordable because the
    /// caller — the snapshot `CheckerOps.orElse` restores from
    /// (`ConLeche/Kernel/CheckerBase.lean:36-53`) — runs at most once per
    /// Nat-op pin variant attempt, a handful of times per run.
    pub fn dup(&self) -> HashMap<K, V> {
        let n = self.slots.len();
        let slots = HashMap::dup_slots(&self.slots, Vec::with_capacity(n), 0, n);
        HashMap {
            num_entries: self.num_entries,
            max_load: self.max_load,
            saturated: self.saturated,
            slots,
        }
    }

    /// con-leche: none — the `dup` of a memo table; Lean's value semantics hides it
    /// `dup`'s bucket walk over `[lo, hi)`, pushing the copies onto `out` in
    /// index order.  Halved rather than peeled one at a time, so the
    /// recursion is `log2 n` deep and a 2^26-bucket `instC` does not blow the
    /// stack (see `allocate_slots` and the note on recursion depth at the top
    /// of the file); the left half is copied first, which is what keeps the
    /// pushes in order.  The accumulator is passed by value and returned
    /// (task #6's rule).
    fn dup_slots(
        src: &Vec<AList<K, V>>,
        out: Vec<AList<K, V>>,
        lo: usize,
        hi: usize,
    ) -> Vec<AList<K, V>> {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let mut out = out;
                out.push(dup_alist(&src[lo]));
                out
            } else {
                let mid = lo + n / 2;
                let out = HashMap::dup_slots(src, out, lo, mid);
                HashMap::dup_slots(src, out, mid, hi)
            }
        } else {
            out
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// xorshift64, so the differential runs are reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
    }

    /// A key whose hash is a constant: every entry lands in bucket 0.
    #[derive(Clone, Copy)]
    struct Bad(u64);

    impl Hashable for Bad {
        fn hash64(&self) -> u64 {
            0
        }
    }

    impl Eq2 for Bad {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    /// A key whose hash only has four values.
    #[derive(Clone, Copy)]
    struct Coarse(u64);

    impl Hashable for Coarse {
        fn hash64(&self) -> u64 {
            self.0 & 3
        }
    }

    impl Eq2 for Coarse {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    /// The oracle: an association list, newest binding kept in place.
    struct Oracle(Vec<(u64, u64)>);

    impl Oracle {
        fn new() -> Oracle {
            Oracle(Vec::new())
        }

        fn get(&self, k: u64) -> Option<u64> {
            for (ck, cv) in self.0.iter() {
                if *ck == k {
                    return Some(*cv);
                }
            }
            None
        }

        fn insert(&mut self, k: u64, v: u64) -> Option<u64> {
            for e in self.0.iter_mut() {
                if e.0 == k {
                    let old = e.1;
                    e.1 = v;
                    return Some(old);
                }
            }
            self.0.push((k, v));
            None
        }

        fn remove(&mut self, k: u64) -> Option<u64> {
            let mut i = 0;
            while i < self.0.len() {
                if self.0[i].0 == k {
                    let (_, v) = self.0.remove(i);
                    return Some(v);
                }
                i += 1;
            }
            None
        }

        fn len(&self) -> usize {
            self.0.len()
        }
    }

    #[test]
    fn basic_ops() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        assert!(m.is_empty());
        assert_eq!(m.len(), 0);
        assert_eq!(m.get(&7), None);
        assert!(!m.contains_key(&7));

        assert_eq!(m.insert(7, 70), None);
        assert_eq!(m.insert(8, 80), None);
        assert_eq!(m.len(), 2);
        assert!(!m.is_empty());
        assert_eq!(m.get(&7), Some(&70));
        assert!(m.contains_key(&8));

        // Replace semantics.
        assert_eq!(m.insert(7, 71), Some(70));
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&7), Some(&71));

        assert_eq!(m.remove(&7), Some(71));
        assert_eq!(m.remove(&7), None);
        assert_eq!(m.len(), 1);

        m.clear();
        assert!(m.is_empty());
        assert_eq!(m.get(&8), None);

        // Usable after a clear.
        assert_eq!(m.insert(8, 81), None);
        assert_eq!(m.get(&8), Some(&81));
    }

    /// Task #35: `new` allocates no buckets, every read answers on the empty
    /// `slots`, and the first `insert` is what allocates.
    #[test]
    fn new_allocates_nothing_and_insert_allocates() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        assert_eq!(m.slots.len(), 0);
        // Reads and removes on an unallocated table.
        assert_eq!(m.get(&7), None);
        assert!(!m.contains_key(&7));
        assert_eq!(m.remove(&7), None);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        // `clear` keeps it unallocated.
        m.clear();
        assert_eq!(m.slots.len(), 0);
        assert!(m.is_empty());
        assert_eq!(m.get(&7), None);
        // The first insert allocates, and the table then behaves as before.
        assert_eq!(m.insert(7, 70), None);
        assert_eq!(m.slots.len(), MIN_CAPACITY);
        assert_eq!(m.max_load, max_load_for(MIN_CAPACITY));
        assert_eq!(m.get(&7), Some(&70));
        assert_eq!(m.len(), 1);
        // A second insert does not reallocate.
        assert_eq!(m.insert(8, 80), None);
        assert_eq!(m.slots.len(), MIN_CAPACITY);
        // `clear` on an allocated table keeps the allocation (con-leche's
        // `{ s with instC := {} }`).
        m.clear();
        assert_eq!(m.slots.len(), MIN_CAPACITY);
        assert!(m.is_empty());
        // `with_capacity` still allocates eagerly.
        let w: HashMap<u64, u64> = HashMap::with_capacity(100);
        assert_eq!(w.slots.len(), 128);
    }

    #[test]
    fn with_capacity_rounds_up_to_a_power_of_two() {
        // Small requests keep the minimum.
        let m: HashMap<u64, u64> = HashMap::with_capacity(0);
        assert_eq!(m.slots.len(), MIN_CAPACITY);
        let m: HashMap<u64, u64> = HashMap::with_capacity(32);
        assert_eq!(m.slots.len(), 32);
        let m: HashMap<u64, u64> = HashMap::with_capacity(33);
        assert_eq!(m.slots.len(), 64);
        let m: HashMap<u64, u64> = HashMap::with_capacity(1000);
        assert_eq!(m.slots.len(), 1024);
        // Saturation instead of overflow (checked on the pure function: a
        // table that big cannot be allocated).
        let c = pow2_at_least(usize::MAX, MIN_CAPACITY, POW2_FUEL);
        assert!(c.is_power_of_two());
        assert!(c > usize::MAX / 2);
        assert_eq!(pow2_at_least(usize::MAX, MIN_CAPACITY, 0), MIN_CAPACITY);
    }

    #[test]
    fn growth_rehashes_and_keeps_every_binding() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        let n: u64 = 4000;
        let mut i: u64 = 0;
        while i < n {
            assert_eq!(m.insert(i * 37, i), None);
            i += 1;
        }
        assert_eq!(m.len(), n as usize);
        assert!(m.slots.len() > MIN_CAPACITY);
        assert!(m.slots.len().is_power_of_two());
        // Load factor respected.
        assert!(m.len() <= max_load_for(m.slots.len()));
        let mut i: u64 = 0;
        while i < n {
            assert_eq!(m.get(&(i * 37)), Some(&i));
            i += 1;
        }
        assert_eq!(m.get(&1), None);
    }

    /// Thousands of random operations on `HashMap<u64, u64>` against the
    /// association-list oracle.  `key_space` controls collision pressure and
    /// hit rate; `n` drives the table well past several growths.
    fn differential_u64(seed: u64, n: usize, key_space: u64, clear_every: usize) {
        let mut rng = Rng(seed);
        let mut m: HashMap<u64, u64> = HashMap::new();
        let mut o = Oracle::new();
        let mut step = 0;
        while step < n {
            let k = rng.next() % key_space;
            let v = rng.next();
            match rng.next() % 8 {
                0 | 1 | 2 | 3 => {
                    assert_eq!(m.insert(k, v), o.insert(k, v), "insert {k} at step {step}");
                }
                4 | 5 => {
                    assert_eq!(m.remove(&k), o.remove(k), "remove {k} at step {step}");
                }
                6 => {
                    assert_eq!(m.get(&k).copied(), o.get(k), "get {k} at step {step}");
                    assert_eq!(m.contains_key(&k), o.get(k).is_some());
                }
                _ => {
                    assert_eq!(m.len(), o.len(), "len at step {step}");
                    assert_eq!(m.is_empty(), o.len() == 0);
                }
            }
            assert_eq!(m.len(), o.len(), "len after step {step}");
            if clear_every != 0 {
                if step % clear_every == clear_every - 1 {
                    m.clear();
                    o = Oracle::new();
                    assert!(m.is_empty());
                }
            }
            step += 1;
        }
        // Final full comparison, both directions.
        let mut k = 0;
        while k < key_space {
            assert_eq!(m.get(&k).copied(), o.get(k), "final get {k}");
            k += 1;
        }
        assert_eq!(m.len(), o.len());
    }

    #[test]
    fn differential_dense_keys() {
        differential_u64(0x2545F4914F6CDD1D, 20000, 500, 0);
    }

    #[test]
    fn differential_sparse_keys_with_growth() {
        differential_u64(0x9E3779B97F4A7C15, 20000, 200000, 0);
    }

    #[test]
    fn differential_with_clears() {
        differential_u64(0xDEADBEEFCAFEBABE, 20000, 300, 977);
    }

    /// The same run with a deliberately bad hash: every key hashes to 0, so
    /// the whole map is one bucket and every growth rehashes into it again.
    #[test]
    fn differential_constant_hash() {
        let mut rng = Rng(0x0123456789ABCDEF);
        let mut m: HashMap<Bad, u64> = HashMap::new();
        let mut o = Oracle::new();
        let mut step = 0;
        while step < 4000 {
            let k = rng.next() % 200;
            let v = rng.next();
            match rng.next() % 4 {
                0 | 1 => assert_eq!(m.insert(Bad(k), v), o.insert(k, v)),
                2 => assert_eq!(m.remove(&Bad(k)), o.remove(k)),
                _ => assert_eq!(m.get(&Bad(k)).copied(), o.get(k)),
            }
            assert_eq!(m.len(), o.len());
            step += 1;
        }
        let mut k = 0;
        while k < 200 {
            assert_eq!(m.get(&Bad(k)).copied(), o.get(k));
            k += 1;
        }
    }

    /// Four hash values: collisions plus real bucket spread.
    #[test]
    fn differential_coarse_hash() {
        let mut rng = Rng(0x1234_5678_9ABC_DEF0);
        let mut m: HashMap<Coarse, u64> = HashMap::new();
        let mut o = Oracle::new();
        let mut step = 0;
        while step < 8000 {
            let k = rng.next() % 1000;
            let v = rng.next();
            match rng.next() % 4 {
                0 | 1 => assert_eq!(m.insert(Coarse(k), v), o.insert(k, v)),
                2 => assert_eq!(m.remove(&Coarse(k)), o.remove(k)),
                _ => assert_eq!(m.get(&Coarse(k)).copied(), o.get(k)),
            }
            assert_eq!(m.len(), o.len());
            step += 1;
        }
        let mut k = 0;
        while k < 1000 {
            assert_eq!(m.get(&Coarse(k)).copied(), o.get(k));
            k += 1;
        }
    }

    #[test]
    fn remove_then_reinsert_across_a_growth() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        let mut i: u64 = 0;
        while i < 1000 {
            assert_eq!(m.insert(i, i), None);
            i += 1;
        }
        let mut i: u64 = 0;
        while i < 1000 {
            if i % 2 == 0 {
                assert_eq!(m.remove(&i), Some(i));
            }
            i += 1;
        }
        assert_eq!(m.len(), 500);
        let mut i: u64 = 0;
        while i < 1000 {
            if i % 2 == 0 {
                assert_eq!(m.get(&i), None);
                assert_eq!(m.insert(i, i + 1), None);
            } else {
                assert_eq!(m.get(&i), Some(&i));
            }
            i += 1;
        }
        assert_eq!(m.len(), 1000);
    }

    impl Dup for Bad {
        fn dup2(&self) -> Bad {
            Bad(self.0)
        }
    }

    /// `dup` of a populated table answers `get` exactly as the original does,
    /// for present and for absent keys, and reports the same `len`.
    #[test]
    fn dup_answers_get_the_same_way() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        let mut i: u64 = 0;
        while i < 500 {
            assert_eq!(m.insert(i, i * 3 + 1), None);
            i += 1;
        }
        let d = m.dup();
        assert_eq!(d.len(), m.len());
        let mut k: u64 = 0;
        while k < 1000 {
            assert_eq!(d.get(&k).copied(), m.get(&k).copied());
            k += 1;
        }
        // 500..1000 are the absent ones, and both tables say so.
        assert_eq!(d.get(&700), None);
    }

    /// A `dup` of an *unallocated* table (`new`'s, which owns no bucket) is
    /// itself empty and usable.
    #[test]
    fn dup_of_an_unallocated_table() {
        let m: HashMap<u64, u64> = HashMap::new();
        let mut d = m.dup();
        assert!(d.is_empty());
        assert_eq!(d.get(&3), None);
        assert_eq!(d.insert(3, 4), None);
        assert_eq!(d.get(&3), Some(&4));
        assert_eq!(m.get(&3), None);
    }

    /// The copy is independent: inserting into one leaves the other alone, in
    /// both directions, removals included.
    #[test]
    fn dup_is_independent_of_the_original() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        let mut i: u64 = 0;
        while i < 100 {
            assert_eq!(m.insert(i, i), None);
            i += 1;
        }
        let mut d = m.dup();
        assert_eq!(d.insert(1000, 7), None);
        assert_eq!(m.get(&1000), None);
        assert_eq!(m.len(), 100);
        assert_eq!(d.len(), 101);
        assert_eq!(m.insert(2000, 9), None);
        assert_eq!(d.get(&2000), None);
        assert_eq!(d.remove(&5), Some(5));
        assert_eq!(m.get(&5), Some(&5));
        assert_eq!(d.insert(0, 42), Some(0));
        assert_eq!(m.get(&0), Some(&0));
    }

    /// Chained buckets are copied node by node: with a constant hash every
    /// entry sits in bucket 0, so this is the one-long-`AList` case.
    #[test]
    fn dup_copies_a_chain() {
        let mut m: HashMap<Bad, u64> = HashMap::new();
        let mut i: u64 = 0;
        while i < 40 {
            assert_eq!(m.insert(Bad(i), i + 1), None);
            i += 1;
        }
        let mut d = m.dup();
        let mut i: u64 = 0;
        while i < 40 {
            assert_eq!(d.get(&Bad(i)), Some(&(i + 1)));
            i += 1;
        }
        assert_eq!(d.remove(&Bad(20)), Some(21));
        assert_eq!(m.get(&Bad(20)), Some(&21));
        assert_eq!(d.get(&Bad(20)), None);
    }

    /// The dictionaries a `(u64, u64)` test key needs; `CState`'s real tuple
    /// keys have theirs in `cached::state_c`.
    impl Hashable for (u64, u64) {
        fn hash64(&self) -> u64 {
            self.0.wrapping_mul(31).wrapping_add(self.1)
        }
    }

    impl Eq2 for (u64, u64) {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0 && self.1 == other.1
        }
    }

    /// A tuple key goes through the `Dup` impl on `(A, B)`; the map is a
    /// stand-in for `CState`'s five tuple-keyed tables.
    #[test]
    fn dup_with_a_tuple_key() {
        let mut m: HashMap<(u64, u64), bool> = HashMap::new();
        let mut i: u64 = 0;
        while i < 50 {
            assert_eq!(m.insert((i, i + 1), i % 2 == 0), None);
            i += 1;
        }
        let d = m.dup();
        let mut i: u64 = 0;
        while i < 50 {
            assert_eq!(d.get(&(i, i + 1)), Some(&(i % 2 == 0)));
            i += 1;
        }
        assert_eq!(d.get(&(3, 3)), None);
    }

    /// `dup` preserves the *shape*, not merely the abstract map: same entry
    /// count, same bucket count, and a table that keeps growing the same way.
    #[test]
    fn dup_preserves_the_capacity() {
        let mut m: HashMap<u64, u64> = HashMap::new();
        let mut i: u64 = 0;
        while i < 300 {
            assert_eq!(m.insert(i, i), None);
            i += 1;
        }
        let mut d = m.dup();
        assert_eq!(d.slots.len(), m.slots.len());
        assert_eq!(d.max_load, m.max_load);
        assert_eq!(d.saturated, m.saturated);
        assert_eq!(d.num_entries, m.num_entries);
        let mut i: u64 = 300;
        while i < 900 {
            assert_eq!(d.insert(i, i), None);
            assert_eq!(m.insert(i, i), None);
            i += 1;
        }
        assert_eq!(d.slots.len(), m.slots.len());
    }
}
