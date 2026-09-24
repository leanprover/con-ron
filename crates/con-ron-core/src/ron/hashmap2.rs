//! con-leche: none — arena infrastructure; a second `Std.HashMap` replacement, unproved
//!
//! `ron::HashMap2<K, V>` — **PROOF OWED** (task #97-P6-4b, DESIGN.md
//! §8.6's P6 twin ledger).  The same abstract object as `ron::hashmap`'s
//! `HashMap` — a partial map from `K` to `V`, with `Hashable`/`Eq2`/`Dup` as
//! its dictionaries and the same eleven operations — over an **open-addressed,
//! epoch-stamped, flat slot vector** instead of the Aeneas tutorial's chained
//! buckets.  `ron::hashmap` is untouched and keeps its proofs
//! (`proof/ConRon/Refine/HashMap*.lean`); this module has **none**, and the
//! list of what it owes is in DESIGN.md's `Task #97-P6-4b` section.
//!
//! **Why it exists.**  Task #97-P6-1 left `clear_slots + allocate_slots +
//! move_elements*` at 21.8 % of `Init`, "all halving recursions over chained
//! buckets".  Task #97-P6-4b counted what those recursions actually do on
//! `Init`, and the counts name the representation rather than the code:
//!
//! | on `Init`, `ron::HashMap` | count |
//! |---|---:|
//! | `get` calls | 1 228 953 968 |
//! | — resolved in 0 or 1 chain step | 98.8 % |
//! | `insert` calls | 627 320 951 |
//! | **`clear` calls** | **36 053 620** |
//! | **— buckets walked by them** | **2 940 488 064** |
//! | — entries those buckets held | 586 917 896 |
//! | buckets pushed by `allocate_slots` | 948 184 512 |
//! | entries moved by `move_elements*` | 349 323 629 |
//!
//! So the chains are *already* short — the table is a good hash table — and
//! essentially all of the 21.8 % is the per-bucket cost of **emptying and
//! re-growing** the slot vector: 2.94 G bucket writes to clear 0.59 G entries
//! (five buckets walked per entry cleared; the average cleared table is 82
//! buckets holding 16 entries) and 0.95 G `Vec::push`es to allocate them back.
//! Nothing a better chain walk can do touches that.
//!
//! **The representation.**
//!
//! * `slots : Vec<Slot<K, V>>`, `Slot` = `Vacant | Live(u32, K, V)`.  No
//!   `Box`, no chain, no allocation per entry — an entry *is* a slot.
//! * A `Live` slot is **live only if its stamp is the table's `epoch`**;
//!   a `Live` slot with a stale stamp is free space, indistinguishable from
//!   `Vacant` to every operation.
//! * `clear` is therefore `epoch += 1`, **O(1)**, which is the whole point:
//!   it deletes the 2.94 G bucket writes outright.  The one bounded case is
//!   the wrap at `u32::MAX`, which vacates the slots the hard way and starts
//!   over — `Init` clears the hottest single table ~36 M times, so the wrap
//!   is four wraps' worth of headroom away and is there for totality, not for
//!   the profile.
//! * Collisions are resolved by **linear probing**: a probe reads slot
//!   `h & (n-1)`, then `+1` with wraparound, until it meets the key or a free
//!   slot.  Four 20-byte slots share a cache line, so a probe run of three is
//!   one cache miss, where a chain of three is three.
//! * `remove` is Knuth's algorithm R (backward-shift deletion), so there are
//!   **no tombstones** and the invariant stays "every live key is reachable
//!   from its home slot by a run of live slots".
//!
//! **What it costs in memory.**  A `Slot<AppNode, EIdx>` is 20 bytes (tag 4,
//! stamp 4, `AppNode` 8, `EIdx` 4) against `AList<AppNode, EIdx>`'s 24, and
//! there is no chain block; at the same 3/4 load factor that is 26.7 bytes per
//! entry against the 40.2 + ~8 task #97-P4a measured.
//!
//! **What it keeps.**  Every §3.4 rule: no loops (the probe, the repair, the
//! slot walks and the power-of-two search are recursions with explicit fuel),
//! no closures, no `?`, no `unsafe`, no `std::collections`, no `derive`, no
//! panic as control flow.  The API is `ron::hashmap::HashMap`'s, name for
//! name, so a table swaps by changing one type.
//!
//! **What it owes.**  `Refine/HashMap.lean`'s development transfers in shape
//! but not in text: `alv`/`al_v` are replaced by `sl_v` (the live slots, in
//! index order), `Inv` gains the run clause and the epoch clause, and the
//! eleven operation specs are re-proved against the *same* `toFun m k =
//! lookupK (sl_v m) k`.  Everything downstream of `toFun`/`Rel`/`RelOn` — the
//! whole of `State.lean`, `FEnv.lean`, `ExprOps.lean` and the frontend files —
//! is stated at the abstract map and does not move.

use std::vec::Vec;

use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// A slot of the flat table.  `Vacant` is a slot that has never been written;
/// `Live(g, k, v)` binds `k` to `v` **if and only if** `g` is the table's
/// current `epoch` — a stale stamp is free space that `clear` left behind.
///
/// The stamp is what makes `clear` O(1), and it is very nearly free: `Slot`
/// and `Option<(K, V)>` are the same 20 bytes for the arena's `app` cons
/// table, because the tag word is padded either way.
pub enum Slot<K, V> {
    Vacant,
    Live(u32, K, V),
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// An open-addressed hash map with linear probing and an epoch stamp.
///
/// Invariants (`proof/ConRon/Refine/HashMap2.lean`'s `Inv`, proved):
/// `slots.len()` is either zero — the unallocated table `new` returns, task
/// #35's lazy allocation, kept — or a power of two at least `MIN_CAPACITY`;
/// `epoch` is at least 1; every live key is reachable from its home slot by a
/// run of live slots with no free slot in between; live keys are pairwise
/// distinct; `num_entries` counts the live slots and is at most `max_load`
/// when an `insert` returns.
///
/// **That last clause is unconditional since task #97-P6-17.**  It used to
/// end "unless the table is `saturated`", and the exception was a port bug:
/// see `try_resize` and `is_saturated_full`.
pub struct HashMap2<K, V> {
    /// The number of live entries.
    num_entries: usize,
    /// `num_entries > max_load` triggers a resize.
    max_load: usize,
    /// The stamp a slot must carry to be live.  At least 1, so that the `0`
    /// an `allocate_slots` slot would carry can never be current.
    epoch: u32,
    /// con-leche: none — arena infrastructure (task #97-P6-7)
    /// **The decaying high-water mark of `num_entries`**, maintained by
    /// `clear_fit` alone and read by nothing else: the size the next round is
    /// expected to need.  It is not part of the map's abstract value (the
    /// map is `slots` and `epoch`); it is the capacity policy's one word of
    /// state.  See `clear_fit`.
    fit_hw: usize,
    /// The slots; `slots.len()` is a power of two.
    slots: Vec<Slot<K, V>>,
}

/// The smallest *allocated* slot count (`new`'s table has none at all).  A
/// power of two, and a multiple of `LOAD_DEN`, so `max_load_for` never rounds.
const MIN_CAPACITY: usize = 32;

/// The load factor, `LOAD_NUM / LOAD_DEN`.  Linear probing pays for load in
/// probe length — the expected unsuccessful probe is `(1 + 1/(1-a)^2)/2` — so
/// this is the one constant of the module that is a measurement and not a
/// definition; task #97-P6-4b's section has the curve.
const LOAD_NUM: usize = 3;
const LOAD_DEN: usize = 4;

/// Fuel for `pow2_at_least`: a `usize` has at most 64 bits.
const POW2_FUEL: usize = 64;

/// con-leche: none — arena infrastructure (task #97-P6-7)
/// `clear_fit`'s decay rate: the high-water mark loses a `FIT_DECAY`th of
/// itself at every round that does not renew it.  Eight (12.5 % a round) is
/// slow enough that a run of similar rounds keeps its table and fast enough
/// that a single outlier is forgotten in tens of rounds, not thousands.
/// Four (25 % a round) was measured on the prefix at `FIT_SLACK = 64` and is
/// worse on both columns: 2 380.82 G instructions and 1 139.61 G cycles
/// against eight's 2 349.17 G and 1 121.21 G.
const FIT_DECAY: usize = 8;

/// con-leche: none — arena infrastructure (task #97-P6-7)
/// How far above the mark a table may sit before `clear_fit` re-makes it.
/// A table that is too SMALL is always re-made, because the alternative is
/// `insert`'s doubling and moving inside the round; a table that is too big
/// is re-made only past this factor, which is what keeps the decay from
/// re-making at every power of two it crosses.  **Measured**, on the Mathlib
/// 25 % prefix, at `FIT_DECAY = 8`:
///
/// | `FIT_SLACK` | instructions:u | cycles:u | wall |
/// |---:|---:|---:|---:|
/// | (no `clear_fit` at all) | 2 294.04 G | 1 505.97 G | 351.7 s |
/// | 4 | 2 512.78 G | 1 246.10 G | 284.8 s |
/// | 16 | 2 406.29 G | 1 158.75 G | 263.5 s |
/// | **64** | **2 349.17 G** | **1 121.21 G** | **255.0 s** |
/// | 256 | 2 317.24 G | 1 191.00 G | 271.5 s |
///
/// Sixty-four is the minimum of the cycles and of the wall; past it the
/// tables stay oversized long enough to lose the cache again, and the
/// instruction count keeps falling because that is the re-makes going away.
const FIT_SLACK: usize = 64;

/// The largest stamp.  `clear` at this value vacates the slots and restarts
/// the epoch at 1 rather than overflowing (the crate builds with
/// `overflow-checks`, so the wrap must be explicit).
const EPOCH_MAX: u32 = 4294967295;

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// The home slot of a hash among `n` slots (`n > 0`, a power of two).
///
/// **The finalizer is not optional, and it is the one lesson of this module.**
/// `ron::hashmap::bucket_index` is a bare `h & (n - 1)` and can afford to be:
/// chaining does not care whether the keys crowd, because a crowded bucket is
/// one short list.  Linear probing cares enormously — a dense set of keys is a
/// single solid cluster, and every probe that lands inside it walks to its
/// end.  And the arena's hot keys are *maximally* dense by design: `Hashable
/// for EIdx` is nanoda's IDENTITY hasher (`Handle.lean:88`), so a handle's
/// hash is its word, one constructor's handles are a contiguous range of
/// indices, and several constructors' are several such ranges laid on top of
/// each other.  Measured on `Init`: without this multiply-xor the arena runs
/// **2 292 G instructions** against the chained map's 735 G, and 25 % of the
/// cycles are one `insert_no_resize` walking clusters; with it, the table
/// below.  The mask itself is `h % n` for a power-of-two `n`, as it is there,
/// and the callers' `len == 0` guard is what keeps `n - 1` from underflowing.
///
/// A *hash* is verdict-neutral (DESIGN.md §3.2: any function of the value
/// will do), and the refinement never looks inside this function — the owed
/// `Inv` says only that a key sits where *this* function puts it, exactly as
/// `ConRon/Refine/HashMap.lean`'s `bucketAt` does today.
fn home_index(h: u64, n: usize) -> usize {
    let m = h.wrapping_mul(0x9e3779b97f4a7c15);
    let x = m ^ (m >> 32);
    let n64 = n as u64;
    let i = x & (n64 - 1);
    i as usize
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// The next slot of a probe run, wrapping at the end.
fn next_index(i: usize, n: usize) -> usize {
    let j = i + 1;
    if j >= n {
        0
    } else {
        j
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// The resize threshold for a given slot count.  `capacity` is a power of two
/// and at least `MIN_CAPACITY`, hence a multiple of `LOAD_DEN`, so dividing
/// first is exact and cannot overflow.
fn max_load_for(capacity: usize) -> usize {
    let q = capacity / LOAD_DEN;
    q * LOAD_NUM
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// The smallest power of two that is `>= n`, starting from `cap` (itself a
/// power of two) and doubling.  Saturates instead of overflowing.
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

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// **The probe.**  Walk the run that starts at `i` and return `(at, found)`:
/// `found` says the key is live at `at`, and otherwise `at` is the first free
/// slot of the run — the slot an `insert` writes.
///
/// `fuel` is the slot count, which is enough because `num_entries <= max_load
/// < slots.len()`, so a run always ends in a free slot and the arm below
/// **cannot** be reached on a well-formed table — `probe_spec` discharges it
/// from `Inv.fit` (task #97-HM2 §2), and since task #97-P6-17 `Inv.fit` holds
/// of every table `insert` returns, with no saturation exception.  The
/// recursion is in tail position.
fn probe<K, V>(
    slots: &Vec<Slot<K, V>>,
    epoch: u32,
    key: &K,
    i: usize,
    n: usize,
    fuel: usize,
) -> (usize, bool)
where
    K: Eq2,
{
    if fuel == 0 {
        (i, false)
    } else {
        match &slots[i] {
            Slot::Vacant => (i, false),
            Slot::Live(g, ckey, _) => {
                if *g != epoch {
                    (i, false)
                } else if ckey.eq2(key) {
                    (i, true)
                } else {
                    probe(slots, epoch, key, next_index(i, n), n, fuel - 1)
                }
            }
        }
    }
}

/// con-leche: none — arena infrastructure (task #97-PERF-BULKFILL)
/// `core::clone::Clone` for `Slot`, which `Vec::resize`'s signature demands of
/// `allocate_slots`' filler, and **that filler is its one use**: it answers
/// `Vacant` for every slot, a `Live` one included, because a `Live` slot's key
/// and value have no generic copy (`dup_slot` is the real copy, and needs
/// `Dup`).  So it is not a copy of a `Live` slot, and nothing but
/// `allocate_slots` may call it.  No `#[derive]` (DESIGN.md §3.4).
impl<K, V> core::clone::Clone for Slot<K, V> {
    /// con-leche: none — arena infrastructure (task #97-PERF-BULKFILL)
    fn clone(&self) -> Slot<K, V> {
        Slot::Vacant
    }
}

impl<K, V> HashMap2<K, V> {
    /// con-leche: none — arena infrastructure (task #97-P6-4b, rewritten by #97-P6-7 and #97-PERF-BULKFILL)
    /// Append `n` `Vacant` slots to `slots`.
    ///
    /// **It is one `Vec::resize`** (task #97-PERF-BULKFILL).  It was a halving
    /// push recursion, then (task #97-P6-7) a halving recursion with a leaf of
    /// eight pushes; task #97-PERF-FRESH priced that at ~15 instructions a
    /// slot, 4.76 G of `Init`'s 212 G, where a bulk fill is a store loop.
    /// `Vec::resize` is modelled by Aeneas (`alloc.vec.Vec.resize`, with
    /// `resize_spec`); what it asks for is a `Clone` for the filler, and the
    /// `Clone` for `Slot` is exactly that filler copy — it needs no `Dup` of `K` or
    /// `V`, which three of this map's key and value types do not have.
    fn allocate_slots(mut slots: Vec<Slot<K, V>>, n: usize) -> Vec<Slot<K, V>> {
        let len: usize = slots.len() + n;
        slots.resize(len, Slot::Vacant);
        slots
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// A fresh table with exactly `capacity` slots; `capacity` must be a power
    /// of two `>= MIN_CAPACITY`.
    fn new_with_capacity_pow2(capacity: usize) -> HashMap2<K, V> {
        let slots = HashMap2::allocate_slots(Vec::with_capacity(capacity), capacity);
        HashMap2 {
            num_entries: 0,
            max_load: max_load_for(capacity),
            epoch: 1,
            fit_hw: 0,
            slots,
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// An empty map that has **not allocated its slots yet** (task #35's lazy
    /// allocation, kept: the checker builds thousands of tables per
    /// declaration that never see an insert).
    pub fn new() -> HashMap2<K, V> {
        HashMap2 {
            num_entries: 0,
            max_load: 0,
            epoch: 1,
            fit_hw: 0,
            slots: Vec::new(),
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// Give an unallocated table its initial `MIN_CAPACITY` slots; a no-op on
    /// a table that already has some.  The epoch is **not** reset: a table
    /// that was cleared before its first insert must not make its stale
    /// nothing live again (there is none, but the invariant is simpler this
    /// way).
    fn ensure_slots(&mut self) {
        if self.slots.len() == 0 {
            let table = HashMap2::new_with_capacity_pow2(MIN_CAPACITY);
            self.max_load = table.max_load;
            self.slots = table.slots;
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// An empty map sized so that `capacity` slots are available (rounded up
    /// to a power of two, at least `MIN_CAPACITY`).
    pub fn with_capacity(capacity: usize) -> HashMap2<K, V> {
        let c = pow2_at_least(capacity, MIN_CAPACITY, POW2_FUEL);
        HashMap2::new_with_capacity_pow2(c)
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// The number of entries.
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// Whether the map holds no entry.
    pub fn is_empty(&self) -> bool {
        self.num_entries == 0
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// How many slots the table has: `0` for the unallocated table `new`
    /// returns, a power of two `>= MIN_CAPACITY` otherwise.  The one
    /// representation query, as `ron::hashmap::HashMap::capacity` is — and
    /// here it has no caller at all in the arena, because `clear` is O(1) and
    /// `arena::core_state::reset_map`'s shrink guard has nothing to weigh.
    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// **Empty the table in O(1)**, keeping the allocation: bump the epoch,
    /// and every live slot becomes free space in the same instruction.  This
    /// is con-leche's `{ s with instC := {} }` (`Cached/StateC.lean:196`) and
    /// `ron::hashmap::HashMap::clear`'s abstract value.
    ///
    /// The wrap arm is the price of a `u32` stamp: at `EPOCH_MAX` the stamps
    /// are no longer distinguishable, so the slots are vacated the hard way
    /// and the epoch restarts.  It is `O(capacity)` and it happens once every
    /// 4.29 G clears of *one* table — `Init` does 36 M over all twenty-two.
    pub fn clear(&mut self) {
        self.num_entries = 0;
        if self.epoch >= EPOCH_MAX {
            let n = self.slots.len();
            HashMap2::vacate_slots(&mut self.slots, 0, n);
            self.epoch = 1
        } else {
            self.epoch = self.epoch + 1
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-7)
    /// **Empty the table and give the slots back when the round that just
    /// ended did not need them.**  Same abstract value as `clear` — the empty
    /// map — and the same value the caller's `:= ∅` assigns; what differs is
    /// the capacity the next round starts from, which is a representation
    /// choice and nothing else (DESIGN.md §3.2).
    ///
    /// **Why it exists.**  An epoch-stamped `clear` is `O(1)` but it is also
    /// a RATCHET: the slot vector keeps the high-water mark of the largest
    /// round the table has ever seen, for the rest of the run.  Task #97-P6-7
    /// measured what that costs on the Mathlib 25 % prefix, at the reset of
    /// each per-declaration and per-call table:
    ///
    /// | table | resets | avg capacity | avg entries |
    /// |---|---:|---:|---:|
    /// | `instantiate1`'s per-call memo | 201 021 604 | 98 184.6 | **7.84** |
    /// | `whnfCore`'s per-declaration memo | 478 530 | 216 049.9 | **344.71** |
    /// | `abstract1`'s per-call memo | 11 440 282 | 69 176.3 | 21.59 |
    /// | the scratch `lam` cons table | 310 227 | 1 384 140.1 | — |
    /// | the scratch `app` cons table | 310 227 | 1 226 970.6 | — |
    ///
    /// A table of 98 185 slots holding eight entries is 2.4 MB of DRAM per
    /// lookup: the home slot is a guaranteed cache miss and the eight entries
    /// never share a line.  Two thirds of the prefix's declarations met a
    /// `lam` cons table of 2^21 slots (42 MB).
    ///
    /// **The ratchet is set by a handful of outlier rounds**, which is why a
    /// cap would not do.  The same run's histogram of entries per round:
    ///
    /// | table | rounds with 0 entries | ≤ 126 | the largest round |
    /// |---|---:|---:|---:|
    /// | `instantiate1`'s memo | 63.3 % | 99.1 % | 65 534 |
    /// | the scratch `app` cons table | 2.5 % | 42.5 % | ~4 000 000 |
    /// | the scratch `lam` cons table | 26.9 % | 74.6 % | ~2 000 000 |
    ///
    /// ONE declaration of the prefix pushes four million `app` nodes, and the
    /// other 310 226 then probe a four-million-slot array.
    ///
    /// **The policy: size the next round to a DECAYING HIGH-WATER MARK.**
    /// `fit_hw` is `max(this round's entries, the previous mark less a
    /// `FIT_DECAY`th)`, and the table is re-made with `2 · fit_hw` slots
    /// rounded up to a power of two whenever that is not the size it already
    /// has.  Three properties, and each is a measurement of this task's:
    ///
    ///  * **the steady state neither grows nor shrinks** — a table sized to
    ///    twice its rounds' entries is at a quarter load, so `insert` never
    ///    resizes and `clear_fit` re-makes nothing: the common case is
    ///    `clear`'s epoch bump, as before;
    ///  * **an outlier decays instead of being cut** — sizing to the LAST
    ///    round's entries alone re-grows the table from 32 slots at every
    ///    round that is bigger than its predecessor, which is what the first
    ///    attempt did: `+60 % instructions` on the prefix, `allocate_slots`
    ///    and `move_slots` 21 % of the cycles.  At `FIT_DECAY = 8` an outlier
    ///    of four million decays to a thousand over about sixty rounds, in
    ///    eleven halvings whose total is four million pushed slots — once per
    ///    outlier, not once per round;
    ///  * **the growth is taken in one step, before the round starts** —
    ///    when the mark is above the current size the table is re-made LARGER
    ///    here, while it is empty, so `insert`'s doubling-and-moving does not
    ///    run inside the round at all.
    ///
    /// The unallocated table (`new`, task #35's lazy allocation) is left
    /// unallocated: a table that has never held anything must not be given
    /// slots by its own reset.
    pub fn clear_fit(&mut self) {
        let n: usize = self.slots.len();
        let used: usize = self.num_entries;
        let hw0: usize = self.fit_hw;
        let decayed: usize = hw0 - hw0 / FIT_DECAY;
        let hw: usize = if used > decayed { used } else { decayed };
        self.fit_hw = hw;
        let want: usize = pow2_at_least(hw + hw + 1, MIN_CAPACITY, POW2_FUEL);
        if n == 0 || (want <= n && n / FIT_SLACK <= want) {
            self.clear()
        } else {
            let table: HashMap2<K, V> = HashMap2::new_with_capacity_pow2(want);
            self.num_entries = 0;
            self.max_load = table.max_load;
            self.epoch = 1;
            self.slots = table.slots
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// The epoch wrap's slot walk over `[lo, hi)`, halving so the recursion is
    /// `log2 n` deep (as `allocate_slots` was before task #97-PERF-BULKFILL).
    fn vacate_slots(slots: &mut Vec<Slot<K, V>>, lo: usize, hi: usize) {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                slots[lo] = Slot::Vacant
            } else {
                let mid = lo + n / 2;
                HashMap2::vacate_slots(slots, lo, mid);
                HashMap2::vacate_slots(slots, mid, hi)
            }
        }
    }
}

impl<K, V> HashMap2<K, V>
where
    K: Hashable + Eq2,
{
    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// The value bound to `key`, if any.  The guard is the unallocated table
    /// of `new`: it binds nothing, and `home_index` would underflow.
    pub fn get(&self, key: &K) -> Option<&V> {
        let n = self.slots.len();
        if n == 0 {
            None
        } else {
            let i = home_index(key.hash64(), n);
            let r = probe(&self.slots, self.epoch, key, i, n, n);
            if r.1 {
                match &self.slots[r.0] {
                    Slot::Vacant => None,
                    Slot::Live(_, _, v) => Some(v),
                }
            } else {
                None
            }
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// Whether `key` is bound.
    pub fn contains_key(&self, key: &K) -> bool {
        match self.get(key) {
            None => false,
            Some(_) => true,
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b, amended by
    /// task #97-P6-17)
    /// Bind `key` to `value`, returning the previous value if there was one.
    ///
    /// **Precondition: `!self.is_saturated_full()`** — see there and
    /// `try_resize`.  It used to be `if !self.saturated { self.try_resize() }`
    /// here, i.e. an `insert` past the limit quietly went on writing into a
    /// full table; now the limit is the caller's to respect, and the one
    /// arithmetic step that cannot be taken past it — `capacity * 2` — is
    /// where the model stops.
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.ensure_slots();
        let old = self.insert_no_resize(key, value);
        if self.num_entries > self.max_load {
            self.try_resize()
        }
        old
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// **The table can take no further key**: it is at its load limit *and*
    /// its slot vector cannot double.  `insert` must not be called on such a
    /// table; the arena's cons tables test this (`Tbl::full`) and decline with
    /// `Native`, exactly as they decline at `IDX_CAP`.
    ///
    /// **Why it exists** (task #97-HM2 §4, DESIGN.md §3.5's "a strengthening
    /// that turns out false is a port bug; fix the Rust").  `try_resize` used
    /// to set a `saturated` flag when the slot count passed `usize::MAX / 2`,
    /// and `insert` then stopped resizing: `num_entries` could climb to
    /// `slots.len()`, `probe`'s `fuel == 0` arm became reachable, and an
    /// `insert` **overwrote a live entry**.  For a memo that is a lost cache
    /// row; for a cons table it is two handles denoting one term, which is
    /// exactly what §8.3 makes `denote`'s injectivity a *soundness*
    /// obligation about.  A silent drop is no better for the same reason.  So
    /// the flag is gone, `try_resize` always doubles, and the limit is a
    /// declared precondition with a query to test it.
    ///
    /// It needs a table of `2^63` slots (`2^63 · 20` bytes, 184 exabytes) and
    /// cannot be reached; what it buys is that the *model* has no such state
    /// at all — `try_resize`'s `capacity * 2` fails there, so every refinement
    /// lemma is about a table that could still grow and none of them carries
    /// the `2 * slots.len() <= usize::MAX` hypothesis any more.
    pub fn is_saturated_full(&self) -> bool {
        if self.num_entries < self.max_load {
            false
        } else {
            self.slots.len() > usize::MAX / 2
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// `insert` without the load check.  One probe decides both arms: the
    /// slot it returns is either the key's own or the first free slot of the
    /// run, and writing `Live(epoch, k, v)` there is correct in both cases.
    fn insert_no_resize(&mut self, key: K, value: V) -> Option<V> {
        let n = self.slots.len();
        let i = home_index(key.hash64(), n);
        let r = probe(&self.slots, self.epoch, &key, i, n, n);
        let e = self.epoch;
        let prev = core::mem::replace(&mut self.slots[r.0], Slot::Live(e, key, value));
        if r.1 {
            match prev {
                Slot::Vacant => None,
                Slot::Live(_, _, v) => Some(v),
            }
        } else {
            self.num_entries += 1;
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// **Write a new entry at the slot `find_slot` just returned**, and grow
    /// if that put the table past its load threshold.  The second half of the
    /// fused find-or-insert; see `find_slot`.
    ///
    /// **Preconditions**, both of them the caller's: `at` is the free slot
    /// `find_slot` returned for this very `key` on this very table, with no
    /// operation on the table in between; and `!self.is_saturated_full()`.
    /// Under them `find_slot` followed by `insert_at` is `insert` at a key the
    /// table does not hold — which is the equation `Refine/HashMap2.lean`'s
    /// `find_slot_insert_at` proves, and the reason the fused pair costs the
    /// specification one lemma rather than a second development.
    pub fn insert_at(&mut self, at: usize, key: K, value: V) {
        let e = self.epoch;
        self.slots[at] = Slot::Live(e, key, value);
        self.num_entries += 1;
        if self.num_entries > self.max_load {
            self.try_resize()
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b, amended by
    /// task #97-P6-17)
    /// Double the slot count and rehash.  The new table inherits the epoch, so
    /// the entries `move_slots` carries over are live in it and the stale ones
    /// are dropped on the floor — which is the only place the epoch scheme
    /// ever frees the memory a cleared entry held.
    ///
    /// **Unconditional since task #97-P6-17.**  The `else` arm used to set a
    /// `saturated` flag (`is_saturated_full`'s note has the bug that cost);
    /// what is left is `capacity * 2`, whose overflow is the module's limit —
    /// the same kind of limit `self.slots[i]`'s bound already is, discharged
    /// the same way, by the caller's precondition and by the invariant.
    fn try_resize(&mut self) {
        let capacity = self.slots.len();
        let mut ntable = HashMap2::new_with_capacity_pow2(capacity * 2);
        ntable.epoch = self.epoch;
        HashMap2::move_slots(&mut ntable, &mut self.slots, 0, capacity, self.epoch);
        self.max_load = ntable.max_load;
        self.slots = ntable.slots;
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// Move the live entries of `[lo, hi)` into `ntable`, halving so the
    /// recursion is `log2 n` deep (see `vacate_slots`).
    fn move_slots(
        ntable: &mut HashMap2<K, V>,
        slots: &mut Vec<Slot<K, V>>,
        lo: usize,
        hi: usize,
        epoch: u32,
    ) {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let s = core::mem::replace(&mut slots[lo], Slot::Vacant);
                match s {
                    Slot::Vacant => (),
                    Slot::Live(g, k, v) => {
                        if g == epoch {
                            let _ = ntable.insert_no_resize(k, v);
                        }
                    }
                }
            } else {
                let mid = lo + n / 2;
                HashMap2::move_slots(ntable, slots, lo, mid, epoch);
                HashMap2::move_slots(ntable, slots, mid, hi, epoch)
            }
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// Unbind `key`, returning the value it was bound to.
    ///
    /// **Backward-shift deletion** (Knuth, *TAOCP* 6.4 algorithm R): the hole
    /// the removal leaves would break the runs of every key stored past it, so
    /// `repair` pulls forward the first later entry whose home lies at or
    /// before the hole, and repeats from the slot that entry vacated.  The
    /// alternative — a tombstone — needs a third slot state, and every probe
    /// then pays for deletions that happened long ago; the checker's one
    /// `remove` caller (`arena::promote::erase_installed`) does not justify
    /// that.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let n = self.slots.len();
        if n == 0 {
            None
        } else {
            let i = home_index(key.hash64(), n);
            let r = probe(&self.slots, self.epoch, key, i, n, n);
            if !r.1 {
                None
            } else {
                let prev = core::mem::replace(&mut self.slots[r.0], Slot::Vacant);
                self.num_entries -= 1;
                self.repair(r.0, next_index(r.0, n), n, n);
                match prev {
                    Slot::Vacant => None,
                    Slot::Live(_, _, v) => Some(v),
                }
            }
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// `remove`'s cluster repair: `hole` is free, `j` is the next slot to
    /// consider, and the run ends at the first free slot.  `fuel` is the slot
    /// count, which bounds the run.
    fn repair(&mut self, hole: usize, j: usize, n: usize, fuel: usize) {
        if fuel == 0 {
            ()
        } else {
            // Each of the two reads below is a `match` that returns a SCALAR,
            // so the loan on `self.slots` is dead at the join.  Deciding
            // inside one three-way `match` arm instead is task #97-P4a's
            // second extraction rule and Aeneas rejects it outright
            // ("Could not match the contexts", `interp/Interp.ml:617`).
            let e = self.epoch;
            let act = if !slot_live(&self.slots[j], e) {
                0
            } else if wraps_past(slot_home(&self.slots[j], n), hole, j, n) {
                1
            } else {
                2
            };
            if act == 0 {
                ()
            } else if act == 1 {
                let s = core::mem::replace(&mut self.slots[j], Slot::Vacant);
                self.slots[hole] = s;
                self.repair(j, next_index(j, n), n, fuel - 1)
            } else {
                self.repair(hole, next_index(j, n), n, fuel - 1)
            }
        }
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// Is this slot live at `epoch`?  A `match` returning a scalar, so that the
/// caller's loan on the slot vector is dead at the join (see `repair`).
fn slot_live<K, V>(s: &Slot<K, V>, epoch: u32) -> bool {
    match s {
        Slot::Vacant => false,
        Slot::Live(g, _, _) => *g == epoch,
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// The home slot of this slot's key among `n` slots; `0` on a `Vacant` slot,
/// which `repair` never asks about (it tests `slot_live` first).  A `match`
/// returning a scalar, for `slot_live`'s reason.
fn slot_home<K, V>(s: &Slot<K, V>, n: usize) -> usize
where
    K: Hashable,
{
    match s {
        Slot::Vacant => 0,
        Slot::Live(_, ckey, _) => home_index(ckey.hash64(), n),
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// Algorithm R's test: may the entry at `j`, whose home slot is `h`, be moved
/// back into the free slot at `hole`?  It may exactly when `h` is **not**
/// cyclically inside `(hole, j]` — i.e. when the distance from `h` forward to
/// `j` is at least the distance from `hole` forward to `j`.
fn wraps_past(h: usize, hole: usize, j: usize, n: usize) -> bool {
    let dh = (j + n - h) % n;
    let dk = (j + n - hole) % n;
    dh >= dk
}

impl<K, V> HashMap2<K, V>
where
    K: Hashable + Eq2,
    V: Dup,
{
    /// con-leche: none — arena infrastructure (task #97-P6-17)
    /// **The fused probe**: one hash and one probe run that answer both "is
    /// the key here?" and "where would it go?".  Returns `(at, hit)`: `hit`
    /// is the value bound to `key`, and when it is `None`, `at` is the free
    /// slot an `insert_at` must write.  The table is allocated on the way in,
    /// so `at` is always a real slot.
    ///
    /// **Why** (task #97-survey's N1/N2, still-nanoda's `cache-study-port`
    /// `289d48d`, which does the same thing with `IndexMap`'s `Entry`): the
    /// arena's cons tables answer an interning MISS with `Tbl::find` followed
    /// by `Tbl::push`, and `push`'s `insert` then hashes the record and walks
    /// the probe run a second time — 372 M times on the Mathlib 25 % prefix.
    /// Nothing about the table changes between the two, because the caller
    /// only computes the derived word and the handle in between, so the slot
    /// the first probe found is still the slot the second would find.
    ///
    /// `get` is `find_slot`'s second component and nothing else; the two are
    /// kept apart because `get` is a `&self` reader on a table that may never
    /// have been allocated, and this one is the insert path's own.
    pub fn find_slot(&mut self, key: &K) -> (usize, Option<V>) {
        self.ensure_slots();
        let n = self.slots.len();
        let i = home_index(key.hash64(), n);
        let r = probe(&self.slots, self.epoch, key, i, n, n);
        if r.1 {
            match &self.slots[r.0] {
                Slot::Vacant => (r.0, None),
                Slot::Live(_, _, v) => (r.0, Some(v.dup2())),
            }
        } else {
            (r.0, None)
        }
    }
}

impl<K, V> HashMap2<K, V>
where
    K: Dup,
    V: Dup,
{
    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// A copy of the table that shares nothing with it — the snapshot
    /// `CheckerOps.orElse` restores from (`ron::hashmap::HashMap::dup`'s doc
    /// comment has the argument).  Stale slots are copied too: they are not
    /// part of the abstract map, and reproducing the table exactly is what
    /// makes the copy's later behaviour identical.
    pub fn dup(&self) -> HashMap2<K, V> {
        let n = self.slots.len();
        let slots = HashMap2::dup_slots(&self.slots, Vec::with_capacity(n), 0, n);
        HashMap2 {
            num_entries: self.num_entries,
            max_load: self.max_load,
            epoch: self.epoch,
            fit_hw: self.fit_hw,
            slots,
        }
    }

    /// con-leche: none — arena infrastructure (task #97-P6-4b)
    /// `dup`'s slot walk over `[lo, hi)`, pushing the copies onto `out` in
    /// index order; halved, as `vacate_slots` is.
    fn dup_slots(
        src: &Vec<Slot<K, V>>,
        out: Vec<Slot<K, V>>,
        lo: usize,
        hi: usize,
    ) -> Vec<Slot<K, V>> {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let mut out = out;
                out.push(dup_slot(&src[lo]));
                out
            } else {
                let mid = lo + n / 2;
                let out = HashMap2::dup_slots(src, out, lo, mid);
                HashMap2::dup_slots(src, out, mid, hi)
            }
        } else {
            out
        }
    }
}

/// con-leche: none — arena infrastructure (task #97-P6-4b)
/// Copy one slot.
fn dup_slot<K, V>(s: &Slot<K, V>) -> Slot<K, V>
where
    K: Dup,
    V: Dup,
{
    match s {
        Slot::Vacant => Slot::Vacant,
        Slot::Live(g, k, v) => Slot::Live(*g, k.dup2(), v.dup2()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ron::hashmap::HashMap;

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

    /// A key whose hash is a constant: every entry lands in one run.
    struct Bad(u64);

    impl Hashable for Bad {
        fn hash64(&self) -> u64 {
            7
        }
    }

    impl Eq2 for Bad {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl Dup for Bad {
        fn dup2(&self) -> Bad {
            Bad(self.0)
        }
    }

    #[test]
    fn empty_table_binds_nothing() {
        let m: HashMap2<u64, u64> = HashMap2::new();
        assert_eq!(m.capacity(), 0);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        assert_eq!(m.get(&0), None);
        assert_eq!(m.get(&12345), None);
        assert!(!m.contains_key(&1));
    }

    #[test]
    fn insert_get_replace() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        assert_eq!(m.insert(1, 10), None);
        assert_eq!(m.insert(2, 20), None);
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&1), Some(&10));
        assert_eq!(m.get(&2), Some(&20));
        assert_eq!(m.get(&3), None);
        assert_eq!(m.insert(1, 11), Some(10));
        assert_eq!(m.len(), 2);
        assert_eq!(m.get(&1), Some(&11));
    }

    #[test]
    fn growth_keeps_every_binding() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 10_000 {
            assert_eq!(m.insert(i.wrapping_mul(0x9e3779b97f4a7c15), i), None);
            i += 1;
        }
        assert_eq!(m.len(), 10_000);
        let mut i: u64 = 0;
        while i < 10_000 {
            assert_eq!(m.get(&i.wrapping_mul(0x9e3779b97f4a7c15)), Some(&i));
            i += 1;
        }
        assert!(m.capacity() >= 10_000);
    }

    #[test]
    fn clear_is_an_epoch_bump_and_the_table_is_empty() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 1000 {
            m.insert(i, i);
            i += 1;
        }
        let c = m.capacity();
        m.clear();
        assert_eq!(m.len(), 0);
        assert_eq!(m.capacity(), c);
        let mut i: u64 = 0;
        while i < 1000 {
            assert_eq!(m.get(&i), None);
            i += 1;
        }
        // and it refills
        let mut i: u64 = 0;
        while i < 1000 {
            assert_eq!(m.insert(i, i + 1), None);
            i += 1;
        }
        let mut i: u64 = 0;
        while i < 1000 {
            assert_eq!(m.get(&i), Some(&(i + 1)));
            i += 1;
        }
    }

    #[test]
    fn many_clears_do_not_leak_stale_rows() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        let mut round: u64 = 0;
        while round < 200 {
            let mut i: u64 = 0;
            while i < 300 {
                m.insert(round * 1000 + i, i);
                i += 1;
            }
            assert_eq!(m.len(), 300);
            m.clear();
            assert_eq!(m.len(), 0);
            // nothing from this round or any earlier one survives
            assert_eq!(m.get(&(round * 1000 + 7)), None);
            if round > 0 {
                assert_eq!(m.get(&((round - 1) * 1000 + 7)), None);
            }
            round += 1;
        }
    }

    #[test]
    fn epoch_wrap_vacates_and_restarts() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        m.insert(1, 1);
        m.insert(2, 2);
        // step the epoch to the brink by hand, then clear across it
        m.epoch = EPOCH_MAX - 1;
        m.insert(3, 3);
        assert_eq!(m.get(&3), Some(&3));
        m.clear();
        assert_eq!(m.epoch, EPOCH_MAX);
        m.insert(4, 4);
        assert_eq!(m.get(&4), Some(&4));
        assert_eq!(m.get(&3), None);
        m.clear();
        assert_eq!(m.epoch, 1);
        assert_eq!(m.len(), 0);
        assert_eq!(m.get(&4), None);
        m.insert(5, 5);
        assert_eq!(m.get(&5), Some(&5));
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn remove_keeps_the_runs_intact() {
        let mut m: HashMap2<Bad, u64> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 40 {
            assert_eq!(m.insert(Bad(i), i + 1), None);
            i += 1;
        }
        // every key is in one run of 40; remove every third and check the rest
        let mut i: u64 = 0;
        while i < 40 {
            if i % 3 == 0 {
                assert_eq!(m.remove(&Bad(i)), Some(i + 1));
            }
            i += 1;
        }
        let mut i: u64 = 0;
        while i < 40 {
            if i % 3 == 0 {
                assert_eq!(m.get(&Bad(i)), None);
            } else {
                assert_eq!(m.get(&Bad(i)), Some(&(i + 1)));
            }
            i += 1;
        }
        assert_eq!(m.len(), 40 - 14);
    }

    /// The whole API, against `ron::hashmap::HashMap` on the same operation
    /// stream: the two must agree on every answer.
    #[test]
    fn differential_against_the_chained_map() {
        let mut a: HashMap<u64, u64> = HashMap::new();
        let mut b: HashMap2<u64, u64> = HashMap2::new();
        let mut rng = Rng(0x2545f4914f6cdd1d);
        let mut step = 0;
        while step < 200_000 {
            let r = rng.next();
            let k = r >> 40; // ~16k distinct keys, so hits and misses both
            match r % 8 {
                0 | 1 | 2 | 3 => {
                    assert_eq!(a.insert(k, r), b.insert(k, r), "insert {} at {}", k, step)
                }
                4 | 5 => assert_eq!(a.get(&k), b.get(&k), "get {} at {}", k, step),
                6 => assert_eq!(
                    a.contains_key(&k),
                    b.contains_key(&k),
                    "contains {} at {}",
                    k,
                    step
                ),
                _ => assert_eq!(a.remove(&k), b.remove(&k), "remove {} at {}", k, step),
            }
            assert_eq!(a.len(), b.len(), "len at {}", step);
            if step % 20_000 == 19_999 {
                a.clear();
                b.clear();
                assert_eq!(a.len(), b.len());
            }
            step += 1;
        }
    }

    /// The same, with a constant hash: one run, every operation quadratic, and
    /// the backward shift under maximum pressure.
    #[test]
    fn differential_constant_hash() {
        let mut a: HashMap<Bad, u64> = HashMap::new();
        let mut b: HashMap2<Bad, u64> = HashMap2::new();
        let mut rng = Rng(0x9e3779b97f4a7c15);
        let mut step = 0;
        while step < 4_000 {
            let r = rng.next();
            let k = r % 64;
            match r % 4 {
                0 | 1 => assert_eq!(a.insert(Bad(k), r), b.insert(Bad(k), r), "at {}", step),
                2 => assert_eq!(a.get(&Bad(k)), b.get(&Bad(k)), "at {}", step),
                _ => assert_eq!(a.remove(&Bad(k)), b.remove(&Bad(k)), "at {}", step),
            }
            assert_eq!(a.len(), b.len(), "len at {}", step);
            step += 1;
        }
    }

    #[test]
    fn dup_is_independent_of_the_original() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
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

    #[test]
    fn dup_after_a_clear_carries_no_stale_row() {
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 100 {
            m.insert(i, i);
            i += 1;
        }
        m.clear();
        let d = m.dup();
        assert_eq!(d.len(), 0);
        let mut i: u64 = 0;
        while i < 100 {
            assert_eq!(d.get(&i), None);
            i += 1;
        }
    }

    /// `is_saturated_full` is the precondition `insert` now declares, and
    /// nothing short of a `2^63`-slot table makes it true: the tables the
    /// checker builds are always able to double.  (The true branch cannot be
    /// exercised at all — it needs 184 exabytes of slots — which is the whole
    /// point of task #97-P6-17: the state exists in the *model* and nowhere
    /// else, and `try_resize`'s `capacity * 2` is where the model stops.)
    #[test]
    fn a_growing_table_is_never_saturated_full() {
        let m: HashMap2<u64, u64> = HashMap2::new();
        assert!(!m.is_saturated_full());
        let mut m: HashMap2<u64, u64> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 5_000 {
            m.insert(i.wrapping_mul(0x9e3779b97f4a7c15), i);
            assert!(!m.is_saturated_full());
            assert!(m.len() <= m.capacity() * 3 / 4);
            i += 1;
        }
        m.clear_fit();
        assert!(!m.is_saturated_full());
    }

    #[test]
    fn with_capacity_pre_sizes() {
        let m: HashMap2<u64, u64> = HashMap2::with_capacity(1000);
        assert_eq!(m.capacity(), 1024);
        assert_eq!(m.len(), 0);
        let m: HashMap2<u64, u64> = HashMap2::with_capacity(1);
        assert_eq!(m.capacity(), MIN_CAPACITY);
    }

    /// A composite key, as `CState`'s tuple-keyed tables have.  A newtype
    /// rather than `(u64, u64)` itself: `ron::hashmap`'s own test module
    /// already implements the two dictionaries for the bare tuple, and two
    /// impls of one trait for one type do not cohere.
    struct Pair(u64, u64);

    impl Hashable for Pair {
        fn hash64(&self) -> u64 {
            self.0.wrapping_mul(31).wrapping_add(self.1)
        }
    }

    impl Eq2 for Pair {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0 && self.1 == other.1
        }
    }

    impl Dup for Pair {
        fn dup2(&self) -> Pair {
            Pair(self.0, self.1)
        }
    }

    #[test]
    fn a_tuple_key_round_trips() {
        let mut m: HashMap2<Pair, bool> = HashMap2::new();
        let mut i: u64 = 0;
        while i < 50 {
            assert_eq!(m.insert(Pair(i, i + 1), i % 2 == 0), None);
            i += 1;
        }
        let d = m.dup();
        let mut i: u64 = 0;
        while i < 50 {
            assert_eq!(d.get(&Pair(i, i + 1)), Some(&(i % 2 == 0)));
            i += 1;
        }
        assert_eq!(d.get(&Pair(3, 3)), None);
    }
}
