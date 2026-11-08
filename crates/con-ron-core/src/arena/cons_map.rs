//! con-leche: none — arena infrastructure; the key-free cons table (task #148)
//!
//! `arena::cons_map::ConsMap<I>` — an interning table that stores **no key**.
//! `ron::hashmap2::HashMap2` is open addressing with linear probing over
//! `Slot<K, V> = Vacant | Live(epoch, K, V)`; this is the same table, probe
//! for probe, with the slot cut down to `(epoch, fragment, handle)`, 8 bytes
//! for every handle kind.  The key of a live slot is the node record the
//! handle points at, `rows[h.row()].0`, which the owning `arena::store::Tbl`
//! holds anyway: `HashMap2` held a second copy of every node in its slots.
//!
//! **The fragment** is 16 bits of the key's hash (`frag_of`), and a probe
//! reads the row only when the slot's fragment is the probed key's.  Without
//! it every live slot a probe passes is a dependent load into the rows, a
//! cache miss on a large table; task #148 measured that at +16 % cycles on
//! the heaviest Mathlib declaration, and the fragment takes it back to +2 %.
//! The stamp is 16 bits to make room for it, so `clear`'s wrap — the
//! `O(capacity)` vacate — comes every 65 535 clears of one table instead of
//! every 2^32; the scratch tables are cleared twice per declaration.
//!
//! **What it saves** (task #146's profile, Mathlib `--olean`): the frozen
//! persistent tier's cons tables were 1 024 MiB of a 1.88 GiB tier, and the
//! `e.apps` one alone 2^25 slots of 20 B; a slot here is 8 B whatever the
//! record (a `StrNode` or `ListNode` key was a `Vec` header plus its own heap
//! block).  Task #148's section has the measurement.
//!
//! **How it is proved** (`proof/ConRon/Refine/ConsMap.lean`).  Every function
//! below is `HashMap2`'s function of the same name with "the slot's key"
//! read as "the slot's row's key", and the proof is a simulation: the VIEW
//! of a `ConsMap` over its rows — each slot of the current epoch as
//! `Live(epoch, rows[h.row()].0, h)`, every other slot `Vacant` — is a
//! `HashMap2<A, I>`, each operation here maps to the `HashMap2` operation on
//! the view, and `Refine/HashMap2.lean`'s specifications are reused as they
//! stand.  The fragment test is the `HashMap2` run under an `Eq2` that
//! answers `false` first when the two fragments differ, which is still exact.
//! The view needs three facts of the table itself: every stamp is at most
//! the epoch, every slot of the current epoch names a row, and its fragment
//! is that row's key's.
//!
//! Only the operations `Tbl` uses exist: no `remove`, no `contains_key`.

use std::vec::Vec;

use crate::arena::handle::word_idx_nat;
use crate::arena::handle::EIdx;
use crate::arena::handle::LIdx;
use crate::arena::handle::LsIdx;
use crate::arena::handle::NIdx;
use crate::ron::hashmap::Dup;
use crate::ron::hashmap::Eq2;
use crate::ron::hashmap::Hashable;

/// con-leche: none — arena infrastructure (task #148)
/// What a key-free table needs of a handle: the index of the row it names,
/// and a filler value for a slot that names nothing.
pub trait ConsHandle {
    /// con-leche: none — arena infrastructure (task #148)
    /// The index into the constructor's row vector (`Idx.idxNat`).
    fn row(&self) -> usize;
    /// con-leche: none — arena infrastructure (task #148)
    /// The handle a never-written slot carries.  It is never read: a slot is
    /// live only at the table's epoch, and a filler slot's stamp is `0`.
    fn vacant() -> Self;
}

/// con-leche: none — arena infrastructure (task #148)
impl ConsHandle for EIdx {
    /// con-leche: none — arena infrastructure (task #148)
    fn row(&self) -> usize {
        word_idx_nat(self.word)
    }
    /// con-leche: none — arena infrastructure (task #148)
    fn vacant() -> EIdx {
        EIdx { word: 0 }
    }
}

/// con-leche: none — arena infrastructure (task #148)
impl ConsHandle for NIdx {
    /// con-leche: none — arena infrastructure (task #148)
    fn row(&self) -> usize {
        word_idx_nat(self.word)
    }
    /// con-leche: none — arena infrastructure (task #148)
    fn vacant() -> NIdx {
        NIdx { word: 0 }
    }
}

/// con-leche: none — arena infrastructure (task #148)
impl ConsHandle for LIdx {
    /// con-leche: none — arena infrastructure (task #148)
    fn row(&self) -> usize {
        word_idx_nat(self.word)
    }
    /// con-leche: none — arena infrastructure (task #148)
    fn vacant() -> LIdx {
        LIdx { word: 0 }
    }
}

/// con-leche: none — arena infrastructure (task #148)
impl ConsHandle for LsIdx {
    /// con-leche: none — arena infrastructure (task #148)
    fn row(&self) -> usize {
        word_idx_nat(self.word)
    }
    /// con-leche: none — arena infrastructure (task #148)
    fn vacant() -> LsIdx {
        LsIdx { word: 0 }
    }
}

/// con-leche: none — arena infrastructure (task #148)
/// A slot: the handle `h` is bound (to the key `rows[h.row()].0`) **if and
/// only if** `g` is the table's current epoch.  The epoch is at least 1, so a
/// filler slot (`g = 0`) is never live; it plays `HashMap2`'s `Vacant`.  `f`
/// is the key's `frag_of`, so a probe compares it before it reads the row.
pub struct CSlot<I> {
    pub g: u16,
    pub f: u16,
    pub h: I,
}

/// con-leche: none — arena infrastructure (task #148)
/// `core::clone::Clone` for `CSlot`, which `Vec::resize`'s signature demands
/// of `allocate_slots`' filler.  It is a real copy (a handle is a word).
impl<I> core::clone::Clone for CSlot<I>
where
    I: Dup,
{
    /// con-leche: none — arena infrastructure (task #148)
    fn clone(&self) -> CSlot<I> {
        CSlot { g: self.g, f: self.f, h: self.h.dup2() }
    }
}

/// con-leche: none — arena infrastructure (task #148)
/// The key-free open-addressed table.  The fields are `HashMap2`'s, with the
/// same meaning and the same invariants (`proof/ConRon/Refine/ConsMap.lean`).
pub struct ConsMap<I> {
    num_entries: usize,
    max_load: usize,
    epoch: u16,
    fit_hw: usize,
    slots: Vec<CSlot<I>>,
}

/// `HashMap2`'s `MIN_CAPACITY`.
const MIN_CAPACITY: usize = 32;

/// `HashMap2`'s load factor, `LOAD_NUM / LOAD_DEN`.
const LOAD_NUM: usize = 3;
const LOAD_DEN: usize = 4;

/// Fuel for `pow2_at_least`: a `usize` has at most 64 bits.
const POW2_FUEL: usize = 64;

/// `HashMap2`'s `FIT_DECAY` (task #97-P6-7).
const FIT_DECAY: usize = 8;

/// `HashMap2`'s `FIT_SLACK` (task #97-P6-7).
const FIT_SLACK: usize = 64;

/// The largest stamp; `clear` at this value vacates the slots and restarts.
const EPOCH_MAX: u16 = 65535;

/// con-leche: none — arena infrastructure (task #148)
/// `HashMap2`'s `home_index`, the same multiply-xor finalizer.
fn home_index(h: u64, n: usize) -> usize {
    let m = h.wrapping_mul(0x9e3779b97f4a7c15);
    let x = m ^ (m >> 32);
    let n64 = n as u64;
    let i = x & (n64 - 1);
    i as usize
}

/// con-leche: none — arena infrastructure (task #148)
/// A slot's fragment: the top 16 bits of the multiplied hash, the bits
/// `home_index` uses least.  Any function of the hash would be exact; this one
/// separates the keys of one probe run.
fn frag_of(h: u64) -> u16 {
    let m = h.wrapping_mul(0x9e3779b97f4a7c15);
    (m >> 48) as u16
}

/// con-leche: none — arena infrastructure (task #148)
/// The next slot of a probe run, wrapping at the end.
fn next_index(i: usize, n: usize) -> usize {
    let j = i + 1;
    if j >= n {
        0
    } else {
        j
    }
}

/// con-leche: none — arena infrastructure (task #148)
/// The resize threshold for a given slot count.
fn max_load_for(capacity: usize) -> usize {
    let q = capacity / LOAD_DEN;
    q * LOAD_NUM
}

/// con-leche: none — arena infrastructure (task #148)
/// The smallest power of two that is `>= n`, from `cap` up.
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

/// con-leche: none — arena infrastructure (task #148)
/// **The probe**, `HashMap2`'s with the key read from the row: walk the run
/// that starts at `i` and return `(at, found)`.  `fr` is the key's fragment;
/// the row is read only on a slot whose fragment is `fr`.
fn probe<A, D, I>(
    rows: &Vec<(A, D)>,
    slots: &Vec<CSlot<I>>,
    epoch: u16,
    key: &A,
    fr: u16,
    i: usize,
    n: usize,
    fuel: usize,
) -> (usize, bool)
where
    A: Eq2,
    I: ConsHandle,
{
    if fuel == 0 {
        (i, false)
    } else {
        let s = &slots[i];
        if s.g != epoch {
            (i, false)
        } else if s.f == fr && rows[s.h.row()].0.eq2(key) {
            (i, true)
        } else {
            probe(rows, slots, epoch, key, fr, next_index(i, n), n, fuel - 1)
        }
    }
}

impl<I> ConsMap<I>
where
    I: Dup + ConsHandle,
{
    /// con-leche: none — arena infrastructure (task #148)
    /// Append `n` filler slots to `slots`: one `Vec::resize`.
    fn allocate_slots(mut slots: Vec<CSlot<I>>, n: usize) -> Vec<CSlot<I>> {
        let len: usize = slots.len() + n;
        slots.resize(len, CSlot { g: 0, f: 0, h: I::vacant() });
        slots
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// A fresh table with exactly `capacity` slots (a power of two `>=
    /// MIN_CAPACITY`).
    fn new_with_capacity_pow2(capacity: usize) -> ConsMap<I> {
        let slots = ConsMap::allocate_slots(Vec::with_capacity(capacity), capacity);
        ConsMap { num_entries: 0, max_load: max_load_for(capacity), epoch: 1, fit_hw: 0, slots }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// An empty table that has not allocated its slots yet.
    pub fn new() -> ConsMap<I> {
        ConsMap { num_entries: 0, max_load: 0, epoch: 1, fit_hw: 0, slots: Vec::new() }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// `HashMap2::ensure_slots`: the deferred allocation, sized by `fit_hw`.
    fn ensure_slots(&mut self) {
        if self.slots.len() == 0 {
            let want: usize =
                pow2_at_least(self.fit_hw + self.fit_hw + 1, MIN_CAPACITY, POW2_FUEL);
            let table = ConsMap::new_with_capacity_pow2(want);
            self.max_load = table.max_load;
            self.slots = table.slots;
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// The number of entries.
    pub fn len(&self) -> usize {
        self.num_entries
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// How many slots the table has.
    pub fn capacity(&self) -> usize {
        self.slots.len()
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// `HashMap2::clear`: empty the table in O(1) by bumping the epoch.
    pub fn clear(&mut self) {
        self.num_entries = 0;
        if self.epoch >= EPOCH_MAX {
            let n = self.slots.len();
            ConsMap::vacate_slots(&mut self.slots, 0, n);
            self.epoch = 1
        } else {
            self.epoch = self.epoch + 1
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// `HashMap2::clear_fit`: empty the table, and give the slots back when
    /// the decaying high-water mark says the next round will not need them.
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
            self.num_entries = 0;
            self.max_load = 0;
            self.epoch = 1;
            self.slots = Vec::new()
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// The epoch wrap's slot walk over `[lo, hi)`, halving.
    fn vacate_slots(slots: &mut Vec<CSlot<I>>, lo: usize, hi: usize) {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                slots[lo] = CSlot { g: 0, f: 0, h: I::vacant() }
            } else {
                let mid = lo + n / 2;
                ConsMap::vacate_slots(slots, lo, mid);
                ConsMap::vacate_slots(slots, mid, hi)
            }
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// The handle bound to `key`, if any.
    pub fn get<A, D>(&self, rows: &Vec<(A, D)>, key: &A) -> Option<I>
    where
        A: Hashable + Eq2,
    {
        let n = self.slots.len();
        if n == 0 {
            None
        } else {
            let hh = key.hash64();
            let i = home_index(hh, n);
            let r = probe(rows, &self.slots, self.epoch, key, frag_of(hh), i, n, n);
            if r.1 {
                Some(self.slots[r.0].h.dup2())
            } else {
                None
            }
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// `HashMap2::find_slot`: one probe that answers both "is the key here?"
    /// and "where would it go?".
    pub fn find_slot<A, D>(&mut self, rows: &Vec<(A, D)>, key: &A) -> (usize, Option<I>)
    where
        A: Hashable + Eq2,
    {
        self.ensure_slots();
        let n = self.slots.len();
        let hh = key.hash64();
        let i = home_index(hh, n);
        let r = probe(rows, &self.slots, self.epoch, key, frag_of(hh), i, n, n);
        if r.1 {
            (r.0, Some(self.slots[r.0].h.dup2()))
        } else {
            (r.0, None)
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// Bind `rows[value.row()].0` — which the caller has just pushed — to
    /// `value`, returning the handle it was bound to before, if any.
    pub fn insert<A, D>(&mut self, rows: &Vec<(A, D)>, key: &A, value: I) -> Option<I>
    where
        A: Hashable + Eq2,
    {
        self.ensure_slots();
        let old = self.insert_no_resize(rows, key, value);
        if self.num_entries > self.max_load {
            self.try_resize(rows)
        }
        old
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// `insert` without the load check.
    fn insert_no_resize<A, D>(&mut self, rows: &Vec<(A, D)>, key: &A, value: I) -> Option<I>
    where
        A: Hashable + Eq2,
    {
        let n = self.slots.len();
        let hh = key.hash64();
        let i = home_index(hh, n);
        let r = probe(rows, &self.slots, self.epoch, key, frag_of(hh), i, n, n);
        let e = self.epoch;
        let prev = core::mem::replace(&mut self.slots[r.0], CSlot { g: e, f: frag_of(hh), h: value });
        if r.1 {
            Some(prev.h)
        } else {
            self.num_entries += 1;
            None
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// **Write a new entry at the slot `find_slot` just returned**; the row
    /// `value` names must already be in `rows`.
    pub fn insert_at<A, D>(&mut self, rows: &Vec<(A, D)>, at: usize, value: I)
    where
        A: Hashable + Eq2,
    {
        let e = self.epoch;
        let fr = frag_of(rows[value.row()].0.hash64());
        self.slots[at] = CSlot { g: e, f: fr, h: value };
        self.num_entries += 1;
        if self.num_entries > self.max_load {
            self.try_resize(rows)
        }
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// Double the slot count and rehash, each entry's hash recomputed from its
    /// row.
    fn try_resize<A, D>(&mut self, rows: &Vec<(A, D)>)
    where
        A: Hashable + Eq2,
    {
        let capacity = self.slots.len();
        let mut ntable = ConsMap::new_with_capacity_pow2(capacity * 2);
        ntable.epoch = self.epoch;
        ConsMap::move_slots(rows, &mut ntable, &mut self.slots, 0, capacity, self.epoch);
        self.max_load = ntable.max_load;
        self.slots = ntable.slots;
    }

    /// con-leche: none — arena infrastructure (task #148)
    /// Move the live entries of `[lo, hi)` into `ntable`, halving.
    fn move_slots<A, D>(
        rows: &Vec<(A, D)>,
        ntable: &mut ConsMap<I>,
        slots: &mut Vec<CSlot<I>>,
        lo: usize,
        hi: usize,
        epoch: u16,
    ) where
        A: Hashable + Eq2,
    {
        if hi > lo {
            let n = hi - lo;
            if n == 1 {
                let s = core::mem::replace(&mut slots[lo], CSlot { g: 0, f: 0, h: I::vacant() });
                if s.g == epoch {
                    let k = &rows[s.h.row()].0;
                    let _ = ntable.insert_no_resize(rows, k, s.h);
                }
            } else {
                let mid = lo + n / 2;
                ConsMap::move_slots(rows, ntable, slots, lo, mid, epoch);
                ConsMap::move_slots(rows, ntable, slots, mid, hi, epoch)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// A key whose hash is constant (every entry in one run), or the
    /// identity, by its second field.
    struct Key(u64, bool);

    impl Hashable for Key {
        fn hash64(&self) -> u64 {
            if self.1 {
                7
            } else {
                self.0
            }
        }
    }

    impl Eq2 for Key {
        fn eq2(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    /// Differential run against `std::collections::HashMap`: `find_slot` then
    /// `insert_at` on a miss (the interning path), `get`, and `clear_fit`
    /// rounds that drop the rows as `Tbl::reset` does.
    fn run(bad: bool) {
        let mut rows: Vec<(Key, ())> = Vec::new();
        let mut m: ConsMap<EIdx> = ConsMap::new();
        let mut oracle: HashMap<u64, u32> = HashMap::new();
        let mut x: u64 = 0x2545f4914f6cdd1d;
        let mut step = 0;
        let steps = if bad { 3_000 } else { 100_000 };
        while step < steps {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let k = (x >> 40) % if bad { 200 } else { 30_000 };
            let key = Key(k, bad);
            let (at, hit) = m.find_slot(&rows, &key);
            match oracle.get(&k) {
                Some(w) => assert_eq!(hit.map(|h| h.word), Some(*w)),
                None => {
                    assert!(hit.is_none());
                    let w = rows.len() as u32;
                    rows.push((key, ()));
                    m.insert_at(&rows, at, EIdx { word: w });
                    oracle.insert(k, w);
                }
            }
            if step % 7 == 0 {
                let probe = Key(k ^ 1, bad);
                assert_eq!(m.get(&rows, &probe).map(|h| h.word), oracle.get(&(k ^ 1)).copied());
            }
            assert_eq!(m.len(), oracle.len());
            if step % 20_000 == 19_999 {
                m.clear_fit();
                rows = Vec::new();
                oracle.clear();
            }
            step += 1;
        }
    }

    #[test]
    fn differential_against_std() {
        run(false)
    }

    #[test]
    fn differential_constant_hash() {
        run(true)
    }
}
