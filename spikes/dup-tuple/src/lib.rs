//! Spike (task #67): does Charon/Aeneas accept a user trait impl on a *tuple*
//! type?  The `CState` snapshot needs one — five of the fourteen memo tables
//! are keyed on a 2- or 3-tuple — and the fallback (a monomorphic copy per
//! tuple-keyed map, since DESIGN.md §3.4 forbids closures) is much worse.
//!
//! **Verdict: yes, both shapes work, and so does a concrete impl on a foreign
//! generic type at a fixed instance.**  Run with
//!
//! ```text
//! charon cargo --preset=aeneas --dest-file out/dup_tuple.llbc
//! aeneas -backend lean -split-files -loops-to-rec \
//!   -dest lean -subdir DupTuple -namespace DupTuple out/dup_tuple.llbc
//! ```
//!
//! Charon reported nothing, Aeneas generated in 0.35 s, and `lean/Funs.lean`
//! (committed beside this file) has, verbatim:
//!
//! * `Pair.Insts.Dup_tupleDup     : Dup A → Dup B → Dup (A × B)`
//! * `TupleABC.Insts.Dup_tupleDup : Dup A → Dup B → Dup C → Dup (A × B × C)`
//! * `alloc.vec.VecLvl.Insts.Dup_tupleDup : Dup (alloc.vec.Vec Lvl)`
//!
//! with `dup_pair_table` / `dup_triple_table` applying them to the component
//! instances exactly as a hand-written instance argument would.  The slot
//! walks come out as `partial_fixpoint` definitions, which is what every
//! other `ron::hashmap` recursion already gets.
use std::vec::Vec;

pub trait Dup {
    fn dup2(&self) -> Self;
}

pub struct Name {
    pub w: u64,
}

impl Dup for u64 {
    fn dup2(&self) -> u64 {
        *self
    }
}

impl Dup for bool {
    fn dup2(&self) -> bool {
        *self
    }
}

impl Dup for Name {
    fn dup2(&self) -> Name {
        Name { w: self.w }
    }
}

pub struct Lvl {
    pub k: u64,
}

impl Dup for Lvl {
    fn dup2(&self) -> Lvl {
        Lvl { k: self.k }
    }
}

/// Concrete impl on a foreign generic type at a fixed instance.
impl Dup for Vec<Lvl> {
    fn dup2(&self) -> Vec<Lvl> {
        dup_vec_go(self, Vec::new(), 0)
    }
}

pub fn dup_vec_go(src: &Vec<Lvl>, out: Vec<Lvl>, i: usize) -> Vec<Lvl> {
    if i >= src.len() {
        out
    } else {
        let mut out = out;
        out.push(src[i].dup2());
        dup_vec_go(src, out, i + 1)
    }
}

/// The question: a generic impl on a 2-tuple.
impl<A: Dup, B: Dup> Dup for (A, B) {
    fn dup2(&self) -> (A, B) {
        (self.0.dup2(), self.1.dup2())
    }
}

/// And a 3-tuple.
impl<A: Dup, B: Dup, C: Dup> Dup for (A, B, C) {
    fn dup2(&self) -> (A, B, C) {
        (self.0.dup2(), self.1.dup2(), self.2.dup2())
    }
}

/// A concrete (non-generic) impl on a tuple type: the other shape we might use.
pub enum AList<K, V> {
    Nil,
    Cons(K, V, Option<Box<AList<K, V>>>),
}

pub struct Table<K, V> {
    pub slots: Vec<AList<K, V>>,
    pub n: usize,
}

pub fn dup_alist<K: Dup, V: Dup>(l: &AList<K, V>) -> AList<K, V> {
    match l {
        AList::Nil => AList::Nil,
        AList::Cons(k, v, tl) => match tl {
            None => AList::Cons(k.dup2(), v.dup2(), None),
            Some(t) => AList::Cons(k.dup2(), v.dup2(), Some(Box::new(dup_alist(t)))),
        },
    }
}

pub fn dup_slots<K: Dup, V: Dup>(src: &Vec<AList<K, V>>, out: &mut Vec<AList<K, V>>, i: usize) {
    if i >= src.len() {
        return;
    }
    out.push(dup_alist(&src[i]));
    dup_slots(src, out, i + 1)
}

pub fn dup_table<K: Dup, V: Dup>(t: &Table<K, V>) -> Table<K, V> {
    let mut slots: Vec<AList<K, V>> = Vec::new();
    dup_slots(&t.slots, &mut slots, 0);
    Table { slots, n: t.n }
}

/// The real question, instantiated: a table whose key is a tuple.
pub fn dup_pair_table(t: &Table<(Name, Vec<Lvl>), u64>) -> Table<(Name, Vec<Lvl>), u64> {
    dup_table(t)
}

pub fn dup_triple_table(t: &Table<(Name, Name, Vec<Lvl>), bool>) -> Table<(Name, Name, Vec<Lvl>), bool> {
    dup_table(t)
}
