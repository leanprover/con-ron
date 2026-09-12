//! Port of `ConLeche/Kernel/Name.lean` — hierarchical names.
//!
//! Representation notes (DESIGN.md §3.2, §3.3):
//! * a `Name` is an `Rc` tree; the `@[computed_field] hashData` of the Lean
//!   inductive is the stored `NameNode::hash`, written by the smart
//!   constructors below and by nothing else;
//! * strings are `Vec<u32>` code points, not `String`: the checker only ever
//!   compares and hashes them, and Aeneas's `String` support is thin;
//! * every function takes its `Name` arguments by shared reference and
//!   returns owned `Name`s, because Rust cannot pattern-match through an
//!   `Rc` and therefore cannot give back a borrowed subterm.

use std::rc::Rc;

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The three constructors of `inductive Name`; the cached hash they carry
/// in Lean's `@[computed_field]` sits in `NameNode` (DESIGN.md §3.2).
pub enum NameKind {
    Anonymous,
    Str(Name, Vec<u32>),
    Num(Name, u64),
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The heap node of a `Name`: the cited inductive's `@[computed_field]
/// hashData` beside the constructor data.
pub struct NameNode {
    pub hash: u64,
    pub kind: NameKind,
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// A hierarchical name: an `Rc` tree, Lean's value semantics made sharing
/// (DESIGN.md §3.2).
pub struct Name(pub Rc<NameNode>);

/// con-leche: none — Lean's `mixHash`, a runtime primitive, not a con-leche definition
/// Lean's `mixHash`, i.e. the runtime's `lean_uint64_mix_hash`
/// (`include/lean/lean.h:2036`, a MurmurHash2 64-bit mix step).
pub fn mix_hash(h: u64, k: u64) -> u64 {
    let m: u64 = 0xc6a4a7935bd1e995;
    let k1: u64 = k.wrapping_mul(m);
    let k2: u64 = k1 ^ (k1 >> 47);
    let k3: u64 = k2 ^ m;
    let h1: u64 = h ^ k3;
    h1.wrapping_mul(m)
}

/// con-leche: none — Lean's `hash : String → UInt64`, a runtime primitive; see below for why any function of the value will do
/// Lean's `hash : String → UInt64`.  The runtime hashes the UTF-8 bytes
/// (`lean_string_hash`, not inlineable from the toolchain headers); we hash
/// the code points instead.  Hash values are verdict-neutral (DESIGN.md §3.2:
/// `mixHash` is opaque in the proofs, the hash guard in `beq` is provably
/// redundant, and hashes only move memo entries between buckets), so this is
/// a free choice — it must simply be *a* function of the value.
pub fn str_hash(s: &Vec<u32>) -> u64 {
    str_hash_from(s, 0, 11)
}

/// con-leche: none — the tail-recursive fold behind `str_hash`; Lean has no counterpart
/// No loops (DESIGN.md §3.4).
pub fn str_hash_from(s: &Vec<u32>, i: usize, acc: u64) -> u64 {
    if i >= s.len() {
        acc
    } else {
        str_hash_from(s, i + 1, mix_hash(acc, s[i] as u64))
    }
}

/// con-leche: none — Lean's `hash : Nat → UInt64`, a runtime primitive
/// On the indices that DESIGN.md §3.3 makes
/// `u64`: the identity, as `Nat.hash` is for machine-sized naturals.
pub fn nat_hash(n: u64) -> u64 {
    n
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// The cached `@[computed_field] hashData`, an `O(1)` field read.
pub fn hash_data(n: &Name) -> u64 {
    n.0.hash
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.anonymous`, hash `1723`.
pub fn anonymous() -> Name {
    Name(Rc::new(NameNode { hash: 1723, kind: NameKind::Anonymous }))
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.str`; the smart constructor computes the cited computed-field
/// equation `mixHash (mixHash 1 p.hashData) (hash s)`, which in Lean the
/// elaborator writes for you.
pub fn mk_str(pre: Name, s: Vec<u32>) -> Name {
    let h: u64 = mix_hash(mix_hash(1, hash_data(&pre)), str_hash(&s));
    Name(Rc::new(NameNode { hash: h, kind: NameKind::Str(pre, s) }))
}

/// con-leche: ConLeche/Kernel/Name.lean:26-45 Name
/// `Name.num`; the smart constructor computes the cited computed-field
/// equation `mixHash (mixHash 2 p.hashData) (hash n)`.
pub fn mk_num(pre: Name, n: u64) -> Name {
    let h: u64 = mix_hash(mix_hash(2, hash_data(&pre)), nat_hash(n));
    Name(Rc::new(NameNode { hash: h, kind: NameKind::Num(pre, n) }))
}

/// con-leche: none — the `Rc` bump that Lean's value semantics hides (DESIGN.md §3.2)
/// Share a name.
pub fn dup(n: &Name) -> Name {
    Name(Rc::clone(&n.0))
}

/// con-leche: ConLeche/Kernel/Name.lean:51-59 Name.beqPtr
/// The pointer test behind the cited `withPtrEq`.  Deviation: modeled as
/// `false` in the generated Lean (DESIGN.md §3.2), where Lean discharges
/// `withPtrEq`'s obligation instead.
pub fn ptr_eq(a: &Name, b: &Name) -> bool {
    Rc::ptr_eq(&a.0, &b.0)
}

/// con-leche: none — `String` equality; strings are `Vec<u32>` code points here (DESIGN.md §3.3)
/// Code-point string equality.
pub fn str_eq(a: &Vec<u32>, b: &Vec<u32>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        str_eq_from(a, b, 0)
    }
}

/// con-leche: none — the index recursion behind `str_eq`
/// No loops (DESIGN.md §3.4).
pub fn str_eq_from(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i] != b[i] {
        false
    } else {
        str_eq_from(a, b, i + 1)
    }
}

/// con-leche: ConLeche/Kernel/Name.lean:51-59 Name.beqPtr
/// con-leche: ConLeche/Kernel/Name.lean:70-74 Name.beq
/// `Name.beqPtr` is the *executed* `Name.beq` (`@[csimp]`-substituted):
/// pointer, then the cached hash, then the structural walk.  Deviation:
/// unlike Lean's `decide (a = b)` the descent keeps the pointer fast path
/// at every level; DESIGN.md §3.2's reflexivity obligation is what makes
/// that transparent.
pub fn beq(a: &Name, b: &Name) -> bool {
    if ptr_eq(a, b) {
        true
    } else if hash_data(a) != hash_data(b) {
        false
    } else {
        match (&a.0.kind, &b.0.kind) {
            (NameKind::Anonymous, NameKind::Anonymous) => true,
            (NameKind::Str(p, s), NameKind::Str(q, t)) => beq(p, q) && str_eq(s, t),
            (NameKind::Num(p, m), NameKind::Num(q, n)) => beq(p, q) && m == n,
            _ => false,
        }
    }
}

/// con-leche: none — `List.contains` on names, from index `i` on; `List` is a `Vec` walked by index (DESIGN.md §3.3)
/// Lean writes `ns.contains n`.
pub fn contains_from(ns: &Vec<Name>, i: usize, n: &Name) -> bool {
    if i >= ns.len() {
        false
    } else if beq(&ns[i], n) {
        true
    } else {
        contains_from(ns, i + 1, n)
    }
}

/// con-leche: none — `List.contains` on names
/// The entry point of the index recursion above.
pub fn contains(ns: &Vec<Name>, n: &Name) -> bool {
    contains_from(ns, 0, n)
}

/// con-leche: none — a one-element `Vec` for the `[p]` literal in `Level.byCases`
/// A one-element name list.
pub fn singleton(n: &Name) -> Vec<Name> {
    let mut v: Vec<Name> = Vec::new();
    v.push(dup(n));
    v
}

/* Not ported here:
   * `Name.ofLeanName` (Name.lean:98) — frontend only, outside the theorem.
   * `Name.toString` (Name.lean:101) — error-message rendering; DESIGN.md §3.1
     says message strings need not match, and nothing the checker decides
     reads it. */
