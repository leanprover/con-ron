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

/// ConLeche/Kernel/Name.lean:34 — `inductive Name`.
pub enum NameKind {
    Anonymous,
    Str(Name, Vec<u32>),
    Num(Name, u64),
}

/// The heap node of a `Name`: the cached hash (ConLeche/Kernel/Name.lean:41,
/// `@[computed_field] hashData`) beside the constructor data.
pub struct NameNode {
    pub hash: u64,
    pub kind: NameKind,
}

/// ConLeche/Kernel/Name.lean:34 — a hierarchical name.
pub struct Name(pub Rc<NameNode>);

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

/// Lean's `hash : String → UInt64`.  The runtime hashes the UTF-8 bytes
/// (`lean_string_hash`, not inlineable from the toolchain headers); we hash
/// the code points instead.  Hash values are verdict-neutral (DESIGN.md §3.2:
/// `mixHash` is opaque in the proofs, the hash guard in `beq` is provably
/// redundant, and hashes only move memo entries between buckets), so this is
/// a free choice — it must simply be *a* function of the value.
pub fn str_hash(s: &Vec<u32>) -> u64 {
    str_hash_from(s, 0, 11)
}

/// The tail-recursive fold behind `str_hash` (no loops, DESIGN.md §3.4).
pub fn str_hash_from(s: &Vec<u32>, i: usize, acc: u64) -> u64 {
    if i >= s.len() {
        acc
    } else {
        str_hash_from(s, i + 1, mix_hash(acc, s[i] as u64))
    }
}

/// Lean's `hash : Nat → UInt64` on the indices that DESIGN.md §3.3 makes
/// `u64`: the identity, as `Nat.hash` is for machine-sized naturals.
pub fn nat_hash(n: u64) -> u64 {
    n
}

/// ConLeche/Kernel/Name.lean:41 — the cached hash, an `O(1)` field read.
pub fn hash_data(n: &Name) -> u64 {
    n.0.hash
}

/// ConLeche/Kernel/Name.lean:34 — `Name.anonymous`, hash `1723`.
pub fn anonymous() -> Name {
    Name(Rc::new(NameNode { hash: 1723, kind: NameKind::Anonymous }))
}

/// ConLeche/Kernel/Name.lean:34 — `Name.str`; the smart constructor computes
/// `mixHash (mixHash 1 p.hashData) (hash s)` (line 43).
pub fn mk_str(pre: Name, s: Vec<u32>) -> Name {
    let h: u64 = mix_hash(mix_hash(1, hash_data(&pre)), str_hash(&s));
    Name(Rc::new(NameNode { hash: h, kind: NameKind::Str(pre, s) }))
}

/// ConLeche/Kernel/Name.lean:34 — `Name.num`; the smart constructor computes
/// `mixHash (mixHash 2 p.hashData) (hash n)` (line 44).
pub fn mk_num(pre: Name, n: u64) -> Name {
    let h: u64 = mix_hash(mix_hash(2, hash_data(&pre)), nat_hash(n));
    Name(Rc::new(NameNode { hash: h, kind: NameKind::Num(pre, n) }))
}

/// Share a name (the `Rc` bump that Lean's value semantics hides).
pub fn dup(n: &Name) -> Name {
    Name(Rc::clone(&n.0))
}

/// The pointer test behind `withPtrEq` (ConLeche/Kernel/Name.lean:57).
/// Modeled as `false` in Lean (DESIGN.md §3.2).
pub fn ptr_eq(a: &Name, b: &Name) -> bool {
    Rc::ptr_eq(&a.0, &b.0)
}

/// Code-point string equality.
pub fn str_eq(a: &Vec<u32>, b: &Vec<u32>) -> bool {
    if a.len() != b.len() {
        false
    } else {
        str_eq_from(a, b, 0)
    }
}

/// The recursion behind `str_eq`.
pub fn str_eq_from(a: &Vec<u32>, b: &Vec<u32>, i: usize) -> bool {
    if i >= a.len() {
        true
    } else if a[i] != b[i] {
        false
    } else {
        str_eq_from(a, b, i + 1)
    }
}

/// ConLeche/Kernel/Name.lean:57 — `Name.beqPtr`, the *executed* `Name.beq`
/// (line 74; `@[csimp]`-substituted, line 88): pointer, then the cached hash,
/// then the structural walk.  Unlike Lean's `decide (a = b)` the descent
/// keeps the pointer fast path at every level; DESIGN.md §3.2's reflexivity
/// obligation is what makes that transparent.
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

/// `List.contains` on names, from index `i` on (Lean's `ns.contains n`).
pub fn contains_from(ns: &Vec<Name>, i: usize, n: &Name) -> bool {
    if i >= ns.len() {
        false
    } else if beq(&ns[i], n) {
        true
    } else {
        contains_from(ns, i + 1, n)
    }
}

/// `List.contains` on names.
pub fn contains(ns: &Vec<Name>, n: &Name) -> bool {
    contains_from(ns, 0, n)
}

/// A one-element name list (`[p]` in `Level.byCases`).
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
