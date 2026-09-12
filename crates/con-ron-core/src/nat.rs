//! con-leche: none — replaces the runtime's `Nat` (GMP); no Lean source to cite.
//!
//! `ron::Nat` — the arbitrary-precision natural number that replaces Lean's
//! runtime `Nat` (DESIGN.md §3.3).  Lean's `Nat` is GMP behind a small-int
//! fast path; nothing of that is in con-ron's trusted base, so the checker
//! carries its own bignum, written in the Aeneas subset (§3.4) and proved.
//!
//! # Representation: one `Vec<u64>` of little-endian limbs, normalised
//!
//! DESIGN.md §3.3 floated `Small(u64) | Big(Vec<u64>)`.  This module takes
//! the other option — a bare limb vector — **because it makes the Aeneas
//! proof strictly simpler**:
//!
//! * the abstraction is a single recursive function,
//!   `toNat l = match l with [] => 0 | x :: r => x.val + 2^64 * toNat r`,
//!   with no case analysis and no "does it fit a word" side condition;
//! * every operation is *one* algorithm, so every homomorphism lemma is one
//!   induction.  With a two-constructor enum each binary operation has four
//!   representation cases (and each of them must additionally prove that the
//!   result was re-tagged into the right constructor), i.e. ~4× the lemma
//!   count for no gain in the model;
//! * normalisation is the single predicate "the last limb is not `0`"
//!   (`Nat.WF`), which is what makes structural equality numeric equality —
//!   the `Small`/`Big` split needs that *plus* "`Big` only when it does not
//!   fit a word", a second invariant every operation must re-establish.
//!
//! The price is a heap allocation for small values, which the enum would
//! have avoided.  That is a *performance* decision, not a correctness one; if
//! profiling in P1.6 asks for it, a `Small` fast path can be added later as a
//! provably-equal special case of the same functions, which is a much smaller
//! proof than starting from the enum.
//!
//! **Invariant (`Nat.WF`).** `limbs` has no trailing zero limb: either it is
//! empty (the number `0`) or `limbs[limbs.len() - 1] != 0`.  Every function
//! here returns a normalised `Nat` when given normalised arguments, so
//! structural equality of `limbs` *is* numeric equality (`beq` exploits it).
//!
//! # Shape of the code (DESIGN.md §3.4 and the task-#3 patterns)
//!
//! No loops: every pass over the limbs is an index-carrying `*_from` helper,
//! the public function being the `i = 0` wrapper.  Accumulators are passed
//! *by value* and returned (`out: Vec<u64>` in, `Vec<u64>` out), so no `&mut`
//! parameter appears and Aeneas sees a plain value-passing recursion.  The
//! only `Vec` operations used are `new`, `push`, `len` and indexing — Aeneas
//! models all four (`Aeneas/Std/Vec.lean`), and in particular the model has
//! no `pop`/`truncate`, which is why `norm` trims by copying.
//!
//! The only casts are `u64 -> u128` (widening) and `u128 -> u64` (truncating,
//! modelled as `BitVec.setWidth` — total, and only ever applied to a value
//! that provably fits).  Limb *indices* are `usize`; every `u64` count that
//! has to become an index (a shift's whole-word part) is consumed by a
//! counting recursion instead of by a cast, so no `u64 -> usize` cast — whose
//! model depends on `System.Platform.numBits` — occurs anywhere.

/// An arbitrary-precision natural number: little-endian `u64` limbs with no
/// trailing zero limb (see the module doc).  `0` is the empty vector.
pub struct Nat {
    pub limbs: Vec<u64>,
}

/// The result of comparing two `Nat`s.  con-leche needs `beq`, `ble` and
/// `blt`; all three read off one three-way comparison, which keeps the
/// refinement proof to a single lemma about `cmp`.
pub enum Cmp {
    Lt,
    Eq,
    Gt,
}

// ---------------------------------------------------------------------------
// Constructors, destructors, the invariant
// ---------------------------------------------------------------------------

/// `0`.
pub fn zero() -> Nat {
    Nat { limbs: Vec::new() }
}

/// `1`.
pub fn one() -> Nat {
    from_u64(1)
}

/// The literal `x` as a `Nat` (`Nat.ofNat` on a machine word).
pub fn from_u64(x: u64) -> Nat {
    if x == 0 {
        Nat { limbs: Vec::new() }
    } else {
        let mut v: Vec<u64> = Vec::new();
        v.push(x);
        Nat { limbs: v }
    }
}

/// `some x` when the value fits a machine word, `none` otherwise.
pub fn to_u64(a: &Nat) -> Option<u64> {
    if a.limbs.len() == 0 {
        Some(0)
    } else if a.limbs.len() == 1 {
        Some(a.limbs[0])
    } else {
        None
    }
}

/// `a == 0`.  By the invariant this is a length test.
pub fn is_zero(a: &Nat) -> bool {
    a.limbs.len() == 0
}

/// Limb `i`, `0` past the end (the mathematical limb sequence is infinite).
fn limb(v: &Vec<u64>, i: usize) -> u64 {
    if i < v.len() {
        v[i]
    } else {
        0
    }
}

/// The number of significant limbs of `v[0..k]`: the largest `s <= k` with
/// `v[s - 1] != 0`.
fn sig_len(v: &Vec<u64>, k: usize) -> usize {
    if k == 0 {
        0
    } else if v[k - 1] != 0 {
        k
    } else {
        sig_len(v, k - 1)
    }
}

/// Push `v[i..end]` onto `out` (the caller guarantees `end <= v.len()`; the
/// second guard is the Lean fall-through, never taken).
fn copy_from(v: &Vec<u64>, i: usize, end: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= end {
        out
    } else if i >= v.len() {
        out
    } else {
        let mut o = out;
        o.push(v[i]);
        copy_from(v, i + 1, end, o)
    }
}

/// Re-establish the invariant: drop trailing zero limbs.  Aeneas's `Vec`
/// model has neither `pop` nor `truncate`, so trimming copies; when nothing
/// has to be dropped (the common case) the vector is moved through.
pub fn norm(limbs: Vec<u64>) -> Nat {
    let n = limbs.len();
    let s = sig_len(&limbs, n);
    if s == n {
        Nat { limbs }
    } else {
        Nat { limbs: copy_from(&limbs, 0, s, Vec::new()) }
    }
}

/// A deep copy.  `#[derive(Clone)]` also goes through (measured: Aeneas
/// models `Vec::clone` as `alloc.vec.CloneVec.clone`, so it is *not* an
/// external hole), but it puts a `core::clone::Clone` trait declaration and
/// instance into the model for nothing; an explicit limb copy keeps the
/// generated Lean trait-free and matches the module's free-function API.
pub fn clone(a: &Nat) -> Nat {
    Nat { limbs: copy_from(&a.limbs, 0, a.limbs.len(), Vec::new()) }
}

// ---------------------------------------------------------------------------
// Comparison — `Nat.beq`, `Nat.ble`, `Nat.blt`
// ---------------------------------------------------------------------------

/// Three-way comparison.  Normalised operands, so a length difference
/// already decides; otherwise compare limbs from the top down.
pub fn cmp(a: &Nat, b: &Nat) -> Cmp {
    let la = a.limbs.len();
    let lb = b.limbs.len();
    if la < lb {
        Cmp::Lt
    } else if la > lb {
        Cmp::Gt
    } else {
        cmp_from(&a.limbs, &b.limbs, la)
    }
}

/// Compare `a[0..k]` against `b[0..k]`, most significant limb first.
fn cmp_from(a: &Vec<u64>, b: &Vec<u64>, k: usize) -> Cmp {
    if k == 0 {
        Cmp::Eq
    } else {
        let x = limb(a, k - 1);
        let y = limb(b, k - 1);
        if x < y {
            Cmp::Lt
        } else if x > y {
            Cmp::Gt
        } else {
            cmp_from(a, b, k - 1)
        }
    }
}

/// `Nat.beq`.
pub fn beq(a: &Nat, b: &Nat) -> bool {
    match cmp(a, b) {
        Cmp::Eq => true,
        Cmp::Lt => false,
        Cmp::Gt => false,
    }
}

/// `Nat.ble`.
pub fn ble(a: &Nat, b: &Nat) -> bool {
    match cmp(a, b) {
        Cmp::Lt => true,
        Cmp::Eq => true,
        Cmp::Gt => false,
    }
}

/// `Nat.blt`.
pub fn blt(a: &Nat, b: &Nat) -> bool {
    match cmp(a, b) {
        Cmp::Lt => true,
        Cmp::Eq => false,
        Cmp::Gt => false,
    }
}

// ---------------------------------------------------------------------------
// Addition, subtraction, predecessor
// ---------------------------------------------------------------------------

/// `a + b`.
pub fn add(a: &Nat, b: &Nat) -> Nat {
    let n = if a.limbs.len() < b.limbs.len() { b.limbs.len() } else { a.limbs.len() };
    norm(add_from(&a.limbs, &b.limbs, 0, n, 0, Vec::new()))
}

/// Ripple-carry over limbs `i..n`, then the final carry limb.  `carry` is `0`
/// or `1`; the two `overflowing_add`s cannot both overflow.
fn add_from(a: &Vec<u64>, b: &Vec<u64>, i: usize, n: usize, carry: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= n {
        if carry == 0 {
            out
        } else {
            let mut o = out;
            o.push(carry);
            o
        }
    } else {
        let x = limb(a, i);
        let y = limb(b, i);
        let (s1, c1) = x.overflowing_add(y);
        let (s2, c2) = s1.overflowing_add(carry);
        let c: u64 = if c1 {
            1
        } else if c2 {
            1
        } else {
            0
        };
        let mut o = out;
        o.push(s2);
        add_from(a, b, i + 1, n, c, o)
    }
}

/// `a - b`, truncated at `0` (Lean's `Nat` subtraction).
pub fn sub(a: &Nat, b: &Nat) -> Nat {
    match cmp(a, b) {
        Cmp::Lt => zero(),
        Cmp::Eq => zero(),
        Cmp::Gt => norm(sub_from(&a.limbs, &b.limbs, 0, a.limbs.len(), 0, Vec::new())),
    }
}

/// Ripple-borrow over limbs `i..n`, called only when `a >= b`, so the borrow
/// out of limb `n - 1` is `0` and no limb is dropped.
fn sub_from(a: &Vec<u64>, b: &Vec<u64>, i: usize, n: usize, borrow: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= n {
        out
    } else {
        let x = limb(a, i);
        let y = limb(b, i);
        let (d1, o1) = x.overflowing_sub(y);
        let (d2, o2) = d1.overflowing_sub(borrow);
        let bo: u64 = if o1 {
            1
        } else if o2 {
            1
        } else {
            0
        };
        let mut o = out;
        o.push(d2);
        sub_from(a, b, i + 1, n, bo, o)
    }
}

/// `Nat.pred`: `a - 1`, with `pred 0 = 0`.
pub fn pred(a: &Nat) -> Nat {
    let o = one();
    sub(a, &o)
}

// ---------------------------------------------------------------------------
// Shifts
// ---------------------------------------------------------------------------

/// Push `count` zero limbs onto `out`.  The count is consumed by recursion
/// rather than turned into an index, so no `u64 -> usize` cast is needed.
fn push_zeros(out: Vec<u64>, count: u64) -> Vec<u64> {
    if count == 0 {
        out
    } else {
        let mut o = out;
        o.push(0);
        push_zeros(o, count - 1)
    }
}

/// `Nat.shiftLeft a k`.
pub fn shift_left(a: &Nat, k: u64) -> Nat {
    if is_zero(a) {
        zero()
    } else {
        let words = k / 64;
        let bits = k % 64;
        let out = push_zeros(Vec::new(), words);
        if bits == 0 {
            norm(copy_from(&a.limbs, 0, a.limbs.len(), out))
        } else {
            norm(shl_bits_from(&a.limbs, 0, bits, 0, out))
        }
    }
}

/// The sub-word part of a left shift; `bits` is in `1..=63`, so both `<<` and
/// `>>` stay below the word width (the `bits == 0` case is handled above,
/// because `x >> 64` is not a legal `u64` shift).
fn shl_bits_from(v: &Vec<u64>, i: usize, bits: u64, carry: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if carry == 0 {
            out
        } else {
            let mut o = out;
            o.push(carry);
            o
        }
    } else {
        let x = v[i];
        let lo = (x << bits) | carry;
        let hi = x >> (64 - bits);
        let mut o = out;
        o.push(lo);
        shl_bits_from(v, i + 1, bits, hi, o)
    }
}

/// The index `min(i + remaining, v.len())`, computed by counting so that a
/// `u64` whole-word shift never has to be cast to `usize`.
fn skip_index(v: &Vec<u64>, i: usize, remaining: u64) -> usize {
    if remaining == 0 {
        i
    } else if i >= v.len() {
        v.len()
    } else {
        skip_index(v, i + 1, remaining - 1)
    }
}

/// `Nat.shiftRight a k`.
pub fn shift_right(a: &Nat, k: u64) -> Nat {
    let words = k / 64;
    let bits = k % 64;
    let s = skip_index(&a.limbs, 0, words);
    if bits == 0 {
        norm(copy_from(&a.limbs, s, a.limbs.len(), Vec::new()))
    } else {
        norm(shr_bits_from(&a.limbs, s, bits, Vec::new()))
    }
}

/// The sub-word part of a right shift; `bits` is in `1..=63`.
fn shr_bits_from(v: &Vec<u64>, i: usize, bits: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        out
    } else {
        let lo = v[i] >> bits;
        let hi = if i + 1 < v.len() {
            v[i + 1] << (64 - bits)
        } else {
            0
        };
        let mut o = out;
        o.push(lo | hi);
        shr_bits_from(v, i + 1, bits, o)
    }
}

/// `2 * a + bit` (`bit` is `0` or `1`) — the step of the long division below.
fn shl1_or(a: &Nat, bit: u64) -> Nat {
    norm(shl1_from(&a.limbs, 0, bit, Vec::new()))
}

fn shl1_from(v: &Vec<u64>, i: usize, carry: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if carry == 0 {
            out
        } else {
            let mut o = out;
            o.push(carry);
            o
        }
    } else {
        let x = v[i];
        let mut o = out;
        o.push((x << 1) | carry);
        shl1_from(v, i + 1, x >> 63, o)
    }
}

// ---------------------------------------------------------------------------
// Multiplication and power
// ---------------------------------------------------------------------------

/// `a * m` for a single-limb `m`.
fn mul_u64(a: &Nat, m: u64) -> Nat {
    norm(mul_u64_from(&a.limbs, 0, m, 0, Vec::new()))
}

/// One pass with a `u128` accumulator: `v[i] * m + carry` is at most
/// `(2^64 - 1)^2 + (2^64 - 1) = 2^128 - 2^64`, so the `u128` product cannot
/// overflow and the truncating cast back to `u64` takes exactly the low half.
fn mul_u64_from(v: &Vec<u64>, i: usize, m: u64, carry: u64, out: Vec<u64>) -> Vec<u64> {
    if i >= v.len() {
        if carry == 0 {
            out
        } else {
            let mut o = out;
            o.push(carry);
            o
        }
    } else {
        let t: u128 = (v[i] as u128) * (m as u128) + (carry as u128);
        let lo: u64 = t as u64;
        let hi: u64 = (t >> 64) as u64;
        let mut o = out;
        o.push(lo);
        mul_u64_from(v, i + 1, m, hi, o)
    }
}

/// `a * b`, as `sum_i (a * b[i]) << (64 * i)`.
///
/// This is schoolbook multiplication written as shift-and-add rather than as
/// an in-place accumulation into a pre-sized output, so that the only `Vec`
/// operations are `new`/`push`/`len`/index (no `IndexMut`) and the
/// homomorphism proof is one induction over `i` with the invariant
/// `toNat acc = toNat a * toNat (b[0..i])`.  Same `O(n*m)` word count as the
/// in-place form, with an extra pass per limb of `b`; if P1.6 profiling asks
/// for it, the in-place version is a local replacement.
pub fn mul(a: &Nat, b: &Nat) -> Nat {
    let z = zero();
    mul_from(a, b, 0, 0, z)
}

fn mul_from(a: &Nat, b: &Nat, i: usize, sh: u64, acc: Nat) -> Nat {
    if i >= b.limbs.len() {
        acc
    } else {
        let p = mul_u64(a, b.limbs[i]);
        let ps = shift_left(&p, sh);
        let acc2 = add(&acc, &ps);
        mul_from(a, b, i + 1, sh + 64, acc2)
    }
}

/// `a ^ e` by square-and-multiply.  The caller enforces con-leche's
/// `ReducePowMaxExp` bound (`e <= 2^24`, `Kernel/Core.lean:639`); this
/// function is total.  Repeated multiplication would give a one-line
/// induction, but `e` up to `2^24` makes it quadratically slow, and the
/// binary recursion is still a plain strong induction on `e` through
/// `x ^ e = (x ^ (e / 2))^2 * x ^ (e % 2)`.
pub fn pow(a: &Nat, e: u64) -> Nat {
    if e == 0 {
        one()
    } else {
        let h = pow(a, e / 2);
        let hh = mul(&h, &h);
        if e % 2 == 0 {
            hh
        } else {
            mul(&hh, a)
        }
    }
}

// ---------------------------------------------------------------------------
// Division, remainder, gcd
// ---------------------------------------------------------------------------

/// `(a / b, a % b)` by shift-subtract long division, restoring, one bit at a
/// time from the top: `rem := 2 * rem + bit; if rem >= b then rem -= b`.
/// Knuth D would be faster and much harder to prove (DESIGN.md §3.3).
///
/// Lean's conventions on a zero divisor: `a / 0 = 0` and `a % 0 = a`.
pub fn div_mod(a: &Nat, b: &Nat) -> (Nat, Nat) {
    if is_zero(b) {
        (zero(), clone(a))
    } else {
        let z = zero();
        let (qrev, r) = dm_limbs(a, b, a.limbs.len(), Vec::new(), z);
        let k = qrev.len();
        (norm(rev_copy_from(&qrev, k, Vec::new())), r)
    }
}

/// `a / b`.
pub fn div(a: &Nat, b: &Nat) -> Nat {
    let (q, _r) = div_mod(a, b);
    q
}

/// `a % b`.  (`mod` is a Rust keyword; con-leche's `Nat.mod`.)
pub fn modulo(a: &Nat, b: &Nat) -> Nat {
    let (_q, r) = div_mod(a, b);
    r
}

/// Push `v[k - 1], v[k - 2], ..., v[0]` onto `out`: the quotient limbs are
/// produced most-significant first and the representation is little-endian.
fn rev_copy_from(v: &Vec<u64>, k: usize, out: Vec<u64>) -> Vec<u64> {
    if k == 0 {
        out
    } else if k > v.len() {
        out
    } else {
        let mut o = out;
        o.push(v[k - 1]);
        rev_copy_from(v, k - 1, o)
    }
}

/// The outer division recursion: limb `i - 1` of the dividend, downwards.
fn dm_limbs(a: &Nat, b: &Nat, i: usize, qrev: Vec<u64>, rem: Nat) -> (Vec<u64>, Nat) {
    if i == 0 {
        (qrev, rem)
    } else {
        let (ql, rem2) = dm_bits(a, b, i - 1, 64, 0, rem);
        let mut q = qrev;
        q.push(ql);
        dm_limbs(a, b, i - 1, q, rem2)
    }
}

/// The inner division recursion: bit `j - 1` of limb `i`, downwards, with the
/// quotient limb accumulated in `qacc`.  `j` runs in `0..=64`, so `j - 1` is
/// always a legal shift amount.
fn dm_bits(a: &Nat, b: &Nat, i: usize, j: u64, qacc: u64, rem: Nat) -> (u64, Nat) {
    if j == 0 {
        (qacc, rem)
    } else {
        let bit = (a.limbs[i] >> (j - 1)) & 1;
        let r1 = shl1_or(&rem, bit);
        match cmp(&r1, b) {
            Cmp::Lt => dm_bits(a, b, i, j - 1, qacc << 1, r1),
            Cmp::Eq => {
                let r2 = sub(&r1, b);
                dm_bits(a, b, i, j - 1, (qacc << 1) | 1, r2)
            }
            Cmp::Gt => {
                let r2 = sub(&r1, b);
                dm_bits(a, b, i, j - 1, (qacc << 1) | 1, r2)
            }
        }
    }
}

/// `Nat.gcd`, transliterated from Lean's own recursion
/// (`gcd 0 y = y`, `gcd (x + 1) y = gcd (y % (x + 1)) (x + 1)`).
pub fn gcd(a: &Nat, b: &Nat) -> Nat {
    if is_zero(a) {
        clone(b)
    } else {
        let m = modulo(b, a);
        gcd(&m, a)
    }
}

// ---------------------------------------------------------------------------
// Bitwise operations
// ---------------------------------------------------------------------------

/// `Nat.land`.  The result is at most as long as the shorter operand.
pub fn land(a: &Nat, b: &Nat) -> Nat {
    let n = if a.limbs.len() < b.limbs.len() { a.limbs.len() } else { b.limbs.len() };
    norm(and_from(&a.limbs, &b.limbs, 0, n, Vec::new()))
}

fn and_from(a: &Vec<u64>, b: &Vec<u64>, i: usize, n: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= n {
        out
    } else {
        let mut o = out;
        o.push(limb(a, i) & limb(b, i));
        and_from(a, b, i + 1, n, o)
    }
}

/// `Nat.lor`.
pub fn lor(a: &Nat, b: &Nat) -> Nat {
    let n = if a.limbs.len() < b.limbs.len() { b.limbs.len() } else { a.limbs.len() };
    norm(or_from(&a.limbs, &b.limbs, 0, n, Vec::new()))
}

fn or_from(a: &Vec<u64>, b: &Vec<u64>, i: usize, n: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= n {
        out
    } else {
        let mut o = out;
        o.push(limb(a, i) | limb(b, i));
        or_from(a, b, i + 1, n, o)
    }
}

/// `Nat.xor`.
pub fn xor(a: &Nat, b: &Nat) -> Nat {
    let n = if a.limbs.len() < b.limbs.len() { b.limbs.len() } else { a.limbs.len() };
    norm(xor_from(&a.limbs, &b.limbs, 0, n, Vec::new()))
}

fn xor_from(a: &Vec<u64>, b: &Vec<u64>, i: usize, n: usize, out: Vec<u64>) -> Vec<u64> {
    if i >= n {
        out
    } else {
        let mut o = out;
        o.push(limb(a, i) ^ limb(b, i));
        xor_from(a, b, i + 1, n, o)
    }
}

// ---------------------------------------------------------------------------
// Hashing
// ---------------------------------------------------------------------------

/// A hash of the *value* (DESIGN.md §3.2: hashes are verdict-neutral, they
/// only move memo entries between buckets, so any fixed function of the value
/// will do — it must merely be a function of the value, which is why the
/// normalisation invariant matters here).
///
/// This one is FNV-1a over the limbs, little-endian, whole limbs at a time:
/// `h_0 = 0xcbf29ce484222325`, `h_{i+1} = (h_i XOR limbs[i]) * 0x100000001b3`
/// with wrapping multiplication.  It is *not* Lean's `Nat` hash, and nothing
/// may compare the two (task #3's note on `hash : String -> UInt64`).
pub fn hash64(a: &Nat) -> u64 {
    hash64_from(&a.limbs, 0, 0xcbf2_9ce4_8422_2325)
}

fn hash64_from(v: &Vec<u64>, i: usize, acc: u64) -> u64 {
    if i >= v.len() {
        acc
    } else {
        hash64_from(v, i + 1, (acc ^ v[i]).wrapping_mul(0x0000_0100_0000_01b3))
    }
}

// ---------------------------------------------------------------------------
// Tests.  Charon never sees this module (DESIGN.md §3.4), so loops, closures
// and iterators are fair game here.
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // -- helpers ----------------------------------------------------------

    fn of_u128(x: u128) -> Nat {
        let mut v: Vec<u64> = Vec::new();
        let lo = x as u64;
        let hi = (x >> 64) as u64;
        v.push(lo);
        v.push(hi);
        norm(v)
    }

    /// Inverse of `of_u128`; panics (in test code) if the value is too big.
    fn as_u128(a: &Nat) -> u128 {
        assert!(a.limbs.len() <= 2, "value does not fit u128: {:?}", a.limbs);
        let mut acc: u128 = 0;
        for i in (0..a.limbs.len()).rev() {
            acc = (acc << 64) | (a.limbs[i] as u128);
        }
        acc
    }

    fn of_limbs(ls: &[u64]) -> Nat {
        let mut v: Vec<u64> = Vec::new();
        for l in ls {
            v.push(*l);
        }
        norm(v)
    }

    fn wf(a: &Nat) -> bool {
        a.limbs.len() == 0 || a.limbs[a.limbs.len() - 1] != 0
    }

    fn eqn(a: &Nat, b: &Nat) -> bool {
        a.limbs == b.limbs
    }

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
        /// A value below `2^bits` (`bits <= 127`).
        fn value(&mut self, bits: u32) -> u128 {
            let x = ((self.next() as u128) << 64) | (self.next() as u128);
            if bits >= 128 {
                x
            } else {
                x & ((1u128 << bits) - 1)
            }
        }
    }

    // -- the differential test against u128 -------------------------------

    #[test]
    fn differential_against_u128() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for round in 0..2000 {
            // Mostly full-width operands, but every fourth round uses small
            // ones so that the boundary cases (0, 1, one limb) are hit often.
            let bits: u32 = if round % 4 == 0 { 1 + (round % 70) as u32 } else { 127 };
            let x = rng.value(bits);
            let y = rng.value(bits);
            let a = of_u128(x);
            let b = of_u128(y);
            assert!(wf(&a) && wf(&b));

            // both operands are below 2^127, so the sum fits u128
            assert_eq!(as_u128(&add(&a, &b)), x + y, "add {x} {y}");
            assert_eq!(as_u128(&sub(&a, &b)), x.saturating_sub(y), "sub {x} {y}");
            assert_eq!(as_u128(&pred(&a)), x.saturating_sub(1), "pred {x}");
            assert_eq!(as_u128(&div(&a, &b)), if y == 0 { 0 } else { x / y }, "div {x} {y}");
            assert_eq!(as_u128(&modulo(&a, &b)), if y == 0 { x } else { x % y }, "mod {x} {y}");
            assert_eq!(as_u128(&gcd(&a, &b)), gcd_u128(x, y), "gcd {x} {y}");
            assert_eq!(as_u128(&land(&a, &b)), x & y, "land {x} {y}");
            assert_eq!(as_u128(&lor(&a, &b)), x | y, "lor {x} {y}");
            assert_eq!(as_u128(&xor(&a, &b)), x ^ y, "xor {x} {y}");
            assert_eq!(beq(&a, &b), x == y, "beq {x} {y}");
            assert_eq!(ble(&a, &b), x <= y, "ble {x} {y}");
            assert_eq!(blt(&a, &b), x < y, "blt {x} {y}");
            assert_eq!(is_zero(&a), x == 0, "is_zero {x}");
            assert_eq!(to_u64(&a), if x <= u64::MAX as u128 { Some(x as u64) } else { None });
            assert!(eqn(&clone(&a), &a));
            assert_eq!(hash64(&a), hash64(&of_u128(x)), "hash {x}");

            // Right shift by anything; left shift on a value narrow enough
            // that the shifted result still fits u128 (wide shifts are in
            // `shifts_across_limb_boundaries`).
            let sh = rng.next() % 200;
            assert_eq!(as_u128(&shift_right(&a, sh)), if sh >= 128 { 0 } else { x >> sh }, "shr {x} {sh}");
            let narrow = x >> 70; // at most 57 bits
            let sh2 = rng.next() % 64;
            assert_eq!(as_u128(&shift_left(&of_u128(narrow), sh2)), narrow << sh2, "shl {narrow} {sh2}");

            // Multiplication: operands below 2^63 so the product fits u128.
            let u = x >> 65;
            let v = y >> 65;
            assert_eq!(as_u128(&mul(&of_u128(u), &of_u128(v))), u * v, "mul {u} {v}");

            // Power with a small base and exponent.
            let base = (rng.next() % 10) as u128;
            let e = rng.next() % 12;
            assert_eq!(as_u128(&pow(&of_u128(base), e)), base.pow(e as u32), "pow {base} {e}");

            // Every result is normalised.
            for r in [add(&a, &b), sub(&a, &b), mul(&of_u128(u), &of_u128(v)),
                      div(&a, &b), modulo(&a, &b), gcd(&a, &b), land(&a, &b),
                      lor(&a, &b), xor(&a, &b), shift_right(&a, sh), pred(&a)] {
                assert!(wf(&r), "not normalised: {:?}", r.limbs);
            }
        }
    }

    fn gcd_u128(a: u128, b: u128) -> u128 {
        if a == 0 {
            b
        } else {
            gcd_u128(b % a, a)
        }
    }

    // -- hand-picked multi-limb cases -------------------------------------

    const M: u64 = u64::MAX;

    #[test]
    fn carry_across_three_limbs() {
        let a = of_limbs(&[M, M, M]);
        let b = one();
        assert_eq!(add(&a, &b).limbs, vec![0, 0, 0, 1]);
        assert_eq!(add(&b, &a).limbs, vec![0, 0, 0, 1]);
        // and back
        assert_eq!(sub(&add(&a, &b), &b).limbs, vec![M, M, M]);
        // a carry that stops in the middle
        let c = of_limbs(&[M, M, 0, 7]);
        assert_eq!(add(&c, &one()).limbs, vec![0, 0, 1, 7]);
        // borrow across three limbs
        let d = of_limbs(&[0, 0, 0, 1]);
        assert_eq!(sub(&d, &one()).limbs, vec![M, M, M]);
    }

    #[test]
    fn sub_truncates_at_zero() {
        let a = of_limbs(&[1, 2, 3]);
        assert!(is_zero(&sub(&a, &a)));
        assert!(is_zero(&sub(&a, &of_limbs(&[1, 2, 4]))));
        assert!(is_zero(&sub(&zero(), &one())));
        assert!(is_zero(&pred(&zero())));
        assert_eq!(sub(&a, &of_limbs(&[2, 2, 3])).limbs, Vec::<u64>::new());
        assert_eq!(sub(&of_limbs(&[0, 0, 1]), &one()).limbs, vec![M, M]);
    }

    #[test]
    fn div_by_multi_limb_divisors() {
        let mut rng = Rng(0xdead_beef_1234_5678);
        for _ in 0..200 {
            let mut av: Vec<u64> = Vec::new();
            for _ in 0..6 {
                av.push(rng.next());
            }
            let mut bv: Vec<u64> = Vec::new();
            for _ in 0..3 {
                bv.push(rng.next());
            }
            let a = norm(av);
            let b = norm(bv);
            let (q, r) = div_mod(&a, &b);
            assert!(wf(&q) && wf(&r));
            // a = q * b + r  and  r < b
            assert!(eqn(&add(&mul(&q, &b), &r), &a));
            assert!(blt(&r, &b));
        }
        // exact division by a multi-limb divisor
        let b = of_limbs(&[M, 3, 7]);
        let q = of_limbs(&[9, M, 0, 5]);
        let a = mul(&q, &b);
        assert!(eqn(&div(&a, &b), &q));
        assert!(is_zero(&modulo(&a, &b)));
        // divisor bigger than the dividend
        assert!(is_zero(&div(&b, &a)));
        assert!(eqn(&modulo(&b, &a), &b));
        // Lean's zero-divisor convention
        assert!(is_zero(&div(&a, &zero())));
        assert!(eqn(&modulo(&a, &zero()), &a));
    }

    #[test]
    fn pow_multi_limb() {
        // 2^200 = limb 3 holding 2^8
        assert_eq!(pow(&of_u128(2), 200).limbs, vec![0, 0, 0, 1 << 8]);
        assert!(eqn(&pow(&of_u128(2), 200), &shift_left(&one(), 200)));
        // 3^200: compare against repeated multiplication, and its low limb
        // against wrapping u64 arithmetic
        let three = of_u128(3);
        let mut acc = one();
        for _ in 0..200 {
            acc = mul(&acc, &three);
        }
        let p = pow(&three, 200);
        assert!(eqn(&p, &acc));
        let mut low: u64 = 1;
        for _ in 0..200 {
            low = low.wrapping_mul(3);
        }
        assert_eq!(p.limbs[0], low);
        // 3^200 has ceil(200 * log2 3) = 317 bits, i.e. five limbs
        assert_eq!(p.limbs.len(), 5);
        assert!(eqn(&div(&p, &pow(&three, 199)), &three));
        assert!(is_zero(&modulo(&p, &pow(&three, 100))));
        assert!(eqn(&pow(&three, 0), &one()));
        assert!(eqn(&pow(&zero(), 0), &one()));
        assert!(is_zero(&pow(&zero(), 5)));
        // (a*b)^n = a^n * b^n on multi-limb values
        let a = of_limbs(&[M, 12345]);
        let b = of_limbs(&[7, 0, 9]);
        assert!(eqn(&pow(&mul(&a, &b), 7), &mul(&pow(&a, 7), &pow(&b, 7))));
    }

    #[test]
    fn shifts_across_limb_boundaries() {
        let a = of_limbs(&[M, 1]);
        assert_eq!(shift_left(&a, 64).limbs, vec![0, M, 1]);
        assert_eq!(shift_left(&a, 128).limbs, vec![0, 0, M, 1]);
        assert_eq!(shift_left(&a, 65).limbs, vec![0, M << 1, 3]);
        assert_eq!(shift_left(&a, 0).limbs, vec![M, 1]);
        assert_eq!(shift_right(&shift_left(&a, 193), 193).limbs, vec![M, 1]);
        assert_eq!(shift_right(&a, 64).limbs, vec![1]);
        assert_eq!(shift_right(&a, 65).limbs, Vec::<u64>::new());
        assert_eq!(shift_right(&a, 128).limbs, Vec::<u64>::new());
        // [M, 1] is 2^65 - 1; halved it is 2^64 - 1
        assert_eq!(shift_right(&a, 1).limbs, vec![M]);
        assert!(is_zero(&shift_left(&zero(), 1000)));
        assert!(is_zero(&shift_right(&zero(), 1000)));
        // round trip through a large shift
        let b = of_limbs(&[1, 2, 3, 4]);
        for k in [0u64, 1, 63, 64, 65, 127, 128, 129, 191, 192, 256] {
            assert!(eqn(&shift_right(&shift_left(&b, k), k), &b), "k = {k}");
            assert!(eqn(&shift_left(&b, k), &mul(&b, &pow(&of_u128(2), k))), "k = {k}");
        }
    }

    #[test]
    fn gcd_of_fibonacci_pairs() {
        // F(n) grows past one limb quickly; gcd(F(n), F(n+1)) = 1 and
        // gcd(F(m), F(n)) = F(gcd(m, n)).
        let mut fib: Vec<Nat> = Vec::new();
        fib.push(zero());
        fib.push(one());
        for i in 2..=180usize {
            let next = add(&fib[i - 1], &fib[i - 2]);
            fib.push(next);
        }
        assert!(fib[180].limbs.len() >= 2);
        for i in 1..180usize {
            assert!(eqn(&gcd(&fib[i], &fib[i + 1]), &one()), "consecutive at {i}");
        }
        for (m, n) in [(12usize, 18usize), (30, 45), (100, 60), (144, 96), (7, 13)] {
            let g = gcd_usize(m, n);
            assert!(eqn(&gcd(&fib[m], &fib[n]), &fib[g]), "gcd F{m} F{n}");
        }
        assert!(eqn(&gcd(&zero(), &fib[20]), &fib[20]));
        assert!(eqn(&gcd(&fib[20], &zero()), &fib[20]));
        assert!(is_zero(&gcd(&zero(), &zero())));
    }

    fn gcd_usize(a: usize, b: usize) -> usize {
        if a == 0 {
            b
        } else {
            gcd_usize(b % a, a)
        }
    }

    #[test]
    fn bitwise_multi_limb() {
        let a = of_limbs(&[M, 0, 0xf0f0]);
        let b = of_limbs(&[0x1234, M]);
        assert_eq!(land(&a, &b).limbs, vec![0x1234]);
        assert_eq!(lor(&a, &b).limbs, vec![M, M, 0xf0f0]);
        assert_eq!(xor(&a, &b).limbs, vec![M ^ 0x1234, M, 0xf0f0]);
        // and that clears the top limbs must normalise
        assert!(is_zero(&land(&of_limbs(&[0, 0, 8]), &of_limbs(&[0, 0, 4]))));
        assert_eq!(xor(&a, &a).limbs, Vec::<u64>::new());
    }

    #[test]
    fn small_values_and_conversions() {
        assert_eq!(to_u64(&zero()), Some(0));
        assert_eq!(to_u64(&from_u64(0)), Some(0));
        assert_eq!(to_u64(&from_u64(M)), Some(M));
        assert_eq!(to_u64(&of_limbs(&[0, 1])), None);
        assert_eq!(from_u64(0).limbs, Vec::<u64>::new());
        assert_eq!(from_u64(5).limbs, vec![5]);
        assert!(is_zero(&zero()));
        assert!(!is_zero(&one()));
        assert_eq!(norm(vec![0, 0, 0]).limbs, Vec::<u64>::new());
        assert_eq!(norm(vec![1, 0, 0]).limbs, vec![1]);
        assert_eq!(norm(vec![1, 0, 2]).limbs, vec![1, 0, 2]);
        // hash is a function of the value, not of the vector length
        assert_eq!(hash64(&norm(vec![7, 0])), hash64(&from_u64(7)));
        assert_ne!(hash64(&from_u64(7)), hash64(&from_u64(8)));
    }
}
