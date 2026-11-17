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
//! Two kinds of limb pass.  The value-passing one is an index-carrying
//! `*_from` helper, the public function being the `i = 0` wrapper, with the
//! output vector passed *by value* and returned (`out: Vec<u64>` in,
//! `Vec<u64>` out), so no `&mut` parameter appears.  The in-place one is a
//! `while` loop over a vector owned by the function (this file is one of the
//! two places §3.4 lets loop): `mul`'s multiply-accumulate rows and the
//! carry and borrow ripples write `v[i] = x` into a pre-sized accumulator,
//! and `-loops-to-rec` gives each loop a `*_loop` function the proof reads
//! like any other recursion.  Every output vector is allocated with
//! `Vec::with_capacity` of its bound.  The `Vec` operations used are `new`,
//! `with_capacity`, `push`, `len`, indexing, index assignment, `resize` (only
//! to truncate, in `norm`) and `clone`; Aeneas models all of them
//! (`Aeneas/Std/Vec.lean`).
//!
//! # Algorithms
//!
//! `mul` is schoolbook below `KARATSUBA_THRESHOLD` limbs and Karatsuba above
//! it, with an unbalanced product split into balanced ones (`mul_win`); it
//! works on limb windows of its operands, so no operand is copied.
//! `div_mod` is long division a limb at a time: a `u128` division for a
//! one-limb divisor, Knuth's algorithm D (TAOCP 4.3.1) on the normalised
//! operands otherwise.  `pow_nat` is square-and-multiply.  Subquadratic
//! division (Burnikel–Ziegler, Newton) is not implemented.
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

/// Re-establish the invariant: drop trailing zero limbs, by truncating in
/// place (`Vec::resize` to a shorter length); when nothing has to be dropped
/// (the common case) the vector is moved through.
pub fn norm(limbs: Vec<u64>) -> Nat {
    let n = limbs.len();
    let s = sig_len(&limbs, n);
    if s == n {
        Nat { limbs }
    } else {
        let mut v = limbs;
        v.resize(s, 0);
        Nat { limbs: v }
    }
}

/// A deep copy: `Vec::clone`, a single `memcpy` (Aeneas models it as
/// `alloc.vec.CloneVec.clone` over `u64`'s `Clone`, an instance of its
/// standard library, so no trait of this crate enters the model).
pub fn clone(a: &Nat) -> Nat {
    Nat { limbs: a.limbs.clone() }
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
    norm(add_from(&a.limbs, &b.limbs, 0, n, 0, Vec::with_capacity(n + 1)))
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
        Cmp::Gt => norm(sub_from(&a.limbs, &b.limbs, 0, a.limbs.len(), 0, Vec::with_capacity(a.limbs.len()))),
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
/// rather than turned into an index, so no `u64 -> usize` cast is needed, and
/// the recursion halves it, so its depth is the count's bit length (at most
/// 64) rather than the count: a shift by `2^24` bits pushes `2^18` limbs, and
/// a debug build, which has no tail calls, has no stack for one frame each.
fn push_zeros(out: Vec<u64>, count: u64) -> Vec<u64> {
    if count == 0 {
        out
    } else {
        let half = count / 2;
        let o = push_zeros(push_zeros(out, half), half);
        if count % 2 == 0 {
            o
        } else {
            let mut o1 = o;
            o1.push(0);
            o1
        }
    }
}

/// Push `count` zero limbs onto `out`, for a bignum `count`.  There is no
/// bound: an amount beyond one `u64` pushes `u64::MAX` zeros and recurses on
/// the rest, so an amount too large for memory fails the way every too-large
/// allocation does (task #98-SHIFT) — in Rust by exhausting memory, in the
/// model at `Vec::push`'s `usize::MAX` element limit.  No check, no decline.
fn push_zeros_nat(out: Vec<u64>, count: &Nat) -> Vec<u64> {
    match to_u64(count) {
        Some(c) => push_zeros(out, c),
        None => {
            let o = push_zeros(out, 18446744073709551615);
            let m = from_u64(18446744073709551615);
            let rest = sub(count, &m);
            push_zeros_nat(o, &rest)
        }
    }
}

/// The limbs of `a` shifted left by `bits` (`0..=63`) and appended to `out`,
/// normalised: the tail shared by both left shifts.
fn shl_onto(a: &Nat, bits: u64, out: Vec<u64>) -> Nat {
    if bits == 0 {
        norm(copy_from(&a.limbs, 0, a.limbs.len(), out))
    } else {
        norm(shl_bits_from(&a.limbs, 0, bits, 0, out))
    }
}

/// `Nat.shiftLeft a k` for a machine-word amount (`div_mod`'s normalisation,
/// `size_bytes`).
pub fn shift_left(a: &Nat, k: u64) -> Nat {
    if is_zero(a) {
        zero()
    } else {
        let out = push_zeros(Vec::new(), k / 64);
        shl_onto(a, k % 64, out)
    }
}

/// The low limb of `a`, i.e. `a % 2^64`.
fn low_limb(a: &Nat) -> u64 {
    if a.limbs.len() == 0 {
        0
    } else {
        a.limbs[0]
    }
}

/// `Nat.shiftLeft a k` for a bignum amount, unbounded (task #98-SHIFT): the
/// whole-word part `k / 64` is pushed as zero limbs by `push_zeros_nat`, which
/// runs out of memory like any allocation when it is too large.
pub fn shift_left_nat(a: &Nat, k: &Nat) -> Nat {
    if is_zero(a) {
        zero()
    } else {
        let words = shift_right(k, 6);
        let out = push_zeros_nat(Vec::new(), &words);
        shl_onto(a, low_limb(k) % 64, out)
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

/// The limbs of `a` from index `s` on, shifted right by `bits` (`0..=63`),
/// normalised: the tail shared by both right shifts.
fn shr_from(a: &Nat, s: usize, bits: u64) -> Nat {
    if bits == 0 {
        norm(copy_from(&a.limbs, s, a.limbs.len(), Vec::with_capacity(a.limbs.len() - s)))
    } else {
        norm(shr_bits_from(&a.limbs, s, bits, Vec::with_capacity(a.limbs.len() - s)))
    }
}

/// `Nat.shiftRight a k` for a machine-word amount.
pub fn shift_right(a: &Nat, k: u64) -> Nat {
    let s = skip_index(&a.limbs, 0, k / 64);
    shr_from(a, s, k % 64)
}

/// `Nat.shiftRight a k` for a bignum amount: total and exact (task
/// #98-SHIFT).  A whole-word part `k / 64` beyond `u64` exceeds every limb
/// count, so the answer there is `0`; otherwise it is the word shift above.
pub fn shift_right_nat(a: &Nat, k: &Nat) -> Nat {
    let words = shift_right(k, 6);
    match to_u64(&words) {
        Some(w) => {
            let s = skip_index(&a.limbs, 0, w);
            shr_from(a, s, low_limb(k) % 64)
        }
        None => zero(),
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

// ---------------------------------------------------------------------------
// Multiplication and power
// ---------------------------------------------------------------------------

/// `a * m` for a single-limb `m` (`div_mod`'s trial product `q̂ * b`).
fn mul_u64(a: &Nat, m: u64) -> Nat {
    norm(mul_u64_from(&a.limbs, 0, m, 0, Vec::with_capacity(a.limbs.len() + 1)))
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

/// Below this many limbs in the shorter operand, `mul_win` is the schoolbook
/// product; from it on, Karatsuba (or halving, for unbalanced operands).
/// Measured with the multiplication microbenchmark of DESIGN.md task #158.
const KARATSUBA_THRESHOLD: usize = 64;

/// `n` zero limbs: the accumulators the in-place products write into.
fn zeros(n: usize) -> Vec<u64> {
    let mut v: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n {
        v.push(0);
        i += 1;
    }
    v
}

/// Add `carry * B^k` (`B = 2^64`) into `out` in place, rippling the carry
/// upwards until it is `0`.  The callers' sums fit `out`, so the ripple stops
/// inside it.
fn add_carry_at(out: Vec<u64>, k: usize, carry: u64) -> Vec<u64> {
    let mut o = out;
    let mut c = carry;
    let mut j = k;
    while c != 0 {
        let t: u128 = (o[j] as u128) + (c as u128);
        o[j] = t as u64;
        c = (t >> 64) as u64;
        j += 1;
    }
    o
}

/// `out + y * a[lo..hi] * B^off`, in place: one multiply-accumulate row
/// (`a[lo..hi]` is the value of that limb window).  `a[i] * y + out[j] +
/// carry` is at most `(2^64 - 1)^2 + 2 (2^64 - 1) = 2^128 - 1`, so the `u128`
/// cannot overflow.  With `y = 1` it is the in-place addition of a window.
fn mul_row(out: Vec<u64>, off: usize, a: &Vec<u64>, lo: usize, hi: usize, y: u64) -> Vec<u64> {
    let mut o = out;
    let mut carry: u64 = 0;
    let mut i: usize = lo;
    let mut j: usize = off;
    while i < hi {
        let t: u128 = (a[i] as u128) * (y as u128) + (o[j] as u128) + (carry as u128);
        o[j] = t as u64;
        carry = (t >> 64) as u64;
        i += 1;
        j += 1;
    }
    add_carry_at(o, j, carry)
}

/// Subtract `B^k` from `out` in place if `borrow` is `1`, rippling the borrow
/// upwards; the callers never subtract more than `out` holds, so the ripple
/// stops inside it.
fn sub_borrow_at(out: Vec<u64>, k: usize, borrow: u64) -> Vec<u64> {
    let mut o = out;
    let mut bo = borrow;
    let mut j = k;
    while bo != 0 {
        let t: u128 = (o[j] as u128) + 18446744073709551615;
        o[j] = t as u64;
        bo = 1 - ((t >> 64) as u64);
        j += 1;
    }
    o
}

/// `out - a[lo..hi] * B^off`, in place (`out` holds at least that much).
/// Each limb is `B + out[j] - a[i] - borrow`, in `1..2 B`, so the `u128`
/// neither underflows nor overflows, and its high bit is "no borrow".
fn sub_row(out: Vec<u64>, off: usize, a: &Vec<u64>, lo: usize, hi: usize) -> Vec<u64> {
    let mut o = out;
    let mut bo: u64 = 0;
    let mut i: usize = lo;
    let mut j: usize = off;
    while i < hi {
        let t: u128 = (o[j] as u128) + 18446744073709551616 - (a[i] as u128) - (bo as u128);
        o[j] = t as u64;
        bo = 1 - ((t >> 64) as u64);
        i += 1;
        j += 1;
    }
    sub_borrow_at(o, j, bo)
}

/// `a * b`: the window product below into a zero accumulator of `|a| + |b|`
/// limbs, normalised.
pub fn mul(a: &Nat, b: &Nat) -> Nat {
    let la = a.limbs.len();
    let lb = b.limbs.len();
    norm(mul_win(&a.limbs, 0, la, &b.limbs, 0, lb, zeros(la + lb), 0))
}

/// Schoolbook: one multiply-accumulate row of `a[alo..ahi]` per limb of
/// `b[blo..bhi]` (the shorter window, so the inner loop runs over the longer
/// one).
fn mul_rows(out: Vec<u64>, off: usize, a: &Vec<u64>, alo: usize, ahi: usize, b: &Vec<u64>, blo: usize, bhi: usize) -> Vec<u64> {
    let mut o = out;
    let mut j: usize = blo;
    while j < bhi {
        o = mul_row(o, off + (j - blo), a, alo, ahi, b[j]);
        j += 1;
    }
    o
}

/// `out + a[alo..ahi] * b[blo..bhi] * B^off`, in place.  The caller
/// guarantees that `out` has at least `off + (ahi - alo) + (bhi - blo)` limbs
/// and that the sum fits them.  The longer window goes first (the swap is the
/// first branch); then, with `la >= lb` limbs: schoolbook below
/// `KARATSUBA_THRESHOLD`; otherwise, when `a` is at least twice as long, it
/// is halved and both halves accumulate straight into `out`, so an
/// unbalanced product costs `O(la / lb)` balanced ones; otherwise Karatsuba
/// at `k = ceil(la / 2)`: with `a = a0 + a1 * B^k` and `b = b0 + b1 * B^k`,
/// `a * b = z0 + z1 * B^k + z2 * B^(2k)` for `z0 = a0 * b0`, `z2 = a1 * b1`
/// and `z1 = (a0 + a1) * (b0 + b1) - z0 - z2`, three half-size products
/// instead of four, each into its own zero accumulator.  The terms are
/// added into `out` by their significant length (`sig_len`), so the sum's
/// bound alone keeps every index inside `out`.
fn mul_win(a: &Vec<u64>, alo: usize, ahi: usize, b: &Vec<u64>, blo: usize, bhi: usize, out: Vec<u64>, off: usize) -> Vec<u64> {
    let la = ahi - alo;
    let lb = bhi - blo;
    if la < lb {
        mul_win(b, blo, bhi, a, alo, ahi, out, off)
    } else if lb < KARATSUBA_THRESHOLD {
        mul_rows(out, off, a, alo, ahi, b, blo, bhi)
    } else if lb <= la / 2 {
        let mid = alo + la / 2;
        let o = mul_win(a, alo, mid, b, blo, bhi, out, off);
        mul_win(a, mid, ahi, b, blo, bhi, o, off + la / 2)
    } else {
        let k = la - la / 2;
        let am = alo + k;
        let bm = blo + k;
        let z0 = mul_win(a, alo, am, b, blo, bm, zeros(k + k), 0);
        let z2 = mul_win(a, am, ahi, b, bm, bhi, zeros(la + lb - (k + k)), 0);
        let sa = mul_row(mul_row(zeros(k + 1), 0, a, alo, am, 1), 0, a, am, ahi, 1);
        let sb = mul_row(mul_row(zeros(k + 1), 0, b, blo, bm, 1), 0, b, bm, bhi, 1);
        let s = mul_win(&sa, 0, k + 1, &sb, 0, k + 1, zeros(k + k + 2), 0);
        let n0 = sig_len(&z0, z0.len());
        let n2 = sig_len(&z2, z2.len());
        let z1 = sub_row(sub_row(s, 0, &z0, 0, n0), 0, &z2, 0, n2);
        let n1 = sig_len(&z1, z1.len());
        let o1 = mul_row(out, off, &z0, 0, n0, 1);
        let o2 = mul_row(o1, off + k, &z1, 0, n1, 1);
        mul_row(o2, off + (k + k), &z2, 0, n2, 1)
    }
}

/// `Nat.pow a e` for a bignum exponent, exact and unbounded: a power-of-two
/// base `2^k` (one limb) is the shift `1 <<< k * e`, which is how the large
/// powers a kernel folds are written; any other base is square-and-multiply
/// (`pow_go`).  The caller bounds the result (con-leche's maximum `Nat` size,
/// `arena::core::pow_guard`); this function is total and runs out of memory
/// like any allocation when the result is too large.
pub fn pow_nat(a: &Nat, e: &Nat) -> Nat {
    match pow2_log(a) {
        Some(k) => {
            let s = mul(&from_u64(k), e);
            shift_left_nat(&one(), &s)
        }
        None => pow_go(a, e),
    }
}

/// `some k` when `a = 2^k` fits one limb, `none` otherwise.
fn pow2_log(a: &Nat) -> Option<u64> {
    if a.limbs.len() == 1 {
        word_log2_exact(a.limbs[0], 0)
    } else {
        None
    }
}

/// `some (k + j)` when `x = 2^j`, `none` otherwise (`x = 0` included).
fn word_log2_exact(x: u64, k: u64) -> Option<u64> {
    if x == 1 {
        Some(k)
    } else if x == 0 {
        None
    } else if x % 2 == 0 {
        word_log2_exact(x / 2, k + 1)
    } else {
        None
    }
}

/// `a ^ e` by square-and-multiply over the exponent's bits:
/// `a ^ e = (a ^ (e / 2))^2 * a ^ (e % 2)`.
fn pow_go(a: &Nat, e: &Nat) -> Nat {
    if is_zero(e) {
        one()
    } else {
        let h = pow_go(a, &shift_right(e, 1));
        let hh = mul(&h, &h);
        if low_limb(e) % 2 == 0 {
            hh
        } else {
            mul(&hh, a)
        }
    }
}

/// con-leche: ConLeche/Cached/StateC.lean:147-150 natSizeBytes
/// The official kernel's size of `a` in bytes (`lean_nat_size_in_bytes`):
/// 8 bytes per limb, and at least 8.  The cited `8 * (a.log2 / 64 + 1)`,
/// read off the limb count: a normalised `a` with `n > 0` limbs has
/// `a.log2 / 64 = n - 1`.
pub fn size_bytes(a: &Nat) -> Nat {
    let n: u64 = a.limbs.len() as u64;
    let l: u64 = if n == 0 { 1 } else { n };
    shift_left(&from_u64(l), 3)
}

/// con-leche: ConLeche/Cached/StateC.lean:147-150 natSizeBytes
/// `natSizeBytes a > m`: the comparison every refusal of a numeral makes.
pub fn size_bytes_gt(a: &Nat, m: &Nat) -> bool {
    blt(m, &size_bytes(a))
}

// ---------------------------------------------------------------------------
// Division, remainder, gcd
// ---------------------------------------------------------------------------

/// `(a / b, a % b)` by long division, one quotient limb at a time from the
/// top (`dm_limbs`).  A one-limb divisor divides each limb with a `u128`
/// division; a longer one is first normalised — both operands shifted left
/// until the divisor's top limb has its top bit set, which leaves the
/// quotient unchanged and scales the remainder, shifted back at the end — and
/// then each quotient limb is Knuth's algorithm D step (`dm_step`).
///
/// Lean's conventions on a zero divisor: `a / 0 = 0` and `a % 0 = a`.
pub fn div_mod(a: &Nat, b: &Nat) -> (Nat, Nat) {
    if is_zero(b) {
        (zero(), clone(a))
    } else if b.limbs.len() == 1 {
        dm_run(a, b)
    } else {
        let s = norm_shift(b.limbs[b.limbs.len() - 1]);
        let an = shift_left(a, s);
        let bn = shift_left(b, s);
        let (q, rn) = dm_run(&an, &bn);
        (q, shift_right(&rn, s))
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

/// The left shift that sets the top bit of `top` (`top != 0`): its number of
/// leading zeros, at most `63`.
fn norm_shift(top: u64) -> u64 {
    let mut x = top;
    let mut s: u64 = 0;
    while s < 63 && x < 0x8000_0000_0000_0000 {
        x = x << 1;
        s += 1;
    }
    s
}

/// The long division proper, `b != 0`: the quotient limbs come out most
/// significant first and are reversed into place.
fn dm_run(a: &Nat, b: &Nat) -> (Nat, Nat) {
    let n = a.limbs.len();
    let (qrev, r) = dm_limbs(a, b, n, Vec::with_capacity(n), zero());
    let k = qrev.len();
    (norm(rev_copy_from(&qrev, k, Vec::with_capacity(k))), r)
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

/// The outer division recursion: limb `i - 1` of the dividend, downwards,
/// with `rem < b` the remainder of the limbs above it.
fn dm_limbs(a: &Nat, b: &Nat, i: usize, qrev: Vec<u64>, rem: Nat) -> (Vec<u64>, Nat) {
    if i == 0 {
        (qrev, rem)
    } else {
        let (ql, rem2) = dm_step(b, &rem, a.limbs[i - 1]);
        let mut q = qrev;
        q.push(ql);
        dm_limbs(a, b, i - 1, q, rem2)
    }
}

/// `x + 2^64 * r`: the remainder with the next dividend limb brought down.
fn prepend_limb(x: u64, r: &Nat) -> Nat {
    let mut v: Vec<u64> = Vec::with_capacity(r.limbs.len() + 1);
    v.push(x);
    norm(copy_from(&r.limbs, 0, r.limbs.len(), v))
}

/// One quotient limb: for `rem < b`, with `t = rem * 2^64 + x`, the pair
/// `(t / b, t % b)` (the quotient fits a limb because `rem < b`).
///
/// A one-limb `b` is one `u128` division.  Otherwise (`m = |b| >= 2`) this
/// is Knuth's step: the estimate `q̂ = min(t[m..m-1] / b[m-1], 2^64 - 1)`
/// from the top two limbs of `t` and the top limb of `b` is never below the
/// true quotient, and `dm_correct` walks it down to it.  On a normalised `b`
/// (top bit set) `q̂` is at most two too large (Knuth, TAOCP 4.3.1,
/// Theorem B); correctness does not depend on it.
fn dm_step(b: &Nat, rem: &Nat, x: u64) -> (u64, Nat) {
    let m = b.limbs.len();
    if m == 1 {
        let d = b.limbs[0] as u128;
        let t: u128 = ((low_limb(rem) as u128) << 64) + (x as u128);
        let q = (t / d) as u64;
        let r = (t % d) as u64;
        (q, from_u64(r))
    } else {
        let t = prepend_limb(x, rem);
        let top = b.limbs[m - 1] as u128;
        let t2: u128 = ((limb(&t.limbs, m) as u128) << 64) + (limb(&t.limbs, m - 1) as u128);
        let qe = t2 / top;
        let qhat: u64 = if qe > 18446744073709551615 { 18446744073709551615 } else { qe as u64 };
        let p = mul_u64(b, qhat);
        dm_correct(b, &t, qhat, p)
    }
}

/// The correction of algorithm D: given `p = q * b` with `q` at least the true
/// quotient `t / b`, step `q` down while `q * b > t`, then the remainder is
/// `t - q * b`.
fn dm_correct(b: &Nat, t: &Nat, q: u64, p: Nat) -> (u64, Nat) {
    let mut qq = q;
    let mut pp = p;
    while blt(t, &pp) {
        qq -= 1;
        pp = sub(&pp, b);
    }
    (qq, sub(t, &pp))
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
    norm(and_from(&a.limbs, &b.limbs, 0, n, Vec::with_capacity(n)))
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
    norm(or_from(&a.limbs, &b.limbs, 0, n, Vec::with_capacity(n)))
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
    norm(xor_from(&a.limbs, &b.limbs, 0, n, Vec::with_capacity(n)))
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

    /// `pow_nat` at a machine-word exponent, the form the tests below use.
    fn pow(a: &Nat, e: u64) -> Nat {
        pow_nat(a, &from_u64(e))
    }

    /// The power-of-two shortcut and the square-and-multiply loop agree, and
    /// `size_bytes` is the official kernel's measure.
    #[test]
    fn pow_paths_and_size() {
        for k in 0..6u64 {
            for e in 0..70u64 {
                let a = from_u64(1 << k);
                assert!(eqn(&pow_nat(&a, &from_u64(e)), &pow_go(&a, &from_u64(e))), "{k} {e}");
            }
        }
        assert!(eqn(&pow_nat(&zero(), &zero()), &one()));
        assert!(is_zero(&pow_nat(&zero(), &from_u64(4000000000))));
        assert!(eqn(&pow_nat(&one(), &from_u64(4294967295)), &one()));
        assert!(eqn(&size_bytes(&zero()), &from_u64(8)));
        assert!(eqn(&size_bytes(&from_u64(u64::MAX)), &from_u64(8)));
        assert!(eqn(&size_bytes(&of_u128(1 << 64)), &from_u64(16)));
        assert!(size_bytes_gt(&of_u128(1 << 64), &from_u64(15)));
        assert!(!size_bytes_gt(&of_u128(1 << 64), &from_u64(16)));
        // `nat_size_ok`'s `2^(2^24)`: `2^18` zero limbs and a one, pushed at a
        // recursion depth of the count's bit length (this runs unoptimised).
        let big = pow_nat(&from_u64(2), &from_u64(1 << 24));
        assert_eq!(big.limbs.len(), (1 << 18) + 1);
        assert_eq!(big.limbs[1 << 18], 1);
        assert!(eqn(&size_bytes(&big), &from_u64(8 * ((1 << 18) + 1))));
    }

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
    fn bignum_shift_amounts() {
        // task #98-SHIFT: the amount is a `Nat`, with no `u64` bound
        let two64 = of_limbs(&[0, 1]); // 2^64
        let two70 = of_limbs(&[0, 64]); // 2^70
        let small = of_u128(12345);
        assert!(is_zero(&shift_right_nat(&small, &two64)));
        assert!(is_zero(&shift_right_nat(&small, &two70)));
        assert!(is_zero(&shift_right_nat(&of_limbs(&[M, M, M]), &two70)));
        assert!(is_zero(&shift_left_nat(&zero(), &two70)));
        assert!(is_zero(&shift_left_nat(&zero(), &two64)));
        // the `64 * len` boundary: exactly all limbs shifted out, and one bit less
        let a = of_limbs(&[M, 1]); // two limbs
        assert!(is_zero(&shift_right_nat(&a, &of_u128(128))));
        assert!(is_zero(&shift_right_nat(&a, &of_u128(129))));
        assert_eq!(shift_right_nat(&a, &of_u128(127)).limbs, Vec::<u64>::new());
        assert_eq!(shift_right_nat(&a, &of_u128(64)).limbs, vec![1]);
        assert_eq!(shift_right_nat(&a, &of_u128(63)).limbs, vec![3]);
        let b = of_limbs(&[M, M]);
        assert_eq!(shift_right_nat(&b, &of_u128(127)).limbs, vec![1]);
        assert!(is_zero(&shift_right_nat(&b, &of_u128(128))));
        // agreement with the word-amount shifts on small amounts
        for k in [0u64, 1, 5, 63, 64, 65, 127, 128, 129, 200] {
            let kn = from_u64(k);
            assert!(eqn(&shift_left_nat(&a, &kn), &shift_left(&a, k)), "shl k = {k}");
            assert!(eqn(&shift_right_nat(&a, &kn), &shift_right(&a, k)), "shr k = {k}");
        }
        // an amount whose low limb is not the amount itself
        assert!(is_zero(&shift_right_nat(&a, &of_limbs(&[1, 1]))));
        assert!(is_zero(&shift_right_nat(&zero(), &two70)));
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

    /// The schoolbook product on its own: `mul_rows` over the whole operands.
    fn mul_base(a: &Nat, b: &Nat) -> Nat {
        let la = a.limbs.len();
        let lb = b.limbs.len();
        norm(mul_rows(zeros(la + lb), 0, &a.limbs, 0, la, &b.limbs, 0, lb))
    }

    fn rand_limbs(rng: &mut Rng, n: usize) -> Nat {
        let mut v: Vec<u64> = Vec::new();
        for _ in 0..n {
            v.push(rng.next());
        }
        norm(v)
    }

    /// The fast paths of `mul` (Karatsuba, halving the longer operand)
    /// against the schoolbook base case, across sizes around the threshold
    /// and unbalanced shapes, plus all-ones operands (maximal carries).
    #[test]
    fn mul_paths_agree_with_schoolbook() {
        let mut rng = Rng(0x0123_4567_89ab_cdef);
        let t = KARATSUBA_THRESHOLD;
        let sizes = [1, 2, t - 1, t, t + 1, 2 * t - 1, 2 * t, 2 * t + 1, 3 * t + 5, 5 * t];
        for &n in &sizes {
            for &m in &sizes {
                let a = rand_limbs(&mut rng, n);
                let b = rand_limbs(&mut rng, m);
                let p = mul(&a, &b);
                assert!(wf(&p));
                assert!(eqn(&p, &mul_base(&a, &b)), "mul {n} x {m}");
                assert!(eqn(&p, &mul(&b, &a)), "commuted {n} x {m}");
            }
        }
        for &(n, m) in &[(10 * t, t), (7 * t + 3, t + 2), (40 * t, 2 * t + 1), (9519, 40)] {
            let a = rand_limbs(&mut rng, n);
            let b = rand_limbs(&mut rng, m);
            assert!(eqn(&mul(&a, &b), &mul_base(&a, &b)), "unbalanced {n} x {m}");
        }
        for &(n, m) in &[(2 * t - 1, t), (2 * t, t + 1), (2 * t + 1, t + 1), (3 * t, 2 * t), (5 * t, 2 * t)] {
            let x = of_limbs(&vec![M; n]);
            let y = of_limbs(&vec![M; m]);
            assert!(eqn(&mul(&x, &y), &mul_base(&x, &y)), "all ones {n} x {m}");
        }
        for &n in &[t, 2 * t + 1, 4 * t] {
            let ones = of_limbs(&vec![M; n]);
            let p = mul(&ones, &ones);
            assert!(eqn(&p, &mul_base(&ones, &ones)), "all ones {n}");
            // (B^n - 1)^2 = B^2n - 2 B^n + 1
            let bn = shift_left(&one(), 64 * n as u64);
            assert!(eqn(&add(&p, &add(&bn, &bn)), &add(&mul_base(&bn, &bn), &one())));
        }
        // operands with zero runs, so the halves normalise to fewer limbs
        let mut v = vec![0u64; 3 * t];
        v[0] = 5;
        v[3 * t - 1] = 7;
        let a = of_limbs(&v);
        let b = rand_limbs(&mut rng, 2 * t);
        assert!(eqn(&mul(&a, &b), &mul_base(&a, &b)));
        assert!(eqn(&mul(&a, &a), &mul_base(&a, &a)));
        assert!(is_zero(&mul(&a, &zero())));
    }

    fn check_div(a: &Nat, b: &Nat) {
        let (q, r) = div_mod(a, b);
        assert!(wf(&q) && wf(&r));
        assert!(eqn(&add(&mul(&q, b), &r), a), "q b + r = a: {:?} {:?}", a.limbs, b.limbs);
        assert!(blt(&r, b), "r < b: {:?} {:?}", a.limbs, b.limbs);
    }

    /// `q * b + r = a` and `r < b` across divisor shapes: one and two limbs,
    /// top limb `1` (the largest normalisation shift) and `2^64 - 1` (none),
    /// `a < b`, `a = b`, exact quotients, and the near-boundary values that
    /// make the estimate `q̂` too large and force the correction loop.
    #[test]
    fn div_identities() {
        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..300 {
            let n = 1 + (rng.next() % 12) as usize;
            let m = 1 + (rng.next() % 6) as usize;
            let a = rand_limbs(&mut rng, n);
            let b = rand_limbs(&mut rng, m);
            if !is_zero(&b) {
                check_div(&a, &b);
                check_div(&b, &clone(&a));
            }
            let mut bt = b.limbs.clone();
            let l = bt.len();
            bt[l - 1] = 1;
            check_div(&a, &of_limbs(&bt));
            bt[l - 1] = M;
            check_div(&a, &of_limbs(&bt));
            check_div(&a, &clone(&a));
            let (q, r) = div_mod(&mul(&a, &b), &b);
            if !is_zero(&b) {
                assert!(eqn(&q, &a) && is_zero(&r), "(a b) / b");
            }
        }
        for &d in &[1u64, 2, 3, 7, 1 << 63, M, M - 1] {
            check_div(&of_limbs(&[M, M, M, M]), &from_u64(d));
            check_div(&of_limbs(&[0, 0, 0, 1]), &from_u64(d));
        }
        // q̂ overshoots: divisor top limbs just above a power of two with a
        // large second limb, dividend just below a multiple
        let hard: [(&[u64], &[u64]); 6] = [
            (&[0, 0, 0x8000_0000_0000_0000], &[1, 0x8000_0000_0000_0000]),
            (&[0, M, 0x7fff_ffff_ffff_ffff], &[M, 0x8000_0000_0000_0000]),
            (&[0, 0, M - 1, M], &[M, M, M]),
            (&[3, 0, 0x8000_0000_0000_0000, 0x7fff_ffff_ffff_ffff], &[1, 0, 0x8000_0000_0000_0000]),
            (&[0, 0, 0, 0x8000_0000_0000_0000], &[1, 0, 0x8000_0000_0000_0000]),
            (&[M, M, M, M, M], &[M, 1]),
        ];
        for (a, b) in hard.iter() {
            check_div(&of_limbs(a), &of_limbs(b));
        }
        let b = of_limbs(&[1, 0, 0x8000_0000_0000_0000]);
        let q = of_limbs(&[M, M]);
        let a = sub(&mul(&q, &b), &one());
        check_div(&a, &b);
        assert!(eqn(&div(&add(&a, &one()), &b), &q));
        // big operands
        let a = rand_limbs(&mut rng, 300);
        let b = rand_limbs(&mut rng, 70);
        check_div(&a, &b);
        check_div(&a, &of_limbs(&[M, 1]));
    }

    /// `dm_step` directly, on normalised two- and three-limb divisors whose
    /// top limb is just above `2^63` and whose lower limbs are large (where
    /// the estimate, which reads only the top limb, overshoots): the result
    /// is exact, the estimate is within Knuth's bound of two, and some
    /// estimates were in fact corrected.
    #[test]
    fn dm_step_corrects_the_estimate() {
        let mut rng = Rng(0x5851_f42d_4c95_7f2d);
        let mut corrected = 0;
        for round in 0..2000 {
            let m = 2 + round % 2;
            let mut bv: Vec<u64> = Vec::new();
            for _ in 0..m - 1 {
                bv.push(M - rng.next() % 4);
            }
            bv.push((1 << 63) | (rng.next() % 4));
            let top = bv[m - 1];
            let b = norm(bv);
            // any `rem < b`: random limbs under a top limb below `b`'s
            let mut rv: Vec<u64> = Vec::new();
            for _ in 0..m - 1 {
                rv.push(rng.next());
            }
            rv.push(rng.next() % top);
            let rem = norm(rv);
            let x = rng.next();
            let (q, r) = dm_step(&b, &rem, x);
            let t = prepend_limb(x, &rem);
            assert!(eqn(&add(&mul(&from_u64(q), &b), &r), &t));
            assert!(blt(&r, &b));
            let t2 = ((limb(&t.limbs, m) as u128) << 64) + (limb(&t.limbs, m - 1) as u128);
            let qe = t2 / (b.limbs[m - 1] as u128);
            let qhat = if qe > (M as u128) { M } else { qe as u64 };
            assert!(qhat >= q && qhat - q <= 2, "Knuth's bound");
            if qhat > q {
                corrected += 1;
            }
        }
        assert!(corrected > 0);
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
