//! Decimal notation for `ron::Nat`: the one runtime primitive the *parser*
//! needs that the checker never does.  No Lean file of its own.
//!
//! `Scan/Fast.lean`'s `readNat` produces a Lean `Nat` straight from the
//! literal's digits, because Lean's `Nat` overflows into GMP by itself
//! (`Fast.lean`'s note: "a `natVal` literal needs no special"…); the port has
//! its own bignum (`ron::nat`, DESIGN.md §3.3), so the digits have to be
//! read.  The scanner keeps them as bytes (`scan_types::ExprRec::NatVal`) and
//! `export_c` calls this when it builds the node.
//!
//! **Why here and not in `ron::nat`.**  `crates/con-ron-dump/src/natdec.rs`
//! used to carry this, and its module note said `ron::nat` "has no
//! `from_decimal` and is not getting one: decimal is an I/O concern, nothing
//! the checker decides reads it".  That was true while the parser was
//! unverified and is not any more — the parser is in the core, so a `natVal`
//! literal is read inside the extraction.  It lives in `frontend/` rather
//! than in `ron/` for a concrete reason: the digit loops are loops, and
//! `crates/con-ron-core/src/frontend/` is the one directory DESIGN.md §3.4
//! exempts.  `con-ron-dump` keeps `natdec` for its own `to_decimal`, the
//! direction no checker reads.
//!
//! The algorithm.  A run of at most `BASE_DIGITS` digits is read nineteen
//! digits at a time, because `10^19` is the largest power of ten below
//! `2^64`, so a chunk is one `mul_add_small` over the limbs: `O(n² / 19)`
//! for `n` digits, and the cheapest method up to a few thousand digits
//! (lean4export's literals are a handful).  A longer run is divided and
//! conquered (`read_split`): `value(hi ++ lo) = value(hi) · 10^|lo| +
//! value(lo)`, where `lo` has exactly `19 · 2^t` digits, so every `10^|lo|`
//! is one entry of a table of powers `10^(19 · 2^t)` built once per literal
//! by repeated squaring (`power_table`), and the combination is
//! `ron::nat`'s Karatsuba `mul` and `add`: `O(M(n) log n)`.
//! `con-ron-dump`'s `natdec` keeps the chunk loop alone.

use crate::ron::nat;
use crate::ron::nat::Nat;

/// con-leche: none — digits per limb-sized chunk: `10^19 < 2^64 < 10^20`
const CHUNK_DIGITS: usize = 19;

/// con-leche: none — the longest run `read_split` reads with the chunk loop
/// alone: 256 chunks, measured (DESIGN.md task #159); below about this length
/// the chunk loop's `O(n²)` is cheaper than the split's products
const BASE_DIGITS: usize = 4864;

/// con-leche: none — `limbs := limbs * m + a`, for machine-word `m` and `a`
/// One pass with a `u128` accumulator, exactly `ron::nat::mul_u64_from`'s
/// shape with the initial carry set to `a`: `v[i] * m + carry` is at most
/// `(2^64 - 1)² + (2^64 - 1) = 2^128 - 2^64`, so the product cannot overflow
/// and the truncating cast back to `u64` takes exactly the low half.
fn mul_add_small(limbs: &Vec<u64>, m: u64, a: u64) -> Vec<u64> {
    let n = limbs.len();
    let mut out: Vec<u64> = Vec::with_capacity(n + 1);
    let mut carry: u64 = a;
    let mut i = 0usize;
    while i < n {
        let t: u128 = (limbs[i] as u128) * (m as u128) + (carry as u128);
        let lo: u64 = t as u64;
        out.push(lo);
        carry = (t >> 64) as u64;
        i += 1;
    }
    if carry != 0 {
        out.push(carry);
    }
    out
}

/// con-leche: none — Lean's `String.toNat?` on a `natVal` literal
/// The value of a decimal literal: no sign, no separators, at least one
/// digit.  Leading zeros are accepted, as Lean's `String.toNat?` accepts
/// them; lean4export never emits one.  `None` is "not a decimal literal",
/// which the caller reports as `ErrTag::BadNatVal`'s sentence.  A literal of
/// at most `BASE_DIGITS` digits is one chunk loop; a longer one builds the
/// power table and splits.
pub fn from_decimal(digits: &[u8]) -> Option<Nat> {
    if digits.len() == 0 {
        return None;
    }
    if all_digits(digits) {
        let n = digits.len();
        if n <= BASE_DIGITS {
            Some(read_chunks(digits))
        } else {
            let pows = power_table(n);
            Some(read_split(digits, &pows))
        }
    } else {
        None
    }
}

/// con-leche: none — the validating loop behind `from_decimal`, split out
/// because Aeneas accepts a `return` out of a loop only when what follows the
/// loop is trivial: "Early returns inside of loops are not supported yet"
/// otherwise (AENEAS_FINDINGS §2.6)
fn all_digits(digits: &[u8]) -> bool {
    let n = digits.len();
    let mut i = 0usize;
    while i < n {
        let c = digits[i];
        if c < 48 || c > 57 {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — the chunk loop behind `from_decimal`, split out because
/// Aeneas' `-loops-to-rec` duplicates whatever follows a loop into every one
/// of its exits (DESIGN.md §3.4's loop rule)
fn from_decimal_go(digits: &[u8], start: usize, acc: Vec<u64>) -> Vec<u64> {
    let n = digits.len();
    let mut limbs = acc;
    let mut i = start;
    while i < n {
        let mut k = n - i;
        if k > CHUNK_DIGITS {
            k = CHUNK_DIGITS;
        }
        let mut chunk: u64 = 0;
        let mut pow: u64 = 1;
        let mut j = 0usize;
        while j < k {
            chunk = chunk * 10 + ((digits[i + j] - 48) as u64);
            pow = pow * 10;
            j += 1;
        }
        limbs = mul_add_small(&limbs, pow, chunk);
        i += k;
    }
    limbs
}

/// con-leche: none — the value of a run of digits by the chunk loop alone,
/// `O(n² / 19)` for `n` digits: the base case of `read_split`
fn read_chunks(digits: &[u8]) -> Nat {
    nat::norm(from_decimal_go(digits, 0, Vec::new()))
}

/// con-leche: none — `P[t] = 10^(19 · 2^t)` for every `t` with
/// `2 · 19 · 2^t ≤ n`, by repeated squaring from `P[0] = 10^19`
/// The caller has `n > BASE_DIGITS ≥ 38`, so the table is never empty;
/// `d + d <= n - d - d` is `4 d ≤ n` without the overflow.
fn power_table(n: usize) -> Vec<Nat> {
    let mut pows: Vec<Nat> = Vec::new();
    pows.push(nat::from_u64(10000000000000000000));
    let mut d = CHUNK_DIGITS;
    let mut t = 0usize;
    while d + d <= n - d - d {
        let sq = nat::mul(&pows[t], &pows[t]);
        pows.push(sq);
        d = d + d;
        t += 1;
    }
    pows
}

/// con-leche: none — the largest `t` with `2 · 19 · 2^t ≤ len`, and
/// `19 · 2^t`
/// The caller has `len > 38`; `d + d <= len - d - d` is `4 d ≤ len`.
fn split_level(len: usize) -> (usize, usize) {
    let mut d = CHUNK_DIGITS;
    let mut t = 0usize;
    while d + d <= len - d - d {
        d = d + d;
        t += 1;
    }
    (t, d)
}

/// con-leche: none — the value of a run of digits, divide and conquer
/// At most `BASE_DIGITS` digits: the chunk loop.  Longer: with `d = 19 · 2^t`
/// the largest such length with `2 d ≤ len` (`split_level`), the run is a
/// high part of `len - d` digits, at least half of it and less than three
/// quarters, and a low part of exactly `d`; its value is
/// `high · 10^d + low` with `10^d = pows[t]`.  A low part halves exactly at
/// every level, a high part shrinks by at least a quarter, so the depth is
/// `O(log len)`, and with `nat::mul`'s Karatsuba the whole read is
/// `O(M(n) log n)`.  Taking the high part as the longer one keeps the largest
/// power at most half the literal, so the table's last squaring is a quarter
/// of the literal's size.
fn read_split(digits: &[u8], pows: &Vec<Nat>) -> Nat {
    let len = digits.len();
    if len <= BASE_DIGITS {
        read_chunks(digits)
    } else {
        let (t, d) = split_level(len);
        let m = len - d;
        let hi = read_split(&digits[0..m], pows);
        let lo = read_split(&digits[m..len], pows);
        let shifted = nat::mul(&hi, &pows[t]);
        nat::add(&shifted, &lo)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ron::nat;

    fn n(s: &str) -> Option<Nat> {
        from_decimal(s.as_bytes())
    }

    fn u(x: u64) -> Nat {
        nat::from_u64(x)
    }

    #[test]
    fn small_literals() {
        assert!(nat::beq(&n("0").unwrap(), &u(0)));
        assert!(nat::beq(&n("1").unwrap(), &u(1)));
        assert!(nat::beq(&n("9").unwrap(), &u(9)));
        assert!(nat::beq(&n("10").unwrap(), &u(10)));
        assert!(nat::beq(&n("123456789").unwrap(), &u(123456789)));
        assert!(nat::beq(&n("18446744073709551615").unwrap(), &u(u64::MAX)));
        // leading zeros, as `String.toNat?` accepts them
        assert!(nat::beq(&n("007").unwrap(), &u(7)));
        assert!(nat::beq(&n("0000000000000000000000").unwrap(), &u(0)));
    }

    #[test]
    fn chunk_boundaries() {
        // 19, 20, 38 and 39 digits: one chunk, two, exactly two, three
        for k in [1usize, 18, 19, 20, 37, 38, 39, 57] {
            let s: String = std::iter::repeat('9').take(k).collect();
            let v = n(&s).expect("all nines is a literal");
            // 10^k - 1
            let mut want = nat::from_u64(1);
            for _ in 0..k {
                want = nat::mul(&want, &u(10));
            }
            want = nat::sub(&want, &u(1));
            assert!(nat::beq(&v, &want), "10^{} - 1", k);
        }
    }

    #[test]
    fn round_trips_against_the_dump_writer_algorithm() {
        // a value with several limbs: 2^200 + 12345
        let mut v = nat::from_u64(1);
        for _ in 0..200 {
            v = nat::mul(&v, &u(2));
        }
        v = nat::add(&v, &u(12345));
        // decimal of 2^200 + 12345
        let s = "1606938044258990275541962092341162602522202993782792835313721";
        assert!(nat::beq(&n(s).unwrap(), &v));
    }

    #[test]
    fn not_a_literal() {
        assert!(n("").is_none());
        assert!(n("12a").is_none());
        assert!(n("-1").is_none());
        assert!(n(" 1").is_none());
        assert!(n("1 ").is_none());
        assert!(n("+").is_none());
    }
    /// Deterministic pseudo-random digits (xorshift64), the first one nonzero
    /// unless `lead` asks for leading zeros.
    fn digits(len: usize, seed: u64, lead: usize) -> Vec<u8> {
        let mut x: u64 = seed | 1;
        let mut s: Vec<u8> = Vec::with_capacity(len);
        for i in 0..len {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            let c = if i < lead { 0 } else { (x % 10) as u8 };
            s.push(b'0' + c);
        }
        s
    }

    /// `from_decimal` (the split above `BASE_DIGITS`) against the chunk loop
    /// alone.
    fn agrees(s: &[u8]) {
        let v = from_decimal(s).expect("a run of digits is a literal");
        assert!(nat::beq(&v, &read_chunks(s)), "length {}", s.len());
    }

    fn boundary_lengths() -> Vec<usize> {
        let mut ls: Vec<usize> = vec![1, 18, 19, 20, 37, 38, 39];
        for k in [BASE_DIGITS - 1, BASE_DIGITS, BASE_DIGITS + 1] {
            ls.push(k);
        }
        for t in 0..14u32 {
            let d = CHUNK_DIGITS << t;
            for k in [d - 1, d, d + 1, 2 * d - 1, 2 * d, 2 * d + 1] {
                ls.push(k);
            }
        }
        ls.push(300_000);
        ls
    }

    /// `ron::nat`'s untouched `*_from` helpers recurse once per limb, which
    /// an unoptimised build does not turn into a loop: the long literals run
    /// on a large stack, as the checker's own threads do.
    fn on_big_stack(f: fn()) {
        std::thread::Builder::new()
            .stack_size(1 << 30)
            .spawn(f)
            .expect("spawn")
            .join()
            .expect("test thread");
    }

    #[test]
    fn split_agrees_with_the_chunk_loop() {
        on_big_stack(|| {
            for (j, &len) in boundary_lengths().iter().enumerate() {
                agrees(&digits(len, 0x9e37_79b9_7f4a_7c15 ^ (j as u64), 0));
            }
        });
    }

    #[test]
    fn split_leading_zeros_and_nines() {
        on_big_stack(split_leading_zeros_and_nines_body);
    }

    fn split_leading_zeros_and_nines_body() {
        for &len in &[BASE_DIGITS + 1, 2 * BASE_DIGITS + 5, 5000, 40_000] {
            // leading zeros straddling the split points
            for lead in [1, len / 3, len - 19, len - 1, len] {
                agrees(&digits(len, len as u64, lead));
            }
            // all nines: 10^len - 1
            let s: Vec<u8> = std::iter::repeat(b'9').take(len).collect();
            agrees(&s);
            let mut want = nat::one();
            for _ in 0..len {
                want = nat::mul(&want, &u(10));
            }
            want = nat::sub(&want, &u(1));
            assert!(nat::beq(&from_decimal(&s).unwrap(), &want), "10^{} - 1", len);
        }
    }

    #[test]
    fn power_table_is_the_powers() {
        let pows = power_table(19 * 128);
        assert_eq!(pows.len(), 7);
        assert_eq!(power_table(19 * 128 - 1).len(), 6);
        let mut want = nat::from_u64(10000000000000000000);
        for t in 0..pows.len() {
            assert!(nat::beq(&pows[t], &want), "P[{}]", t);
            want = nat::mul(&want, &want);
        }
        assert_eq!(split_level(38), (0, 19));
        assert_eq!(split_level(75), (0, 19));
        assert_eq!(split_level(76), (1, 38));
        assert_eq!(split_level(151), (1, 38));
        assert_eq!(split_level(152), (2, 76));
    }
}
