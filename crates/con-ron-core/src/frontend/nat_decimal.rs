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
//! The algorithm is `natdec`'s: nineteen digits at a time, because `10^19` is
//! the largest power of ten below `2^64`, so a chunk is one `mul_add_small`
//! over the limbs.  `O(limbs² / 19)` rather than the `O(bits × limbs)` of
//! `nat::div_mod`'s bit-at-a-time long division — which matters only in
//! principle: the largest `Literal.natVal` in the corpus is a handful of
//! digits.

use crate::ron::nat;
use crate::ron::nat::Nat;

/// con-leche: none — digits per limb-sized chunk: `10^19 < 2^64 < 10^20`
const CHUNK_DIGITS: usize = 19;

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
/// which the caller reports as `ErrTag::BadNatVal`'s sentence.
pub fn from_decimal(digits: &[u8]) -> Option<Nat> {
    let n = digits.len();
    if n == 0 {
        return None;
    }
    let mut i = 0usize;
    while i < n {
        let c = digits[i];
        if c < 48 || c > 57 {
            return None;
        }
        i += 1;
    }
    Some(nat::norm(from_decimal_go(digits, 0, Vec::new())))
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
}
