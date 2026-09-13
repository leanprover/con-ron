//! Decimal notation for `ron::Nat` — the one scalar of the dump format the
//! core has no codec for.
//!
//! `crates/con-ron-core/src/ron/nat.rs` has no `from_decimal`/`to_decimal` and
//! is not getting one: decimal is an I/O concern, nothing the checker decides
//! reads it, and DESIGN.md §3.4's subset would pay for the digit loop in
//! generated Lean that no lemma mentions.  So it lives here, in the unverified
//! crate, where ordinary Rust is allowed.
//!
//! Both directions work on `Nat::limbs` (little-endian `u64`, no trailing zero
//! limb) with `u128` intermediates, nineteen digits at a time — `10^19 < 2^64`
//! is the largest power of ten that fits a limb.  That is `O(limbs^2 / 19)`
//! rather than the `O(bits * limbs)` of `nat::div_mod`'s bit-at-a-time long
//! division, which matters only in principle: the largest `Literal.natVal` in
//! the corpus is a handful of digits.  The only entry point into the core is
//! `nat::norm`, which re-establishes the representation invariant.

use con_ron_core::ron::nat;
use con_ron_core::ron::nat::Nat;

/// Digits per limb-sized chunk: `10^19 < 2^64 < 10^20`.
const CHUNK_DIGITS: usize = 19;

/// `10^19`.
const CHUNK_POW: u64 = 10_000_000_000_000_000_000;

/// `limbs := limbs * m + a`, for machine-word `m` and `a`.
fn mul_add_small(limbs: &mut Vec<u64>, m: u64, a: u64) {
    let mut carry: u128 = a as u128;
    for l in limbs.iter_mut() {
        let t = (*l as u128) * (m as u128) + carry;
        *l = t as u64;
        carry = t >> 64;
    }
    while carry != 0 {
        limbs.push(carry as u64);
        carry >>= 64;
    }
}

/// `limbs := limbs / d`, returning `limbs % d`.  `d != 0`.
fn div_small(limbs: &mut [u64], d: u64) -> u64 {
    let mut rem: u128 = 0;
    for i in (0..limbs.len()).rev() {
        let cur = (rem << 64) | (limbs[i] as u128);
        limbs[i] = (cur / (d as u128)) as u64;
        rem = cur % (d as u128);
    }
    rem as u64
}

/// Parse a `<nat>` field: decimal, no sign, no separators.  Leading zeros are
/// accepted (`Pins.lean`'s `String.toNat?` accepts them too); the writer never
/// emits one.
pub fn from_decimal(s: &str) -> Result<Nat, String> {
    let b = s.as_bytes();
    if b.is_empty() {
        return Err("expected a decimal number, got an empty field".to_string());
    }
    if !b.iter().all(|c| c.is_ascii_digit()) {
        return Err(format!("expected a decimal number, got '{}'", s));
    }
    let mut limbs: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < b.len() {
        let k = core::cmp::min(CHUNK_DIGITS, b.len() - i);
        let mut chunk: u64 = 0;
        let mut pow: u64 = 1;
        for j in 0..k {
            chunk = chunk * 10 + (b[i + j] - b'0') as u64;
            pow *= 10;
        }
        mul_add_small(&mut limbs, pow, chunk);
        i += k;
    }
    Ok(nat::norm(limbs))
}

/// Render a `Nat` as a `<nat>` field: decimal, no leading zeros.
pub fn to_decimal(n: &Nat) -> String {
    if nat::is_zero(n) {
        return "0".to_string();
    }
    let mut limbs: Vec<u64> = n.limbs.clone();
    let mut groups: Vec<u64> = Vec::new();
    while !limbs.is_empty() {
        groups.push(div_small(&mut limbs, CHUNK_POW));
        while limbs.last() == Some(&0) {
            limbs.pop();
        }
    }
    let mut out = String::new();
    let top = groups.len() - 1;
    out.push_str(&groups[top].to_string());
    for g in groups[..top].iter().rev() {
        out.push_str(&format!("{:0>width$}", g, width = CHUNK_DIGITS));
    }
    out
}
