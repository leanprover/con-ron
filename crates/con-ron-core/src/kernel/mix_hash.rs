//! Port of `ConLeche/Kernel/MixHash.lean` — the 32-bit hash combinator of
//! `Expr` nodes.
//!
//! `mix_hash32 h k` is the block step of MurmurHash3_x86_32 with
//! `k = ROTL32(k, 15)` replaced by `k ^= k >> 15`: the arithmetic of
//! lean4#16107's `lean_uint32_mix_hash`, operation for operation.  With
//! either argument fixed it is a bijection in the other, so on a chain
//! `x ↦ C[x]` with a fixed context (an accumulator `acc + 1`, a successor
//! tower) the node hashes repeat only by returning to the start's
//! (con-leche task #638).

/// con-leche: ConLeche/Kernel/MixHash.lean:43-49 mixHash32
/// The 32-bit hash combinator.  Lean's `UInt32` `*` and `+` wrap, hence
/// `wrapping_mul`/`wrapping_add`; the rotation is the cited shift pair.
pub fn mix_hash32(h: u32, k: u32) -> u32 {
    let k1: u32 = k.wrapping_mul(0xcc9e2d51);
    let k2: u32 = k1 ^ (k1 >> 15);
    let k3: u32 = k2.wrapping_mul(0x1b873593);
    let h1: u32 = h ^ k3;
    let h2: u32 = (h1 << 13) | (h1 >> 19);
    h2.wrapping_mul(5).wrapping_add(0xe6546b64)
}

#[cfg(test)]
mod tests {
    use super::mix_hash32;

    #[test]
    fn mix_hash32_agrees_with_upstreams_c() {
        // con-leche's `tests/ConLecheTests/ExprHashTests.lean`: values
        // computed from lean4#16107's `lean_uint32_mix_hash`.
        assert_eq!(mix_hash32(0, 0), 3864292196);
        assert_eq!(mix_hash32(1, 2), 3704777237);
        assert_eq!(mix_hash32(29, 0xdeadbeef), 3395699167);
        assert_eq!(mix_hash32(0xffffffff, 0xffffffff), 1284620446);
        assert_eq!(mix_hash32(0x12345678, 0x9abcdef0), 733402588);
    }
}
