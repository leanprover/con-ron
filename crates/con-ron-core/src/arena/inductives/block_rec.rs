//! `arena::inductives::block_rec` — the recursor stage's shared pieces.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/BlockRec.lean`, which is
//! `ConLeche/Kernel/Inductives/BlockRec.lean` over handles: the elimination
//! guard, official's `elim_only_at_universe_zero` said declaratively.

use super::block_parts::{shape_k, shape_num_ctors, BlockShape};
use crate::arena::monad::{read_level_m, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types::CheckError;
use crate::kernel::level;

/// con-leche: ConLeche/Kernel/Inductives/BlockRec.lean:50-84 blockLargeElimAllowed
/// Lean twin: `proof/ConRon/Arena/Inductives/BlockRec.lean:21-31 blockLargeElimAllowed` —
/// **when a large eliminator is allowed**: always when the block's sort is
/// never `0`; otherwise only for ONE member with no container occurrence and
/// at most one constructor, at the large shape.  The cited `||` short-circuits
/// after the sort's read, which is the only part that touches the store.
pub fn block_large_elim_allowed(
    pers: &PersTier,
    st: &mut AState,
    p: &BlockShape,
    nested: bool,
) -> Result<bool, CheckError> {
    match read_level_m(pers, st, &p.res_sort) {
        Err(e) => Err(e),
        Ok(l) => {
            if level::is_never_zero(&l) {
                Ok(true)
            } else {
                let n: u64 = shape_num_ctors(p);
                if nested {
                    Ok(false)
                } else {
                    Ok(p.large && shape_k(p) == 1 && (n == 0 || n == 1))
                }
            }
        }
    }
}
