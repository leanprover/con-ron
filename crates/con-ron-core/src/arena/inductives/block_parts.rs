//! WIP stub (task #105): replaced by the port of `Inductives/BlockParts.lean`.
use crate::arena::env::IConstantInfo;
use crate::arena::monad::AState;
use crate::arena::store::PersTier;
use crate::kernel::core_types::CheckError;

/// con-leche: none — WIP stub
pub struct BlockParts {}

/// con-leche: none — WIP stub
pub fn block_parts(
    _pers: &PersTier,
    _st: &mut AState,
    _n_p: u64,
    _block: &Vec<IConstantInfo>,
) -> Result<Option<BlockParts>, CheckError> {
    Ok(None)
}
