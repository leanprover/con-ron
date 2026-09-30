//! WIP stub (task #105): replaced by the port of `Inductives/BlockTail.lean`.
use super::block_parts::BlockParts;
use crate::arena::env::{IConstantInfo, IFEnv};
use crate::arena::monad::AState;
use crate::arena::store::PersTier;
use crate::kernel::core_types::CheckError;
use crate::kernel::env::CheckMode;

/// con-leche: none — WIP stub
pub fn check_block(
    _pers: &PersTier,
    _st: &mut AState,
    _mode: &CheckMode,
    fe: IFEnv,
    _block: &Vec<IConstantInfo>,
    _p: &BlockParts,
) -> Result<IFEnv, CheckError> {
    Ok(fe)
}
