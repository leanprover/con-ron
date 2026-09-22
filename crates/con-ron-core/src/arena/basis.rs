//! `arena::basis` — the pinned basis blocks, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/Basis.lean`, which is con-leche's
//! `Kernel/Basis.lean` and `Kernel/BasisA.lean`: the constants of the six
//! pinned blocks (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, `Quot`) and the two
//! tests that recognise a stream record as one of them.
//!
//! **The blocks are values, interned** (`arena::intern`'s module note).  The
//! Lean twin interns con-leche's `BasisKind.decls` / `declsA`; the Rust interns
//! `con_ron_core::kernel::basis_raw::basis_kind_decls` and
//! `kernel::basis_tables::basis_decls_a`, which are the same two blocks —
//! con-ron-core's raw pins are hand-ported from the same builder and its
//! annotated tables are *generated from con-leche's own `declsA`* (task #22).
//! What IS a twin here is the two recognisers, which read the environment and
//! compare with `arena::canon`'s lockstep comparisons.
//!
//! **`decls` versus `declsA`.**  `BasisKind.decls` is the RAW block and
//! `declsA` the ANNOTATED one the install stores; `basis_pin_hit` compares
//! against the raw block and `check_basis_decl` installs the annotated one, so
//! the arena keeps the two apart exactly as con-leche does.

use crate::arena::env::{i_constant_info_name, i_constant_info_to_constant_val, IConstantInfo, IConstantVal};
use crate::arena::handle::NIdx;
use crate::arena::intern::intern_ci_list;
use crate::arena::monad::AState;
use crate::kernel::basis_raw;
use crate::kernel::basis_tables;
use crate::kernel::core_types::CheckError;
use crate::kernel::env as cenv;
use crate::kernel::env::{BasisKind, QuotKind};
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/Basis.lean:40-47 BasisKind.decls
/// Lean twin: `proof/ConRon/Arena/Basis.lean:34-37 BasisKind.decls` — the RAW
/// constants of one basis block, in dependency order, interned.
pub fn basis_kind_decls(
    pers: &PersTier,
    st: &mut AState,
    k: &BasisKind,
) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &basis_raw::basis_kind_decls(k))
}

/// con-leche: ConLeche/Kernel/BasisA.lean:50-57 BasisKind.declsA
/// Lean twin: `proof/ConRon/Arena/Basis.lean:39-43 BasisKind.declsA` — the
/// ANNOTATED constants of one basis block, in dependency order, interned.
/// This is what `check_basis_decl` installs.
pub fn basis_kind_decls_a(
    pers: &PersTier,
    st: &mut AState,
    k: &BasisKind,
) -> Result<Vec<IConstantInfo>, CheckError> {
    intern_ci_list(pers, st, &basis_tables::basis_decls_a(k))
}

/// con-leche: ConLeche/Kernel/Basis.lean:60-71 basisPinHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:45-49 blockNames` — the names of
/// a block's members, for `basis_pin_hit`'s name pre-filter.
/// `i_constant_info_name` is pure (task #97e), so this is a plain map, spelled
/// as a cursor (§3.4 forbids the closure `List.map` takes).
pub fn block_names(block: &Vec<IConstantInfo>, i: usize, out: Vec<NIdx>) -> Vec<NIdx> {
    if i >= block.len() {
        out
    } else {
        let mut out2 = out;
        out2.push(i_constant_info_name(&block[i]));
        block_names(block, i + 1, out2)
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:60-71 basisPinHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:51-67 basisPinHitGo` — the five
/// kinds tried in con-leche's order, with con-leche's task-#215 NAME
/// pre-filter in front: `canon` renames only level parameters, so a block can
/// match a pin only when its members' names are the pin's, member for member,
/// and that test is a handful of handle comparisons.
///
/// `find?` stops at the FIRST kind whose names match and then `filter`s by the
/// canonical comparison — i.e. a name match that fails the comparison is
/// `none`, not "try the next kind", which is what the `then` branch spells.
pub fn basis_pin_hit_go(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
    ks: &Vec<BasisKind>,
    i: usize,
) -> Result<Option<BasisKind>, CheckError> {
    if i >= ks.len() {
        Ok(None)
    } else {
        match basis_kind_decls(pers, st, &ks[i]) {
            Err(e) => Err(e),
            Ok(pinned) => {
                if !crate::arena::canon::nidx_vec_beq(
                    &block_names(&pinned, 0, Vec::new()),
                    &block_names(block, 0, Vec::new()),
                    0,
                ) {
                    basis_pin_hit_go(pers, st, block, ks, i + 1)
                } else {
                    match crate::arena::canon::canon_eq_list(pers, st, block, &pinned, 0) {
                        Err(e) => Err(e),
                        Ok(r) => {
                            if r {
                                Ok(Some(cenv::basis_kind_dup(&ks[i])))
                            } else {
                                Ok(None)
                            }
                        }
                    }
                }
            }
        }
    }
}

/// con-leche: ConLeche/Kernel/Basis.lean:60-71 basisPinHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:69-77 basisPinHit` — the five
/// pinned blocks, in con-leche's order.  `.quotK` is deliberately not among
/// them (a quotient block arrives as four `quotDecl` records, which
/// `quot_pin_hit` decides); the list is
/// `con_ron_core::kernel::basis_raw::block_pin_kinds`, the same literal.
pub fn basis_pin_hit(
    pers: &PersTier,
    st: &mut AState,
    block: &Vec<IConstantInfo>,
) -> Result<Option<BasisKind>, CheckError> {
    let ks: Vec<BasisKind> = basis_raw::block_pin_kinds();
    basis_pin_hit_go(pers, st, block, &ks, 0)
}

/// con-leche: ConLeche/Kernel/Basis.lean:73-78 quotPinHit
/// Lean twin: `proof/ConRon/Arena/Basis.lean:79-88 quotPinHit` — **the
/// quotient-pin match**: the record is the pinned package's constant at the
/// slot it declares itself at, compared at `toConstantVal`.  The twin's
/// `blk[k.slot]?` is the bound test here; `quot_basis` has exactly the five
/// members `quot_kind_slot` indexes, so the `none` arm is unreachable and is
/// `false`, as the twin's is.
pub fn quot_pin_hit(
    pers: &PersTier,
    st: &mut AState,
    k: &QuotKind,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    match basis_kind_decls(pers, st, &BasisKind::QuotK) {
        Err(e) => Err(e),
        Ok(blk) => {
            let slot: u64 = cenv::quot_kind_slot(k);
            if slot >= blk.len() as u64 {
                Ok(false)
            } else {
                match i_constant_info_to_constant_val(pers, &mut st.store, &blk[slot as usize]) {
                    Err(e) => Err(e),
                    Ok(pcv) => crate::arena::canon::i_constant_val_canon_eq(pers, st, cv, &pcv),
                }
            }
        }
    }
}
