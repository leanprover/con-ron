//! `arena::inductives` — the inductive block's dispatch.
//!
//! The uniform inductive route of con-leche 445b9cf4 (task #105): every
//! inductive block — structure, sum, mutual, nested, indexed — is installed by
//! one installer, `block_tail::check_block`, which `arena::check_decl`'s
//! `.indDecl` arm (`check_ind_decl`, con-leche `Kernel/CheckDecl.lean`) reaches
//! after the basis-pin test, the parameter count and `block_parts`' recogniser.
//! One Rust module per con-leche file under `ConLeche/Kernel/Inductives/`:
//!
//! | Rust | con-leche |
//! |---|---|
//! | `field_tele` | `Inductives/FieldTele.lean` |
//! | `positivity` | `Inductives/Positivity.lean` |
//! | `block_rec` | `Inductives/BlockRec.lean` |
//! | `rec_check` | `Inductives/RecCheck.lean` |
//! | `class_read` | `Inductives/ClassRead.lean` |
//! | `gen_rec` | `Inductives/GenRec.lean` |
//! | `block_install` | `Inductives/BlockInstall.lean`, `BlockInstallF.lean` |
//! | `block_parts` | `Inductives/BlockParts.lean` |
//! | `block_tail` | `Inductives/BlockTail.lean` |
//! | `struct_parts` | `Inductives/StructParts.lean` |
//! | `struct_install` | `Inductives/StructInstall.lean`, `StructInstallF.lean` |
//! | `sum_install` | `Inductives/SumInstall.lean`, `SumInstallF.lean` |
//!
//! **`StructInstallF.lean`/`SumInstallF.lean`'s `F`-suffixed names had no
//! caller** (task #105 sweep): the arena has ONE environment type (task
//! #97c's deviation 1), so their bodies were already `struct_install`'s/
//! `sum_install`'s — the one-line delegation modules `struct_install_f.rs`/
//! `sum_install_f.rs` carried nothing else, and were deleted along with their
//! `mod` lines.  Their con-leche citations survive as the SECOND `/// con-
//! leche:` line already on the corresponding `struct_install`/`sum_install`
//! function (e.g. `checkStructDomsAtF` on `check_struct_doms_at`), so
//! `scripts/provenance.py coverage` needed no new skip-list entry.
//!
//! What is NOT here is the **pinned basis block** (`basisPinHit`): a stream's
//! `Nat` block arrives as an ordinary `indDecl` and is recognised first, in
//! `check_ind_decl`, because its install is `checkBasisDecl`'s.  The modelled
//! route (`native_parts`, `native_install`, `modeled`, the `_model` families)
//! and the gated tiers are gone with upstream's.

pub mod field_tele;
pub mod positivity;
pub mod block_rec;
pub mod rec_check;
pub mod class_read;
pub mod gen_rec;
pub mod block_install;
pub mod block_parts;
pub mod block_tail;
pub mod struct_install;
pub mod struct_parts;
pub mod sum_install;

