//! `tree` — the `Expr`-VALUE helpers the in-process modeller still needs
//! (task #97-SWAP).
//!
//! `in_model` generates `_model` families as `Expr` trees and hands them to
//! `in_model::InProcess`, which interns them into the store (`in_model`'s
//! module note has the picture).  Until the swap, the six modules below lived
//! in `crates/con-ron-core` and were shared with the `Expr`-tree checker; the
//! swap deleted that checker, and the modeller is the only caller left.  So
//! they moved here, into the UNVERIFIED crate, rather than staying in the
//! verified one where Charon would model a thousand lines nothing checks.
//!
//! Nothing about them changed but their module path and one call (see
//! `proj_rec`'s note on `instantiate1_lift`).  They keep their con-leche
//! citations, which is what `scripts/provenance.py` reads.
//!
//! | Rust | con-leche |
//! |---|---|
//! | `export` | `ConLeche/Frontend/Export.lean` (what the modeller uses of it: `names_beq`) |
//! | `in_model_rec` | `ConLeche/Frontend/InModel/Mutual.lean`'s block records |
//! | `proj_rec` | `ConLeche/Frontend/ProjRec.lean` |
//! | `native_parts` | `ConLeche/Kernel/Inductives/NativeParts.lean` |
//! | `struct_parts` | `ConLeche/Kernel/Inductives/StructParts.lean` |
//! | `sum_parts` | `ConLeche/Kernel/Inductives/SumParts.lean` |
//!
//! The verified crate has the same six files' *handle* twins, under
//! `con_ron_core::{frontend::proj_rec, arena::inductives::*}`: those are what
//! the checker runs, these are what the modeller builds trees with.

pub mod export;
pub mod in_model_rec;
pub mod native_parts;
pub mod proj_rec;
pub mod struct_parts;
pub mod sum_parts;
