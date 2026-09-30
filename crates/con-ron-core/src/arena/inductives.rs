//! `arena::inductives` — the inductive block's dispatch.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives.lean`: the `.indDecl` arm of
//! con-leche's `checkDecl` (`ConLeche/Kernel/Checker.lean:566-609`), from the
//! declared parameter count down to the two routes.  This is the single entry
//! point `arena::checker`'s declaration checker calls, and everything in
//! `arena::inductives::*` is what it calls.
//!
//! What is NOT here is the **pinned basis block** (`basisPinHit`): a stream's
//! `Nat` block arrives as an ordinary `indDecl` and is recognised before this,
//! in the declaration checker, because its install is `checkBasisDecl`'s and
//! not an inductive route's.  con-leche's `checkDecl` makes that test first and
//! only then reaches the two clauses below; the arena's does the same.
//!
//! | Rust | Lean twin |
//! |---|---|
//! | `struct_parts` | `Arena/Inductives/StructParts.lean` |
//! | `sum_parts` | `Arena/Inductives/SumParts.lean` |
//! | `struct_install` | `Arena/Inductives/StructInstall.lean` |
//! | `struct_install_f` | `Arena/Inductives/StructInstallF.lean` |
//! | `sum_install` | `Arena/Inductives/SumInstall.lean` |
//! | `sum_install_f` | `Arena/Inductives/SumInstallF.lean` |
//! | `native_parts` | `Arena/Inductives/NativeParts.lean` |
//!
//! The declaration checker's own helpers — `unwrapOr`, `checkConstantVal`,
//! `allLevelParamsDefined`, `constsResolveFFast`, `openPisAtFvarsF`,
//! `domsMatchAux`, the three list checks, `isEqHead`, `IFEnv.findCV?`,
//! `checkProjShape`, `checkProjRule`, `isRecInfo`, `recsFormSuffix`,
//! `indParamsOk` — are `arena::checker_base`'s, the whole-constant
//! comparisons `arena::canon`'s, the interning converters `arena::intern`'s
//! and the pinned `Eq` basis `arena::std_axioms`'s.  While the two halves of
//! P4d ran concurrently this module carried a borrowed copy of them
//! (`arena::inductives::ind_base`, as the Lean carried
//! `Arena/Inductives/Base.lean`); the merge deleted both.

pub mod native_parts;
pub mod block_parts;
pub mod block_tail;
pub mod struct_install;
pub mod struct_install_f;
pub mod struct_parts;
pub mod sum_install;
pub mod sum_install_f;
pub mod sum_parts;

