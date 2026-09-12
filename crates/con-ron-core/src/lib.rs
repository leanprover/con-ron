//! The verified core of con-ron: a transliteration of con-leche's
//! `ConLeche/Kernel/*` and `ConLeche/Cached/*` (DESIGN.md §3.1), written in
//! the Aeneas-friendly subset of Rust (§3.4, `scripts/lint-rust-style.sh`).
//!
//! Module map (one Rust module per Lean file; the first two have no Lean
//! counterpart, they replace runtime primitives, §3.3):
//!
//! | Rust | Lean |
//! |---|---|
//! | `nat` | `Nat` (the runtime's GMP bignum) |
//! | `hashmap` | `Std.HashMap` |
//! | `name` | `ConLeche/Kernel/Name.lean` |
//! | `level` | `ConLeche/Kernel/Expr.lean` (Level part), `Kernel/Level.lean` |
//! | `prop_when` | `ConLeche/Kernel/PropWhen.lean` |
//! | `prop_read` | `ConLeche/Kernel/PropRead.lean` |
//! | `basis_names` | `ConLeche/Kernel/Basis/Names.lean` |
//! | `expr` | `ConLeche/Kernel/Expr.lean` (everything but the `Level` part) |
//! | `core_types` | `ConLeche/Kernel/Core.lean:45-59` (`CheckError`, `CheckM`) |
//! | `expr_ops` | `ConLeche/Kernel/ExprOps.lean` |
//! | `env` | `ConLeche/Kernel/Env.lean` |
//! | `fenv` | `ConLeche/Kernel/FEnv.lean` |
//! | `state_c` | `ConLeche/Cached/StateC.lean` |
//! | `parsed_c` | `ConLeche/Cached/ParsedC.lean`, plus the two seam records of `Cached/Installed.lean` and `Kernel/CheckerSplit.lean` |
//! | `core_k` | `ConLeche/Kernel/Core.lean` (its syntactic layer; `core` is a Rust prelude crate name) |
//! | `core_c` | `ConLeche/Cached/CoreC.lean` (the executed bodies **and** the six memoizing wrappers that tie them) |
//!
//! The one place the map is not one-to-one is the checker core: `CoreC.lean`
//! has its own twin of almost every `Kernel/Core.lean` body, and it is the
//! twins the knot executes, so the bodies live in `core_c` (with the
//! `Core.lean` citation beside the `CoreC.lean` one) and `core_k` keeps the
//! readers, pins and shape guards they call.  See both modules' notes and
//! DESIGN.md's task #23.

pub mod cached;
pub mod kernel;
pub mod ron;
