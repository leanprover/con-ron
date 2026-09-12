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
//! | `expr` | `ConLeche/Kernel/Expr.lean` (everything but the `Level` part) |
//! | `core_types` | `ConLeche/Kernel/Core.lean:45-59` (`CheckError`, `CheckM`) |
//! | `env` | `ConLeche/Kernel/Env.lean` |
//! | `fenv` | `ConLeche/Kernel/FEnv.lean` |
//! | `state_c` | `ConLeche/Cached/StateC.lean` |
//! | `parsed_c` | `ConLeche/Cached/ParsedC.lean`, plus the two seam records of `Cached/Installed.lean` and `Kernel/CheckerSplit.lean` |

pub mod core_types;
pub mod env;
pub mod expr;
pub mod fenv;
pub mod hashmap;
pub mod level;
pub mod name;
pub mod nat;
pub mod parsed_c;
pub mod prop_when;
pub mod state_c;
