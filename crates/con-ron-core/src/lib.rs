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
//! | `core_k` | `ConLeche/Kernel/Core.lean` (the bodies; `core` is a Rust prelude crate name) |
//! | `core_c` | `ConLeche/Cached/CoreC.lean` (the six memoizing wrappers that tie the knot) |
//! | `type_checker` | `ConLeche/Kernel/TypeChecker.lean` (the knot's entry points, at `checkFuel`) |
//! | `basis_builder` | `ConLeche/Kernel/Basis/Builder.lean` (the raw-pin DSL) |
//! | `std_axioms` | `ConLeche/Kernel/StdAxioms.lean` |
//! | `trust_pins` | `ConLeche/Kernel/TrustPins.lean` |
//! | `trust_axioms` | `ConLeche/Kernel/TrustAxioms.lean` |
//! | `nat_op_pins` | `ConLeche/Kernel/NatOpPinSet.lean` + `Kernel/NatOpPins.lean` (`natOpPinSets` is task #22's table; stubbed empty) |
//! | `basis_pins` | `ConLeche/Kernel/BasisA.lean` — **a stub**; task #22's `basis_tables` replaces it |
//! | `checker_base` | `ConLeche/Kernel/CheckerBase.lean` |
//! | `checker` | `ConLeche/Kernel/Checker.lean` (`checkDecl`, `checkDeclsPure`) |
//! | `decl_check` | `ConLeche/Kernel/DeclCheck.lean` (the `F`-mirrors with no generic twin) |
//! | `checker_split` | `ConLeche/Kernel/CheckerSplit.lean` |
//! | `checker_c` | `ConLeche/Cached/CheckerC.lean` (`orElse`, the one error-recovery point) |

pub mod cached;
pub mod kernel;
pub mod ron;
