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
//! | `expr_ops_c` | `ConLeche/Cached/ExprOpsC.lean` (the executed, memoised twins of `expr_ops`), plus `Cached/ExprC.lean`'s `hasFvar` |
//! | `state_c` | `ConLeche/Cached/StateC.lean` |
//! | `parsed_c` | `ConLeche/Cached/ParsedC.lean` (`checkDeclC`, `checkDeclStepC`), plus the two seam records of `Cached/Installed.lean` and `Kernel/CheckerSplit.lean` |
//! | `core_k` | `ConLeche/Kernel/Core.lean` (its syntactic layer; `core` is a Rust prelude crate name) |
//! | `core_c` | `ConLeche/Cached/CoreC.lean` (the executed bodies **and** the six memoizing wrappers that tie them) |
//! | `type_checker` | `ConLeche/Kernel/TypeChecker.lean` (the knot's entry points, at `checkFuel`) |
//! | `basis_builder` | `ConLeche/Kernel/Basis/Builder.lean` (the raw-pin DSL) |
//! | `std_axioms` | `ConLeche/Kernel/StdAxioms.lean` |
//! | `trust_pins` | `ConLeche/Kernel/TrustPins.lean` |
//! | `trust_axioms` | `ConLeche/Kernel/TrustAxioms.lean` |
//! | `nat_op_pins` | `ConLeche/Kernel/NatOpPinSet.lean` + `Kernel/NatOpPins.lean` (the record only: `natOpPinSets` is runtime data, a parameter of `check_decls` — §3.6, task #31) |
//! | `basis_tables` | `ConLeche/Kernel/BasisA.lean`'s `BasisKind.declsA` — **generated** from con-leche's own value (task #22) |
//! | `basis_pins` | `ConLeche/Kernel/BasisA.lean`'s two exactly-compared pins (`eqA`, `natA`), read off `basis_tables` (task #27) |
//! | `checker_base` | `ConLeche/Kernel/CheckerBase.lean` |
//! | `checker` | `ConLeche/Kernel/Checker.lean` (`checkDecl`, `checkDeclsPure`) |
//! | `decl_check` | `ConLeche/Kernel/DeclCheck.lean` (the `F`-mirrors with no generic twin) |
//! | `checker_split` | `ConLeche/Kernel/CheckerSplit.lean` |
//! | `checker_c` | `ConLeche/Cached/CheckerC.lean` (`orElse`, the one error-recovery point) |
//! | `installed` | `ConLeche/Cached/Installed.lean` (**`check_decls`**, the install/check fold; its `Prop`-indexed driver evidence is not ported — the module note says which and why) |
//!
//! The one place the map is not one-to-one is the checker core: `CoreC.lean`
//! has its own twin of almost every `Kernel/Core.lean` body, and it is the
//! twins the knot executes, so the bodies live in `core_c` (with the
//! `Core.lean` citation beside the `CoreC.lean` one) and `core_k` keeps the
//! readers, pins and shape guards they call.  See both modules' notes and
//! DESIGN.md's task #23.
//! | `core_k` | `ConLeche/Kernel/Core.lean` (the bodies; `core` is a Rust prelude crate name) |
//! | `core_c` | `ConLeche/Cached/CoreC.lean` (the six memoizing wrappers that tie the knot) |
//! | `inductives` | `ConLeche/Kernel/Inductives/*` (the two install routes for an inductive block; its own `mod.rs` has the sub-map and the three directory-wide deviations) |

pub mod cached;
pub mod kernel;
pub mod ron;
