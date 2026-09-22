//! The verified core of con-ron: a transliteration of con-leche's
//! `ConLeche/Kernel/*`, `ConLeche/Cached/*` and `ConLeche/Frontend/*`
//! (DESIGN.md §3.1), written in the Aeneas-friendly subset of Rust (§3.4,
//! `scripts/lint-rust-style.sh`).
//!
//! **The checker is the arena's** (DESIGN.md §8, task #97).  Task #97-SWAP
//! retired the `Expr`-tree checker that occupied `kernel/` and `cached/` and
//! put the arena rewrite — `arena/` and the store-native parser in
//! `frontend/` — in its place, in ONE crate, which is what closes the
//! ~213-hole crate boundary `arena-core` carried (DESIGN.md's task #97-P4a).
//! `arena-core` no longer exists; `crates/con-ron` is the driver.
//!
//! # Module map
//!
//! Four directories, in dependency order:
//!
//! | directory | what it is |
//! |---|---|
//! | `ron` | replacements for Lean runtime primitives (DESIGN.md §3.3): no Lean source to cite |
//! | `kernel` | the representation-free types and the PINNED DATA the checker compares against, as `Expr`-valued con-leche constants |
//! | `arena` | the checker itself, over the four interned stores — the Rust twin of `proof/ConRon/Arena/*` |
//! | `frontend` | the export parser, straight into the store |
//!
//! ## `ron`
//!
//! | Rust | Lean |
//! |---|---|
//! | `nat` | `Nat` (the runtime's GMP bignum) |
//! | `hashmap` | `Std.HashMap` |
//! | `hashmap2` | `Std.HashMap`, the open-addressed second map (task #97-P6-4b) |
//! | `ptr` | none — the shared-pointer type of DESIGN.md §3.2 |
//! | `tagged`, `node` | none — the tagged counted handle `Expr` is built from (task #94) |
//!
//! ## `kernel` — the types and the pinned data
//!
//! | Rust | Lean |
//! |---|---|
//! | `name` | `ConLeche/Kernel/Name.lean` |
//! | `level` | `ConLeche/Kernel/Expr.lean` (Level part), `Kernel/Level.lean` |
//! | `prop_when` | `ConLeche/Kernel/PropWhen.lean` |
//! | `prop_read` | `ConLeche/Kernel/PropRead.lean` |
//! | `expr` | `ConLeche/Kernel/Expr.lean` (everything but the `Level` part) — the VALUE representation the pinned data is written in |
//! | `expr_ops` | `ConLeche/Kernel/ExprOps.lean` (what the pinned data and `level` still need of it) |
//! | `core_types` | `ConLeche/Kernel/Core.lean:45-59` (`CheckError`, `CheckM`) |
//! | `core_k` | `ConLeche/Kernel/Core.lean` (the pinned `Nat`/`Bool` operator names and the decimal renderer) |
//! | `env` | `ConLeche/Kernel/Env.lean` (the `ConstantInfo`/`Declaration` the pinned data is expressed in, and the `CheckMode` gates) |
//! | `fenv` | `ConLeche/Kernel/FEnv.lean` (what the pin comparisons need) |
//! | `canon` | `ConLeche/Kernel/Canon.lean` (the raw-pin canonicaliser) |
//! | `basis_names` | `ConLeche/Kernel/Basis/Names.lean` |
//! | `basis_builder` | `ConLeche/Kernel/Basis/Builder.lean` (the raw-pin DSL) |
//! | `basis_raw` | `ConLeche/Kernel/Basis.lean`'s `BasisKind.decls` |
//! | `basis_tables` | `ConLeche/Kernel/BasisA.lean`'s `BasisKind.declsA` — **generated** from con-leche's own value (task #22) |
//! | `basis_pins` | `ConLeche/Kernel/BasisA.lean`'s two exactly-compared pins (`eqA`, `natA`), read off `basis_tables` (task #27) |
//! | `std_axioms` | `ConLeche/Kernel/StdAxioms.lean` |
//! | `trust_pins` | `ConLeche/Kernel/TrustPins.lean` |
//! | `trust_axioms` | `ConLeche/Kernel/TrustAxioms.lean` |
//! | `nat_op_pins` | `ConLeche/Kernel/NatOpPinSet.lean` + `Kernel/NatOpPins.lean` (the record only: `natOpPinSets` is data, the last argument of `checkDecls` on both sides — §3.6, tasks #31/#43/#74) |
//! | `pins_text`, `pins_decode` | the embedded `con-ron-pins/1` dump and its reader (§3.6, task #43) |
//!
//! **Why `Expr` survives the arena rewrite.**  Three families of con-leche
//! declaration are pure `Expr` / `ConstantInfo` *values* written out by hand or
//! spliced by an elaborator: the basis blocks (`BasisKind.decls` / `declsA`),
//! the standard- and compiler-trust axiom pins, and the `Nat`-operation pin
//! variants.  DESIGN.md §8.7's ruling is that the port IMPORTS con-leche's
//! representation-free data rather than copying it, and the Rust's import of
//! it is these modules; `arena::intern` walks each value once at startup and
//! puts it in the persistent tier, which is why no `Expr` is ever built while
//! a declaration is checked.  Retiring `Expr` therefore means re-expressing
//! this data handle-natively, which is its own task (§8.6's follow-up, and
//! the task #97-SWAP section's finding).
//!
//! ## `arena` and `frontend`
//!
//! See `arena/mod.rs` and `frontend/mod.rs`: one Rust module per file of
//! `proof/ConRon/Arena/*`, with both citations on every item — con-leche's,
//! as the whole port has (DESIGN.md §3.7), and the Lean twin's line.

pub mod arena;
pub mod frontend;
pub mod kernel;
pub mod ron;
