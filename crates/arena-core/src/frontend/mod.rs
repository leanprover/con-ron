//! The export parser **into the store** (DESIGN.md §8.3 "Parsing", task #97
//! P4e part 1): the Rust side of `proof/ConRon/Arena/Frontend/*`, in lockstep
//! with the Lean twin.
//!
//! | Rust | Lean twin | con-leche |
//! |---|---|---|
//! | `types` | `Arena/Frontend/Types.lean` | `Frontend/Export.lean`'s verdicts, `Frontend/ProjRec.lean`'s owner, `Frontend/InModel/Mutual.lean`'s block records, `InModel.lean`'s `wants` and the `Modeller` seam |
//! | `export_c` | `Arena/Frontend/ExportC.lean` | `Frontend/ExportC.lean` |
//! | `prepare` | `Arena/Frontend/Prepare.lean` | `Frontend/Prepare.lean` |
//! | `prelude` | `Arena/Frontend/Prelude.lean` | `Frontend/Prelude.lean` |
//!
//! ## What is reused across the crate boundary, and why that is the twin
//!
//! **The byte recogniser is not twinned.**  `ConLeche/Frontend/Scan/{Types,
//! Fast}.lean` is term-free — `Scan/Types.lean` imports `Std.Data.HashMap` and
//! nothing else, and its records carry stream indices, strings and booleans
//! with no checker type in them — so the Lean twin *imports* it rather than
//! copying it (`Arena/Frontend/ExportC.lean`'s note has the check).  The Rust
//! does exactly the same across the crate line: `con_ron_core::frontend::
//! {scan_types, scan_fast}` is the recogniser, `scan_types::IdTable<NIdx>` /
//! `<LIdx>` / `<EIdx>` are the parse tables (DESIGN.md §8.3's "an `Array EIdx`
//! from export index to handle", with the sparse overflow con-leche keeps for
//! the hand-written fixtures whose indices have gaps), and
//! `con_ron_core::frontend::{text, nat_decimal}` render the messages and
//! decode a `natVal`'s digits.  A twin of a byte recogniser that produces
//! representation-free records would be a copy, not a port.
//!
//! `con_ron_core::frontend::prelude_text::prelude_text()` is reused for the
//! same reason and one more: the 67 byte-array chunks it is split into are a
//! *generated* constant with `scripts/gen-prelude.sh --check` behind them, and
//! the Lean twin's own `builtinPreludeText` is an `include_str` through the
//! lake package directory that its task section already files as a follow-up.
//! Copying 1 500 generated lines into this crate to un-hole the model would
//! fork the gate; DESIGN.md §8.6's swap retires the boundary instead.
//!
//! ## The one change from `con-ron-core`'s parser: no `Expr` is ever built
//!
//! Where `con_ron_core::frontend::export_c` keeps an `IdTable<Expr>` of
//! *values* and a table hit is a shared node by `ron::ptr` bump, this keeps an
//! `IdTable<EIdx>` of **handles** into the persistent tier of the `EStore`,
//! and a table hit is the same shared node named by its handle.  The export's
//! own sharing is preserved exactly (con-leche's lesson 25), and the packed
//! derived word con-leche's smart constructors computed is `EStore::intern`'s
//! (task #97a's `der_of_view`, `Expr.data`'s formula verbatim).
//!
//! **No smart constructor is missing.**  con-leche's `Expr.mkApp`/`mkSort`/…
//! are `@[inline]` identity wrappers since its task #172 B3a made the derived
//! fields `@[computed_field]`s, so they reject nothing and validate nothing;
//! the only work they ever did is the derived word.  The checks the parse
//! *does* make are its own and are all here: the rebinding test,
//! `validate_ind_d`'s eleven block-consistency verdicts, the safety and
//! quotient-kind recognisers and the size guard.
//!
//! ## `AM` is `&mut EStore` plus `Result<_, CheckError>`
//!
//! The Lean twin's monad is `StateT AState (Except CheckError)`; `AState` is
//! the store and the `ExprOps` memo tables, and the frontend touches no memo.
//! So every function that reads the store takes `ar: &EStore` and every
//! function that interns takes `ar: &mut EStore`, beside the `st: &mut StateD`
//! that `con-ron-core`'s parser already threads.  `arena/monad.rs` (task #97
//! P4b) makes the first of those two a field of `AState`, and no body here
//! changes when it does.  The four `Monad.lean` primitives the parse needs —
//! `view`, `viewN`, `readName`, `readLevel` — sit at the bottom of
//! `arena/env.rs` until then, for the same reason.
//!
//! ## The loop relaxation (DESIGN.md §3.4, dated 2026-09-14)
//!
//! This directory — like `con-ron-core`'s `frontend/`, and only these two —
//! may use `while`, `loop` and `for … in a..b` where the cited Lean function
//! is a per-byte or per-element tail recursion.  Lean compiles those tail
//! calls to loops; Rust does not promise to, and a per-byte recursion on a
//! long export line is a stack overflow.  Extraction runs with
//! `-loops-to-rec`, so each loop becomes a `foo_loop` function that mirrors
//! the Lean recursion one for one.  `scripts/lint-rust-style.sh` knows the
//! exemption by path.  Everything else in §3.4 stands.

pub mod export_c;
pub mod nat_op_ground;
pub mod prelude;
pub mod prepare;
pub mod types;
