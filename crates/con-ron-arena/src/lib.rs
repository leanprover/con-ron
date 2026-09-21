//! `con-ron-arena` — the **arena checker's driver and CLI** (DESIGN.md §8.6,
//! task #97 phase P4f): the binary half of (C), beside `crates/arena-core`'s
//! checker half, and the Rust twin of `proof/ConRon/Arena/Main.lean`'s
//! `con-ron-lean`.
//!
//! ```text
//! con-ron-arena [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!               [--progress[=<stride>]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron-arena --help
//! ```
//!
//! It is the same program as `con-ron` over a different representation, and
//! the same command line to the letter — which is the point: DESIGN.md §8.6's
//! gate is `scripts/diff-e2e.sh --bin=target/release/con-ron-arena` over the
//! same 348 fixtures and the same expectations, and a binary that speaks
//! con-leche's command line can be put under that sweep from the first day.
//!
//! **UNVERIFIED, like `crates/con-ron`** (DESIGN.md §1: "the CLI and the
//! thread pool are outside the theorem, as they are in con-leche").  Charon
//! never sees this crate, no refinement lemma mentions it, and §3.4's Aeneas
//! subset does not apply — it uses `for`, `while`, `?`, `std::collections`,
//! closures and `derive` freely.  There is no `unsafe`.  It is outside
//! `scripts/lint-rust-style.sh` and outside `scripts/extract-arena.sh` for
//! that reason, exactly as `crates/con-ron` is outside the lint and
//! `scripts/extract.sh`.
//!
//! | Rust | con-leche | Lean twin |
//! |---|---|---|
//! | `driver` | `Main.lean` (the phases, the heartbeat, the verdicts, the reads) | `Arena/Main.lean` |
//! | `in_model` | `Frontend/InModel.lean` (the seam, instantiated) | `Arena/Frontend/InModel.lean` |
//! | `src/bin/con-ron-arena.rs` | `Main.lean` (the binary) | `Arena/Main.lean`'s `main` |
//!
//! **The modeller is `crates/con-ron`'s, and that is a property of the
//! differential test** ([`in_model`]): the mutual/nested `_model` generator
//! both binaries run is one copy of one unverified port, called here through a
//! readback and an intern.  So a fixture whose block is modelled is modelled
//! the same way by `con-ron` and by `con-ron-arena`, and a difference the
//! sweep reports is the CHECKER's.  The Lean twin does the same thing with
//! con-leche's own generator, for the same reason.
//!
//! **The worker pool is `pool`** (task #97-P6-6b), `con_ron::pool` over the
//! arena: DESIGN.md §8.3's "the persistent tier is immutable in phase B,
//! each worker owns a scratch tier — no atomics anywhere", with the tier
//! frozen at the phase boundary and shared by reference.  Threads live here
//! and never in `arena-core` (§8.5).

pub mod driver;
pub mod in_model;
pub mod pool;
