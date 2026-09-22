//! con-ron's **unverified crate**: the driver and CLI, the check phase's
//! worker pool, and the in-process modeller for mutual and nested inductive
//! blocks.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!         [--progress[=<stride>]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron --help
//! ```
//!
//! DESIGN.md §1 puts all three *outside* the main theorem — "the Rust parser,
//! the frontend rewrites (prelude, Nat-op reordering, projection rewrite, the
//! mutual/nested inductive modeller), the CLI, and the thread pool are outside
//! it, as they are in con-leche" — so this crate is **unverified**: Charon
//! never sees it, no refinement lemma mentions it, and §3.4's Aeneas subset
//! does not apply (it uses `for`, `while`, `?`, `std::collections`, closures
//! and `derive(Debug)` freely).  There is no `unsafe`.
//!
//! **Task #97-SWAP made this the arena's driver** (DESIGN.md §8.6).  The
//! crate that held it through the campaign was `con-ron-arena`, beside the
//! `Expr`-tree binary; the swap deleted the old `driver`/`pool`/`bin` and put
//! `con-ron-arena`'s in their place, under the old name and with the same
//! command line to the letter.  `crates/con-ron-arena` no longer exists, and
//! neither does the `Expr`-tree checker the old driver drove.
//!
//! **The parser left at task #84** (DESIGN.md §3.8, OVERVIEW §3.7).  con-leche
//! states its main corollary over the file's byte chunks now, so the whole
//! path from the bytes to `check_decls` had to be inside the extraction; the
//! modules that were `crate::frontend::*` are `con_ron_core::frontend::*`.
//! What of that path stays here is exactly what is not a function of the
//! input: the **reads** (`driver::read_up_to` and the handle/stream parse
//! loops, whose pure counterpart `parse_chunks` is the core's), and the
//! **modeller**, which the core calls through the one-method trait
//! `con_ron_core::frontend::types::Modeller` and this crate implements as
//! `in_model::InProcess`.
//!
//! What this crate *does* keep is §3.1's mirroring and §3.7's citations: one
//! Rust module per con-leche file, functions in the same order, every item
//! carrying its `/// con-leche:` line — because the provenance gate's `update`
//! mode is the only sync signal an unverified module will ever have (§3.7:
//! "for the unverified frontend it is the only sync signal there is").
//!
//! | Rust | con-leche | Lean twin |
//! |---|---|---|
//! | `driver` | `Main.lean` (the phases, the flags, the verdict, the reads) | `Arena/Main.lean` |
//! | `pool` | `Main.lean:193-316` (phase B on a pool of check workers) | `Arena/Main.lean` |
//! | `in_model` | `ConLeche/Frontend/InModel.lean`, plus the `Modeller` impl | `Arena/Frontend/InModel.lean` |
//! | `in_model::kit` | `ConLeche/Frontend/InModel/Kit.lean` | — |
//! | `in_model::mutual` | `ConLeche/Frontend/InModel/Mutual.lean` | — |
//! | `in_model::nested` | `ConLeche/Frontend/InModel/Nested.lean` | — |
//! | `keys` | none — `std::hash::Hash`/`Eq` wrappers for `Expr` and `Name` | — |
//! | `render` | none — `Name.toString`, which the core's skip list keeps out | — |
//! | `tree` | the six `Expr`-value helpers the modeller builds trees with (task #97-SWAP) | — |
//! | `src/bin/con-ron.rs` | `Main.lean` (the binary) | `Arena/Main.lean`'s `main` |
//!
//! **Two things are deliberately not ported at all**, and each is a
//! `scripts/provenance-skip.txt` entry with its reason (§3.7 — the skip file
//! is the machine-readable index of these notes):
//!
//! 1. **`ConLeche/Frontend/ExportWrite.lean`** (the checker's own *annotated*
//!    NDJSON writer) is not needed: it is an output path (`lake exe
//!    con-leche-annot` writes the `tests/annot` fixtures), not something the
//!    checker reads.  con-ron reads those fixtures like any other stream.
//! 2. **`ConLeche/Frontend/InModelDump.lean`**, the `CON_LECHE_INMODEL_DUMP`
//!    debug splice, which is built on that writer and is likewise not on the
//!    checking path (`in_model`'s module note).
//!
//! **The worker pool** (`pool`, task #48; task #97-P6-6b over the arena) is
//! DESIGN.md §8.3's "the persistent tier is immutable in phase B, each worker
//! owns a scratch tier — no atomics anywhere", with the tier frozen at the
//! phase boundary and shared by reference.  Threads live here and never in
//! `con-ron-core` (§8.5).

pub mod driver;
pub mod in_model;
pub mod keys;
pub mod pool;
pub mod render;
pub mod tree;
