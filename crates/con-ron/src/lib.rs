//! con-ron's **unverified crate**: the driver and CLI, and the check phase's
//! worker pool.
//!
//! ```text
//! con-ron [--verified|--trusted] [--jobs=<n>] [--no-mark-persistent]
//!         [--progress[=<stride>]] [--pins FILE|--no-pins] FILE.ndjson
//! con-ron --help
//! ```
//!
//! DESIGN.md §1 puts all of this *outside* the main theorem — "the Rust
//! parser, the frontend rewrites (prelude, Nat-op reordering), the CLI, and
//! the thread pool are outside it, as they are in con-leche" — so this crate
//! is **unverified**: Charon never sees it, no refinement lemma mentions it,
//! and §3.4's Aeneas subset does not apply (it uses `for`, `while`, `?`,
//! `std::collections`, closures and `derive(Debug)` freely).  There is no
//! `unsafe`.
//!
//! **Task #97-SWAP made this the arena's driver** (DESIGN.md §8.6).  The
//! crate that held it through the campaign was `con-ron-arena`, beside the
//! `Expr`-tree binary; the swap deleted the old `driver`/`pool`/`bin` and put
//! `con-ron-arena`'s in their place, under the old name and with the same
//! command line to the letter.  `crates/con-ron-arena` no longer exists, and
//! neither does the `Expr`-tree checker the old driver drove.
//!
//! **Neither the projection-function rewrite nor the in-process modeller
//! exist any more** (task #105, con-leche's `uniform-inds` merge): every
//! mutual and nested inductive block installs through the kernel's uniform
//! installer now, so `crate::in_model` (the modeller's implementation of
//! `con_ron_core::frontend::types::Modeller`) and `crate::tree` (the `Expr`
//! -value helpers it built trees with) are gone, and so is the
//! `CON_LECHE_INMODEL*` family of debug flags — the driver reads no
//! environment variable at all.
//!
//! **The parser left at task #84** (DESIGN.md §3.8, OVERVIEW §6.2).  con-leche
//! states its main corollary over the file's byte chunks now, so the whole
//! path from the bytes to `check_decls` had to be inside the extraction; the
//! modules that were `crate::frontend::*` are `con_ron_core::frontend::*`.
//! What of that path stays here is exactly what is not a function of the
//! input: the **reads** (`driver::read_up_to` and `driver::HandleSource`, the
//! file handle as the core's `export_c::ChunkSource`, whose loop
//! `export_c::parse_source` is the core's since task #97-P5-Driver).
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
//! | `keys` | none — `std::hash::Hash`/`Eq` wrappers for `Expr` and `Name` | — |
//! | `render` | none — `Name.toString`, which the core's skip list keeps out | — |
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
//!    debug splice, is gone upstream along with the modeller it served
//!    (task #105); it was never on the checking path either.
//!
//! **The worker pool** (`pool`, task #48; task #97-P6-6b over the arena) is
//! DESIGN.md §8.3's "the persistent tier is immutable in phase B, each worker
//! owns a scratch tier — no atomics anywhere", with the tier frozen at the
//! phase boundary and shared by reference.  Threads live here and never in
//! `con-ron-core` (§8.5).

pub mod driver;
pub mod keys;
pub mod pool;
pub mod render;
