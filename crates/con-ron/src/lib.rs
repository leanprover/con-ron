//! con-ron's **frontend**: the lean4export NDJSON parser and the pure stream
//! transformations con-leche's `Main.lean` runs before it calls `checkDecls`.
//!
//! DESIGN.md §1 puts every one of them *outside* the main theorem — "the Rust
//! parser, the frontend rewrites (prelude, Nat-op reordering, projection
//! rewrite, the mutual/nested inductive modeller), the CLI, and the thread
//! pool are outside it, as they are in con-leche" — so this crate is
//! **unverified**: Charon never sees it, no refinement lemma mentions it, and
//! §3.4's Aeneas subset does not apply (it uses `for`, `while`, `?`,
//! `std::collections`, closures and `derive(Debug)` freely).  There is no
//! `unsafe`.
//!
//! What it *does* keep is §3.1's mirroring and §3.7's citations: one Rust
//! module per con-leche file, functions in the same order, every item carrying
//! its `/// con-leche:` line — because the provenance gate's `update` mode is
//! the only sync signal the frontend will ever have (§3.7: "for the
//! unverified frontend it is the only sync signal there is").
//!
//! | Rust | con-leche |
//! |---|---|
//! | `frontend::scan_types` | `ConLeche/Frontend/Scan/Types.lean` |
//! | `frontend::scan_fast` | `ConLeche/Frontend/Scan/Fast.lean` (spec: `Scan/Naive.lean`) |
//! | `frontend::export` | `ConLeche/Frontend/Export.lean` |
//! | `frontend::basis_raw` | `ConLeche/Kernel/Basis/*.lean` (the *raw* pins) |
//! | `frontend::proj_rec` | `ConLeche/Frontend/ProjRec.lean` |
//! | `frontend::nat_op_ground` | `ConLeche/Frontend/NatOpGround.lean` |
//! | `frontend::export_c` | `ConLeche/Frontend/ExportC.lean` |
//! | `frontend::prelude` | `ConLeche/Frontend/Prelude.lean` |
//! | `in_model` | `ConLeche/Frontend/InModel.lean` |
//! | `in_model::kit` | `ConLeche/Frontend/InModel/Kit.lean` |
//! | `in_model::mutual` | `ConLeche/Frontend/InModel/Mutual.lean` |
//! | `in_model::nested` | `ConLeche/Frontend/InModel/Nested.lean` |
//! | `driver` | `Main.lean` (the shared driver: the phases, the flags, the verdict) |
//! | `pool` | `Main.lean:213-328` (phase B on a pool of check workers) |
//! | `src/bin/con-ron.rs` | `Main.lean` (the raw-stream front door) |
//! | `src/bin/con-ron-check.rs` | `Main.lean` (the same driver on a `con-ron-decls/1` dump) |
//!
//! **Three things are deliberately not here**, and every one of them is a
//! `scripts/provenance-skip.txt` entry with its reason (§3.7 — the skip file
//! is the machine-readable index of these notes).  The fourth, `Main.lean`'s
//! **worker pool**, is here since task #48: `pool` is `checkOne`,
//! `checkWorker`, `mergeResults` and `checkPool`, and `--jobs=<n>` runs it.
//!
//! 1. **`ConLeche/Frontend/ExportWrite.lean`** (the checker's own *annotated*
//!    NDJSON writer) is not needed: it is an output path (`lake exe
//!    con-leche-annot` writes the `tests/annot` fixtures), not something the
//!    checker reads.  con-ron reads those fixtures like any other stream.
//! 2. **`ConLeche/Frontend/InModelDump.lean`**, the `CON_LECHE_INMODEL_DUMP`
//!    debug splice, which is built on that writer and is likewise not on the
//!    checking path (`in_model`'s module note).
//! 3. **`ConLeche/Frontend/Scan/Naive.lean` and `Scan/Equiv*.lean`** are the
//!    reference recogniser and the `@[csimp]` equivalence proof.  There is one
//!    Rust recogniser (`scan_fast`), and each of its items cites the `Naive`
//!    declaration that *specifies* it beside the `Fast` one it ports; what is
//!    skipped is the reference-only half — the `NRes` reader monad and the
//!    twenty-odd field tables `Fast.lean` inlines into its slot loops.

pub mod driver;
pub mod frontend;
pub mod in_model;
pub mod pool;
