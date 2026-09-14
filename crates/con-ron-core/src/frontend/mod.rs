//! The export parser, inside the verified core (task #84).
//!
//! con-leche's main corollary is stated over the *file's byte chunks* since
//! its tasks #290/#294: `builtinPreludeE`, `parseChunks`, `preparePrelude`,
//! `checkDecls`, four pure steps in one `do` block
//! (`ConLeche/MainTheorem.lean`).  con-ron's capstones used to stop at the
//! fold and assume the parsed input well-formed (`hds`); this directory is
//! the parser crossing into the core so that a later task can discharge that
//! hypothesis from the parser's own refinement and state the port's own
//! chunk-level corollary.
//!
//! One Rust module per Lean file, as everywhere in the core:
//!
//! | Rust | Lean |
//! |---|---|
//! | `text` | none — the port's message rendering (`String` is `Vec<u32>`) |
//! | `nat_decimal` | none — `String.toNat?` on a `natVal` literal (`ron::nat` has no decimal codec) |
//! | `scan_types` | `ConLeche/Frontend/Scan/Types.lean` |
//! | `scan_fast` | `ConLeche/Frontend/Scan/Fast.lean` (the `@[csimp]` twin the compiler *runs*; `Scan/Naive.lean` is the specification and is not ported) |
//! | `export` | `ConLeche/Frontend/Export.lean` |
//! | `in_model_rec` | `ConLeche/Frontend/InModel/Mutual.lean`'s block records and `InModel.lean`'s `wants`, plus the `Modeller` seam |
//! | `proj_rec` | `ConLeche/Frontend/ProjRec.lean` |
//! | `export_c` | `ConLeche/Frontend/ExportC.lean` |
//! | `nat_op_ground` | `ConLeche/Frontend/NatOpGround.lean` |
//! | `prepare` | `ConLeche/Frontend/Prepare.lean` |
//! | `prelude_text` | `ConLeche/Frontend/Prelude.lean:57-62`'s `include_str` — **generated**, `scripts/gen-prelude.sh` |
//! | `prelude` | `ConLeche/Frontend/Prelude.lean` |
//!
//! **The modeller is NOT here.**  `InModel.generate` — the in-process
//! construction of a `_model` family for a mutual or nested block — stays in
//! the unverified crate, behind the one-method trait `in_model_rec::Modeller`
//! that `export_c::parse_chunks` takes as a type parameter.  A trait method on
//! a type parameter extracts as a typeclass field, i.e. an opaque function, so
//! the extracted parse is quantified over an arbitrary modeller and the
//! refinement will carry one hypothesis about its output rather than a port of
//! four thousand lines whose correctness decides coverage and not soundness
//! (`crates/con-ron/src/in_model/mod.rs`: "soundness needs nothing from this
//! module").
//!
//! **The loop relaxation** (DESIGN.md §3.4, dated 2026-09-14).  This directory
//! — and only this directory — may use `while`, `loop` and `for … in a..b`
//! where the cited Lean function is a per-byte or per-element tail recursion.
//! Lean compiles those tail calls to loops; Rust does not promise to, and a
//! per-byte recursion on a long export line is a stack overflow.  Extraction
//! runs with `-loops-to-rec`, so each loop becomes a `foo_loop` function that
//! mirrors the Lean recursion one for one, which is what the refinement will
//! be stated against.  Everything else in §3.4 stands.

pub mod export;
pub mod export_c;
pub mod in_model_rec;
pub mod nat_decimal;
pub mod nat_op_ground;
pub mod prelude_text;
pub mod prepare;
pub mod proj_rec;
pub mod scan_fast;
pub mod scan_types;
pub mod text;
