//! The export parser, inside the verified core (task #84; rewritten **into the
//! store** by task #97's arena campaign, DESIGN.md §8.3 "Parsing", P4e).
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
//! One Rust module per Lean file, as everywhere in the core.  The first five
//! rows are the byte recogniser and the rendering helpers, which are
//! representation-free and were not rewritten by the arena campaign; the last
//! six are the parse proper, whose Lean twin is `proof/ConRon/Arena/Frontend/*`
//! (task #97-SWAP moved them here from `arena-core`):
//!
//! | Rust | Lean twin | con-leche |
//! |---|---|---|
//! | `text` | none | none — the port's message rendering (`String` is `Vec<u32>`) |
//! | `nat_decimal` | none | none — `String.toNat?` on a `natVal` literal (`ron::nat` has no decimal codec) |
//! | `scan_types` | imported, not twinned | `ConLeche/Frontend/Scan/Types.lean` |
//! | `scan_fast` | imported, not twinned | `ConLeche/Frontend/Scan/Fast.lean` (the `@[csimp]` twin the compiler *runs*; `Scan/Naive.lean` is the specification and is not ported) |
//! | `prelude_text` | `include_str` | `ConLeche/Frontend/Prelude.lean:57-62`'s `include_str` — **generated**, `scripts/gen-prelude.sh` |
//! | `types` | `Arena/Frontend/Types.lean` | `Frontend/Export.lean`'s verdicts, `Frontend/ProjRec.lean`'s owner, `Frontend/InModel/Mutual.lean`'s block records, `InModel.lean`'s `wants` and the `Modeller` seam |
//! | `export_c` | `Arena/Frontend/ExportC.lean` | `Frontend/ExportC.lean` |
//! | `proj_rec` | `Arena/Frontend/ProjRec.lean` | `Frontend/ProjRec.lean` |
//! | `nat_op_ground` | `Arena/Frontend/NatOpGround.lean` | `Frontend/NatOpGround.lean` |
//! | `prepare` | `Arena/Frontend/Prepare.lean` | `Frontend/Prepare.lean` |
//! | `prelude` | `Arena/Frontend/Prelude.lean` | `Frontend/Prelude.lean` |
//!
//! ## The byte recogniser is not twinned, and that is deliberate
//!
//! `ConLeche/Frontend/Scan/{Types,Fast}.lean` is term-free — `Scan/Types.lean`
//! imports `Std.Data.HashMap` and nothing else, and its records carry stream
//! indices, strings and booleans with no checker type in them — so the Lean
//! twin *imports* it rather than copying it (`Arena/Frontend/ExportC.lean`'s
//! note has the check).  `scan_types::IdTable<NIdx>` / `<LIdx>` / `<EIdx>` are
//! the parse tables (DESIGN.md §8.3's "an `Array EIdx` from export index to
//! handle", with the sparse overflow con-leche keeps for the hand-written
//! fixtures whose indices have gaps), and `text` / `nat_decimal` render the
//! messages and decode a `natVal`'s digits.  A twin of a byte recogniser that
//! produces representation-free records would be a copy, not a port.
//!
//! `prelude_text::prelude_text()` is the same case and one more: the 67
//! byte-array chunks it is split into are a *generated* constant with
//! `scripts/gen-prelude.sh --check` behind them.
//!
//! ## The one change from the pre-arena parser: no `Expr` is ever built
//!
//! Where the `Expr`-tree parser kept an `IdTable<Expr>` of *values* and a
//! table hit was a shared node by `ron::ptr` bump, this keeps an
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
//! ## `AM` is `&mut AState` plus `Result<_, CheckError>`
//!
//! The Lean twin's monad is `StateT AState (Except CheckError)`; `AState` is
//! the store, the `ExprOps` memo tables and the per-declaration caches.
//!
//! Task #97 P4e part 1 could narrow that to the store alone — the parse
//! touched no memo — so every function that read the store took
//! `ar: &EStore` and every function that interned took `ar: &mut EStore`,
//! beside the `st: &mut StateD` that the parser already threads.
//! **Part 2 ends the narrowing on the path that needs it.**  The projection
//! rewrite (`proj_rec`) runs `ExprOps`' `instantiate1LiftFast`,
//! `liftLooseBVarsFast` and `instLPFast`, whose memos ARE `AState` fields, so
//! the eighteen functions between `chunk_step` / `chunk_finish` /
//! `parse_bytes` / `parse_chunks` and the three rewrite entry points now take
//! `ar: &mut AState` — the twin's own monad, unnarrowed — and hand
//! `&ar.store` / `&mut ar.store` to the ninety-odd that still only intern.
//! That is `prepare.rs`'s arrangement too ("`prepare_d` takes the whole
//! `AState` where everything else in this module takes the store"), and it is
//! the change part 1's note predicted, in the place that needed it.
//!
//! The four `Monad.lean` primitives at the bottom of `arena/env.rs`
//! (`view`, `viewN`, `readName`, `readLevel`) still stand where P4b left
//! them; nothing here depends on which of the two they take.
//!
//! **The modeller is NOT here.**  `InModel.generate` — the in-process
//! construction of a `_model` family for a mutual or nested block — stays in
//! the unverified crate, behind the one-method trait `types::Modeller` that
//! `export_c::parse_chunks` takes as a type parameter.  A trait method on a
//! type parameter extracts as a typeclass field, i.e. an opaque function, so
//! the extracted parse is quantified over an arbitrary modeller and the
//! refinement will carry one hypothesis about its output rather than a port of
//! four thousand lines whose correctness decides coverage and not soundness
//! (`crates/con-ron/src/in_model/mod.rs`: "soundness needs nothing from this
//! module").
//!
//! ## The loop relaxation (DESIGN.md §3.4, dated 2026-09-14)
//!
//! This directory — and only this directory — may use `while`, `loop` and
//! `for … in a..b` where the cited Lean function is a per-byte or per-element
//! tail recursion.  Lean compiles those tail calls to loops; Rust does not
//! promise to, and a per-byte recursion on a long export line is a stack
//! overflow.  Extraction runs with `-loops-to-rec`, so each loop becomes a
//! `foo_loop` function that mirrors the Lean recursion one for one, which is
//! what the refinement will be stated against.  Everything else in §3.4
//! stands.

pub mod export_c;
pub mod nat_decimal;
pub mod nat_op_ground;
pub mod prelude;
pub mod prelude_text;
pub mod prepare;
pub mod proj_rec;
pub mod scan_fast;
pub mod scan_types;
pub mod text;
pub mod types;
