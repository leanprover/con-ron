//! `arena-core` — the Rust side of con-ron's arena rewrite (DESIGN.md §8,
//! task #97, phase P4a).
//!
//! A **verified crate to be**: every rule of DESIGN.md §3.4 applies here as
//! it does to `con-ron-core` — no `#[derive]`, no closures, no `?`, no loops,
//! no `unsafe`, no `std::collections`, no `&str` constant, explicit fuel,
//! checked arithmetic — and `scripts/lint-rust-style.sh crates/arena-core/src`
//! enforces them.  It is a new crate rather than a module of `con-ron-core`
//! because DESIGN.md §8.6 has the rewrite grow beside the shipping checker:
//! "a new verified crate `crates/arena-core` and a binary `con-ron-arena`,
//! beside the old crates (master's gates stay green on the branch); the swap
//! to `con-ron-core`/`con-ron` happens when the fixtures and the Mathlib run
//! pass."
//!
//! ## What it is a transliteration of
//!
//! `proof/ConRon/Arena/{Handle,Store}.lean`, the Lean twin (B) frozen by
//! DESIGN.md's task #97a, function for function and clause for clause.  The
//! twin's other three modules — `Denote`, `WF`, `WFProofs` — are the arena's
//! own verification and have no Rust counterpart.  Every item here carries
//! both citations: con-leche's, as the whole port does (DESIGN.md §3.7), and
//! the Lean twin's line, so that a reader can put the two side by side and a
//! later divergence is visible without a build.
//!
//! ## Its one dependency, and what that costs the model
//!
//! `con-ron-core`, for `ron::HashMap` (and its `Hashable`/`Eq2`/`Dup`
//! dictionaries), `ron::Nat`, `kernel::core_types::CheckError`, the
//! `BinderMeta`/`Literal` values a node record carries, and — the point —
//! `kernel::expr`'s packed-word arithmetic (`pack_data`, `hash32`,
//! `sat_succ`, `sat_pred`, `max_u64`, the four field readers) and
//! `kernel::name::mix_hash`.  The derived column is **con-leche's `Expr.data`
//! computed by con-ron-core's own functions**, not a second derivation of the
//! same formulas; that is what keeps the two crates from drifting and what
//! `mod tests` checks, term by term, against `expr::data` of the tree the
//! same constructors build.
//!
//! The price is paid at extraction, and it is worth stating plainly, because
//! P4a measured it (DESIGN.md's task #97-P4a): **Charon does not descend into
//! a path dependency.**  Running `charon cargo` here translates this crate's
//! bodies in full and turns every `con_ron_core::…` item it calls into an
//! `@[rust_fun]`/`@[rust_type]` axiom in `FunsExternal_Template.lean`.
//! Asking it to (`charon cargo --include 'con_ron_core::_'`) does translate
//! them, but from the dependency's *optimized* MIR — the only stage Charon
//! has for a dependency — and Aeneas then fails on `HashMap::
//! move_elements_from_list` ("There should be no bottoms in the value").  So
//! the arena's model is complete and the boundary is a documented hole list
//! until DESIGN.md §8.6's swap merges the two crates, at which point the
//! boundary is gone and `scripts/extract.sh`'s single-crate run covers
//! everything again.

pub mod arena;
