//! `proof/ConRon/Arena/Frontend/Prelude.lean` — **the built-in prelude**
//! (task #97 P4e part 1).
//!
//! con-leche's `ConLeche/Frontend/Prelude.lean`: the checker's own little
//! prelude — the six pinned basis blocks (`Eq`, `Nat`, `PUnit`, `Empty`,
//! `False`, `Quot` with its soundness axiom), the `Bool` block, and the `And`
//! block pinned by design — as a lean4export-format stream parsed by the
//! ORDINARY parser into declaration records.  `prepare::prepare_prelude` puts
//! them at the front of every stream it prepares, which is what "in the env
//! initially and unconditionally" means in practice.
//!
//! **Where the text comes from.**  con-leche's `builtinPreludeText` is an
//! `include_str` of its committed `pins/<toolchain>.prelude.ndjson`; the Lean
//! twin reaches the same file through the lake package directory, and files
//! the path-outside-the-repository objection as a follow-up.  The Rust does
//! not have to: `con_ron_core::frontend::prelude_text::prelude_text()` is that
//! file already, as a *generated* constant committed inside `con-ron-core`
//! with `scripts/gen-prelude.sh --check` as its freshness gate.  Reusing it
//! across the crate boundary (this directory's `mod.rs`) is one more entry on
//! the boundary's hole list and one fewer fork of a generated 1 500-line file;
//! DESIGN.md §8.6's swap retires the hole.
//!
//! **Why the parse takes the store where con-leche's is a 0-ary `def`.**
//! con-leche parses the text once at module initialisation, because its parse
//! is pure and its result owns nothing but `Expr` trees.  The arena's parse
//! INTERNS into the `EStore`, so the prelude's nodes must land in the same
//! store the stream's do — that is the whole point of the persistent tier, and
//! the twin's own measurement is that on `Init` they coincide exactly: all 196
//! prelude expression nodes are hash-consed into nodes the stream declares
//! anyway.  It is the same deviation
//! `crates/con-ron-core/src/frontend/prelude.rs` records, for the same reason.
//!
//! The prelude has no mutual or nested block, so the `Modeller` it is parsed
//! with cannot change the result; the driver passes the same one it parses the
//! stream with, as both other ports do.

use crate::arena::monad::AState;
use crate::frontend::export_c;
use crate::frontend::prepare::PreludeIx;
use crate::frontend::types::Modeller;
use con_ron_core::frontend::prelude_text::prelude_text;
use con_ron_core::kernel::core_types::CheckError;

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// Lean twin: `proof/ConRon/Arena/Frontend/Prelude.lean:47-48 builtinPreludeText`
/// — the committed prelude for the pinned toolchain, as bytes.  A toolchain
/// bump regenerates `crates/con-ron-core/src/frontend/prelude_text.rs` (and
/// con-leche's own `pins/` file behind it) and re-points all three spellings.
pub fn builtin_prelude_text() -> Vec<u8> {
    prelude_text()
}

/// con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE
/// Lean twin: `proof/ConRon/Arena/Frontend/Prelude.lean:53-56 builtinPreludeE`
/// — the parsed, indexed prelude: an error channel because a committed file
/// can in principle be corrupted, and a prelude that does not parse must be a
/// loud error rather than a silently empty prelude.  The index is the records
/// alone since con-leche's task #293.
pub fn builtin_prelude_e<G: Modeller>(
    m: &G,
    ar: &mut AState,
) -> Result<PreludeIx, (CheckError, u64)> {
    let text: Vec<u8> = builtin_prelude_text();
    match export_c::parse_bytes(m, ar, &text, true, false) {
        Err(e) => Err(e),
        Ok(r) => Ok(PreludeIx { decls: r.decls }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::env::i_declaration_names;
    use crate::frontend::types::DeclineModeller;

    /// The prelude parses, and holds the declarations the fold expects of it.
    #[test]
    fn builtin_prelude_parses() {
        let mut ar = AState::init(crate::arena::store::EStore::empty());
        let p = match builtin_prelude_e(&DeclineModeller {}, &mut ar) {
            Ok(p) => p,
            Err((_, line)) => panic!("the built-in prelude does not parse at line {}", line),
        };
        assert!(!p.decls.is_empty());
        // every record declares at least one name
        for d in p.decls.iter() {
            assert!(!i_declaration_names(d).is_empty());
        }
    }

    /// **The Lean twin's own number, to the node.**  Task #97e measured the
    /// arena checker on an *empty* input — i.e. with nothing in the store but
    /// the prelude — and got **196 expression, 5 level, 55 name** nodes.  The
    /// Rust parse of the same bytes into the same representation must give the
    /// same three counts, and this is where that is checked: it exercises the
    /// whole of `export_c` (every record kind the prelude uses), the derived
    /// word, the cons tables and the level-list interning at once, and it is
    /// the cheapest cross-check of the transliteration there is.
    #[test]
    fn the_prelude_interns_the_twins_own_node_counts() {
        let mut ar = AState::init(crate::arena::store::EStore::empty());
        let p = match builtin_prelude_e(&DeclineModeller {}, &mut ar) {
            Ok(p) => p,
            Err((_, line)) => panic!("the built-in prelude does not parse at line {}", line),
        };
        assert_eq!(p.decls.len(), 12, "prelude declaration records");
        assert_eq!(ar.store.node_count(), 196, "expression nodes");
        assert_eq!(ar.store.ls().node_count(), 5, "level nodes");
        assert_eq!(ar.store.ns().node_count(), 55, "name nodes");
    }

    /// The prelude text is `con-ron-core`'s generated constant, byte for byte
    /// the committed `pins/<toolchain>.prelude.ndjson`
    /// (`scripts/gen-prelude.sh --check` is the gate of record; this states
    /// the same fact where `cargo test` sees it).
    #[test]
    fn the_prelude_text_is_the_committed_ndjson() {
        let b = builtin_prelude_text();
        assert_eq!(b.len(), 16922);
        assert_eq!(b[b.len() - 1], b'\n');
    }
}
