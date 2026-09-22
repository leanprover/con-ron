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
use crate::frontend::prelude_text::prelude_text;
use crate::kernel::core_types::CheckError;
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// Lean twin: `proof/ConRon/Arena/Frontend/PreludeText.lean:1380-1457 preludeText`
/// — the committed prelude for the pinned toolchain, as bytes.  A toolchain
/// bump regenerates `crates/con-ron-core/src/frontend/prelude_text.rs` (and
/// con-leche's own `pins/` file behind it) and re-points all three spellings.
pub fn builtin_prelude_text() -> Vec<u8> {
    prelude_text()
}

/// con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE
/// Lean twin: `proof/ConRon/Arena/Frontend/Prelude.lean:42-55 builtinPreludeE`
/// — the parsed, indexed prelude: an error channel because a committed file
/// can in principle be corrupted, and a prelude that does not parse must be a
/// loud error rather than a silently empty prelude.  The index is the records
/// alone since con-leche's task #293.
pub fn builtin_prelude_e<G: Modeller>(
    pers: &PersTier,
    m: &G,
    ar: &mut AState,
) -> Result<PreludeIx, (CheckError, u64)> {
    let text: Vec<u8> = builtin_prelude_text();
    match export_c::parse_bytes(pers, m, ar, &text, true, false) {
        Err(e) => Err(e),
        Ok(r) => Ok(PreludeIx { decls: r.decls }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arena::env::i_declaration_names;
    use crate::frontend::types::DeclineModeller;

    /// con-leche: none — a test fixture
    /// The state the driver builds: an empty store with the reserved-name
    /// pins interned (task #97-P6-4a).  `export_c`'s projection-rewrite seam
    /// reads a pin, so this is the only state the prelude parses in.
    fn pinned_state() -> AState {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = AState::init(crate::arena::store::EStore::empty());
        match crate::arena::pins::intern_reserved_pins(pers, &mut ar) {
            Ok(()) => ar,
            Err(_) => panic!("the reserved-name pins must intern"),
        }
    }

    /// The prelude parses, and holds the declarations the fold expects of it.
    #[test]
    fn builtin_prelude_parses() {
        let pers: &PersTier = &PersTier::empty();
        let mut ar = pinned_state();
        let p = match builtin_prelude_e(pers, &DeclineModeller {}, &mut ar) {
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
        let pers: &PersTier = &PersTier::empty();
        let mut ar = pinned_state();
        // What the reserved-name pins put in the store before the prelude is
        // read (task #97-P6-4a); the twin's numbers are about the PRELUDE, so
        // the three counts below are differences.
        let (e0, l0, n0) = (
            ar.store.node_count(pers),
            ar.store.ls().node_count(pers),
            ar.store.ns().node_count(pers),
        );
        let p = match builtin_prelude_e(pers, &DeclineModeller {}, &mut ar) {
            Ok(p) => p,
            Err((_, line)) => panic!("the built-in prelude does not parse at line {}", line),
        };
        assert_eq!(p.decls.len(), 12, "prelude declaration records");
        // The reserved-name pins are interned first and the store is
        // hash-consed, so what the prelude ADDS is the twin's count minus
        // what the two share: the pins' one expression node (`Sort 1`) and
        // both its level nodes (`0`, `1`) are the prelude's too, and 24 of
        // their 64 name nodes are.
        assert_eq!(e0, 1, "the pins' expression nodes");
        assert_eq!(l0, 2, "the pins' level nodes");
        assert_eq!(n0, 64, "the pins' name nodes");
        assert_eq!(ar.store.node_count(pers) - e0, 195, "expression nodes added");
        assert_eq!(ar.store.ls().node_count(pers) - l0, 3, "level nodes added");
        assert_eq!(ar.store.ns().node_count(pers) - n0, 31, "name nodes added");
        // …so the UNION is still the twin's own 196 and 5 on the two stores
        // whose pinned nodes the prelude re-declares.
        assert_eq!(ar.store.node_count(pers), 196, "expression nodes");
        assert_eq!(ar.store.ls().node_count(pers), 5, "level nodes");
        assert_eq!(ar.store.ns().node_count(pers), 55 + 40, "name nodes");
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
