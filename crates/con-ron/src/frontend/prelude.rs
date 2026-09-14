//! `ConLeche/Frontend/Prelude.lean` — the built-in prelude.
//!
//! **What it is.**  The checker's own little prelude: the six pinned basis
//! blocks (`Eq`, `Nat`, `PUnit`, `Empty`, `False`, `Quot` with its soundness
//! axiom), the `Bool` block — every declaration the pin-certified `Nat`
//! operations' install needs that is neither in the operation's own
//! dependency closure nor a stream-certified operation itself — and the `And`
//! block, pinned by design (the one propositional structure whose recursor
//! the stuck-major rescue serves, keyed on the name, so the name must denote
//! the toolchain's `And` in every fold).
//!
//! **Why.**  A user report (2026-09-06): the Nat-op pins were sensitive to
//! the stream's installation order — an export that emits `Nat.shiftLeft`
//! before the `Bool`/`Eq` blocks its certificate statements are spelled over
//! declined at the install.  The user's directive: *"add Bool and what else
//! is needed … and actually add them to the env initially and
//! unconditionally (our own little prelude).  when they come later in the
//! stream, just compare and decline if different."*
//!
//! **How.**  The prelude is a lean4export-format stream, embedded here with
//! `include_str!` (con-leche's `include_str`) and parsed by the ordinary
//! direct parser into `Declaration` records.  `prepare::prepare_prelude` puts
//! the prelude's declarations at the front of every stream it prepares — **the
//! stream's OWN record where the stream has one**, and one of these only where
//! it has none — so "in the env initially and unconditionally" is "first in
//! every fold", and a stream that declares the toolchain's `Bool` is checked
//! on its own `Bool` record.  The records install by exactly the routes a
//! stream's records install by, the pinned blocks among them recognised by the
//! fold (`basis_raw::basis_pin_hit`).
//!
//! A parse failure — a corrupted committed file — is an `Err`, which the CLI
//! reports as exit 3 before reading any input.  Deviation: con-leche's
//! `builtinPreludeE` is a 0-ary `def`, so Lean parses the text once at
//! process initialisation; Rust has no such thing for a value that owns
//! `Rc`s, so this is a function the CLI calls once.  The committed file is
//! read out of the vendored con-leche at *compile* time, which is what keeps
//! the binary self-contained.

use con_ron_core::kernel::core_types::CheckError;

use crate::frontend::export_c::parse_export_d;
use crate::frontend::prepare::PreludeIx;

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// The committed prelude for the pinned toolchain (`lean-toolchain`),
/// embedded at build time.  A toolchain bump regenerates it and re-points
/// this path.
pub const BUILTIN_PRELUDE_TEXT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../vendor/con-leche/pins/leanprover-lean4-v4.33.0.prelude.ndjson"
));

/// con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE
/// The parsed, indexed prelude: `Result` because a committed file can in
/// principle be corrupted, and a prelude that does not parse must be a loud
/// error rather than a silently empty prelude.  The index is the records
/// alone since con-leche task #293 — the by-name and by-kind tables the
/// dropped dedupe needed are gone with it.
pub fn builtin_prelude_e() -> Result<PreludeIx, (CheckError, u64)> {
    let r = parse_export_d(BUILTIN_PRELUDE_TEXT, true, false)?;
    Ok(PreludeIx { decls: r.decls })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::export::name_str;
    use crate::frontend::prepare::prelude_key;
    use con_ron_core::kernel::env::Declaration;

    /// A failed prelude parse, rendered for a panic message: `CheckError`
    /// carries code points and derives no `Debug`.
    fn show(e: &(CheckError, u64)) -> String {
        let m = match &e.0 {
            CheckError::NotImplemented(m)
            | CheckError::Invalid(m)
            | CheckError::Internal(m)
            | CheckError::Native(m) => m,
        };
        let t: String = m.iter().filter_map(|c| char::from_u32(*c)).collect();
        format!("line {}: {}", e.1, t)
    }

    /// The committed prelude parses, and holds what con-leche's own test
    /// pins: the blocks the pin-certified `Nat` operations need, each as the
    /// ordinary record the file declares — since con-leche task #293 the
    /// decoder recognises nothing, so `Eq`, `Nat` and `Bool` are `IndDecl`s
    /// and the quotient package is four `QuotDecl`s.
    #[test]
    fn the_builtin_prelude_parses_and_holds_the_pinned_set() {
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{}", show(&e)));
        let keys: Vec<String> = ix.decls.iter().map(|d| name_str(&prelude_key(d))).collect();
        for n in ["Eq", "Nat", "PUnit", "Empty", "False", "Bool", "And"] {
            assert!(keys.contains(&n.to_string()), "missing {}: {:?}", n, keys);
        }
        // the four `#QUOT` records, one per kind, plus `Quot.sound` as the
        // ordinary axiom record it is
        let n_quot = ix
            .decls
            .iter()
            .filter(|d| matches!(d, Declaration::QuotDecl(_, _)))
            .count();
        assert_eq!(n_quot, 4, "{:?}", keys);
        assert!(keys.contains(&"Quot.sound".to_string()), "{:?}", keys);
    }

    /// The decoder recognises no basis block any more (con-leche task #293):
    /// nothing in a parsed stream is a `BasisDecl`, the prelude included.
    /// Recognising the pinned shapes is the fold's.
    #[test]
    fn the_parse_produces_no_basis_block() {
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{}", show(&e)));
        assert!(!ix
            .decls
            .iter()
            .any(|d| matches!(d, Declaration::BasisDecl(_))));
    }
}
