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
//! direct parser into `DeclC` records — the basis blocks through the same pin
//! match as any stream's, `Bool` as an ordinary inductive block the direct
//! sum install serves.  Every stream parse is handed it, PREPENDS it to its
//! result and DEDUPES against it (`export_c::push_decl`).  So "in the env
//! initially and unconditionally" is "first in every fold": the verified fold
//! `check_decls` sees `prelude ++ stream'` as one list of records and
//! installs the prelude by exactly the routes it installs a stream's records
//! by.
//!
//! A parse failure — a corrupted committed file — is an `Err`, which the CLI
//! reports as exit 3 before reading any input.  Deviation: con-leche's
//! `builtinPreludeE` is a 0-ary `def`, so Lean parses the text once at
//! process initialisation; Rust has no such thing for a value that owns
//! `Rc`s, so this is a function the CLI calls once.  The committed file is
//! read out of the pinned submodule at *compile* time, which is what keeps
//! the binary self-contained.

use crate::frontend::export::FrontendError;
use crate::frontend::export_c::{parse_export_d, prelude_ix_empty, PreludeIx};

/// con-leche: ConLeche/Frontend/Prelude.lean:57-62 builtinPreludeText
/// The committed prelude for the pinned toolchain (`lean-toolchain`),
/// embedded at build time.  A toolchain bump regenerates it and re-points
/// this path.
pub const BUILTIN_PRELUDE_TEXT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../vendor/con-leche/pins/leanprover-lean4-v4.33.0.prelude.ndjson"
));

/// con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE
/// con-leche: CHANGED since 405d06b7 — re-port, re-test, re-prove prelude::builtin_prelude_e_refines, then delete this line
/// The parsed, indexed prelude: `Result` because a committed file can in
/// principle be corrupted, and a prelude that does not parse must be a loud
/// error rather than a silently empty prelude.
pub fn builtin_prelude_e() -> Result<PreludeIx, FrontendError> {
    let r = parse_export_d(
        BUILTIN_PRELUDE_TEXT.as_bytes(),
        prelude_ix_empty(),
        true,
        false,
    )?;
    Ok(crate::frontend::export_c::prelude_ix_of_decls(r.decls))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::export::name_str;
    use crate::frontend::export_c::basis_kind_beq;
    use con_ron_core::cached::parsed_c::DeclC;
    use con_ron_core::kernel::env::BasisKind;

    /// The committed prelude parses, and holds exactly what con-leche's own
    /// test pins: the six basis blocks by kind, plus `Bool` and `And` as
    /// ordinary inductive records.
    #[test]
    fn the_builtin_prelude_parses_and_holds_the_pinned_set() {
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{:?}", e));
        for k in [
            BasisKind::EqK,
            BasisKind::NatK,
            BasisKind::PunitK,
            BasisKind::EmptyK,
            BasisKind::FalseK,
            BasisKind::QuotK,
        ] {
            assert!(
                ix.basis.iter().any(|b| basis_kind_beq(b, &k)),
                "missing basis block"
            );
        }
        let mut ind_names: Vec<String> = Vec::new();
        for d in ix.decls.iter() {
            if let DeclC::IndDecl(block, _) = d {
                ind_names.push(name_str(
                    &con_ron_core::kernel::env::constant_info_name(&block[0]),
                ));
            }
        }
        assert!(ind_names.contains(&"Bool".to_string()), "{:?}", ind_names);
        assert!(ind_names.contains(&"And".to_string()), "{:?}", ind_names);
        // every record is indexed by every name it declares
        assert!(!ix.by_name.is_empty());
    }

    /// The prelude's own basis blocks were matched against the RAW pins:
    /// `basis_raw` is what made them `BasisDecl`s rather than `IndDecl`s, so a
    /// `Nat` inductive record in the prelude would mean the pin match failed.
    #[test]
    fn the_prelude_matched_the_raw_pins() {
        let ix = builtin_prelude_e().unwrap_or_else(|e| panic!("{:?}", e));
        let n_basis = ix
            .decls
            .iter()
            .filter(|d| matches!(d, DeclC::BasisDecl(_)))
            .count();
        assert_eq!(n_basis, 6, "the six pinned basis blocks");
    }
}
