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
//! **How.**  The prelude is a lean4export-format stream, embedded as
//! `prelude_text::PRELUDE_TEXT` and parsed by the ordinary direct parser into
//! `Declaration` records.  `prepare::prepare_prelude` puts the prelude's
//! declarations at the front of every stream it prepares — **the stream's OWN
//! record where the stream has one**, and one of these only where it has none
//! — so "in the env initially and unconditionally" is "first in every fold",
//! and a stream that declares the toolchain's `Bool` is checked on its own
//! `Bool` record.  The records install by exactly the routes a stream's
//! records install by, the pinned blocks among them recognised by the fold
//! (`basis_raw::basis_pin_hit`).
//!
//! A parse failure — a corrupted committed file — is an `Err`, which the CLI
//! reports as exit 3 before reading any input.
//!
//! **Two deviations.**
//!
//! * con-leche's `builtinPreludeE` is a 0-ary `def`, so Lean parses the text
//!   once at process initialisation; Rust has no such thing for a value that
//!   owns counted pointers, so this is a function the caller calls once.
//! * con-leche's `builtinPreludeText` is an `include_str` of
//!   `pins/<toolchain>.prelude.ndjson`; the port's is a generated constant in
//!   the crate (`prelude_text`, `scripts/gen-prelude.sh`, gated by
//!   `--check`), for the reason `kernel/pins_text.rs` gives for the pin list,
//!   and a `[u8; N]` rather than that module's `&str` for the reason
//!   `prelude_text`'s own note gives — in fact thirty-four of them, joined by
//!   `prelude_text::prelude_text()`.  So this is `parse_bytes` of those bytes
//!   where con-leche is `parseExportD` of a `String`.
//! * the parse needs a **modeller** (`in_model_rec::Modeller`), because the
//!   parse in general does; the prelude has no mutual or nested block, so
//!   which modeller is passed cannot change the result, and the CLI passes
//!   the same one it parses the stream with.

use crate::frontend::export_c;
use crate::frontend::in_model_rec::Modeller;
use crate::frontend::prelude_text::prelude_text;
use crate::frontend::prepare::PreludeIx;
use crate::kernel::core_types::CheckError;

/// con-leche: ConLeche/Frontend/Prelude.lean:64-68 builtinPreludeE
/// The parsed, indexed prelude: `Result` because a committed file can in
/// principle be corrupted, and a prelude that does not parse must be a loud
/// error rather than a silently empty prelude.  The index is the records
/// alone since con-leche task #293 — the by-name and by-kind tables the
/// dropped dedupe needed are gone with it.
pub fn builtin_prelude_e<M: Modeller>(m: &M) -> Result<PreludeIx, (CheckError, u64)> {
    let text: Vec<u8> = prelude_text();
    match export_c::parse_bytes(m, &text, true, false) {
        Err(e) => Err(e),
        Ok(r) => Ok(PreludeIx { decls: r.decls }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::in_model_rec::{BlockRec, ModelCtx};
    use crate::kernel::env::Declaration;

    /// A modeller that declines everything: the prelude has no mutual or
    /// nested block, so it is never asked.
    struct NoModel;

    impl Modeller for NoModel {
        fn generate(
            &self,
            _ctx: &ModelCtx,
            _b: &BlockRec,
        ) -> Result<Vec<Declaration>, Vec<u32>> {
            Err(Vec::new())
        }
    }

    /// The constant is the committed ndjson byte for byte: same length, same
    /// record count, and the two non-ASCII entries survive as UTF-8.
    /// `scripts/gen-prelude.sh --check` is the gate; this states the same
    /// fact where `cargo test` sees it.
    #[test]
    fn prelude_text_is_the_committed_ndjson() {
        let bytes = prelude_text();
        assert_eq!(bytes.len(), 16922);
        assert_eq!(bytes[bytes.len() - 1], b'\n');
        let text = std::str::from_utf8(&bytes).expect("the prelude is UTF-8");
        let lines: Vec<&str> = text.lines().collect();
        assert_eq!(lines.len(), 267);
        assert!(lines[0].contains("con-leche-prelude"));
        assert!(lines[266].starts_with("{\"inductive\":"));
        assert!(text.contains("\u{3b1}"));
        assert!(text.contains("\u{3b2}"));
        // and it IS the committed file, byte for byte.  con-leche is a plain
        // lake dependency of proof/ (task #91, not vendored), so its
        // directory is resolved through `scripts/provenance.py dir` rather
        // than a fixed repository-relative path; skip the byte comparison
        // if that fails (e.g. `lake update` has not run in proof/ yet) --
        // `scripts/gen-prelude.sh --check` is the gate of record for this.
        let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        if let Ok(out) = std::process::Command::new("python3")
            .arg("scripts/provenance.py")
            .arg("dir")
            .current_dir(&root)
            .output()
        {
            if out.status.success() {
                let cl = String::from_utf8(out.stdout).unwrap().trim().to_string();
                let p = std::path::Path::new(&cl)
                    .join("pins/leanprover-lean4-v4.33.0.prelude.ndjson");
                if let Ok(f) = std::fs::read(&p) {
                    assert_eq!(&f[..], &bytes[..]);
                }
            }
        }
    }

    /// The prelude parses, and holds the declarations the fold expects of it.
    #[test]
    fn builtin_prelude_parses() {
        let p = match builtin_prelude_e(&NoModel) {
            Ok(p) => p,
            Err((_, line)) => panic!("the built-in prelude does not parse at line {}", line),
        };
        assert!(!p.decls.is_empty());
    }
}
