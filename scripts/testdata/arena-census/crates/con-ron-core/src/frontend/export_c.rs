//! The fixture's `frontend::export_c` and `frontend::prelude`.

/// con-leche: ConLeche/Frontend/ExportC.lean:200-210 reboundError
/// Lean twin: `proof/ConRon/Arena/Frontend/ExportC.lean reboundError`
pub fn rebound_error(n: &NIdx) {}

/// con-leche: ConLeche/Frontend/Prelude.lean:10-20 builtinPreludeText
/// Lean twin: `proof/ConRon/Arena/Frontend/PreludeText.lean preludeText`
pub fn builtin_prelude_text() -> Vec<u8> {
    Vec::new()
}
