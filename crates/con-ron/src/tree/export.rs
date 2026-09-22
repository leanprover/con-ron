//! `ConLeche/Frontend/Export.lean` — the representation-free half of the
//! parse: the parse's error monad and the record verdicts.
//!
//! **One error type for the whole accept path** (con-leche task #295).  The
//! prelude, the parse and the fold all fail in `Except (CheckError × Nat)`, so
//! the three steps chain in one `do` block — which is what con-leche's main
//! corollary states.  The frontend therefore has no error type of its own:
//! `FrontendError` is gone, and its `parseError`/`unsupported`/`invalid` were
//! the same three verdict classes as `CheckError`'s
//! `internal`/`notImplemented`/`invalid` under other names (the driver already
//! mapped both onto the same three exit codes).  The `Nat` beside the error is
//! the failure's POSITION read in the step's own unit: the **input line
//! number** in the frontend's half (0 where no line is meant — the size guard,
//! which refuses the input before reading it), the record's position in the
//! list the fold folds.
//!
//! **The canonical form is the KERNEL's** (con-leche task #293).
//! `canonLevel`/`canonExpr`/`ConstantInfo.canon` and the lockstep `canonEq*`
//! twins used to live here, because the parse did the basis matching.  The
//! fold does it now, and the kernel may not import the frontend, so they moved
//! to `ConLeche/Kernel/Canon.lean` — `con_ron_core::kernel::canon` in the port.
//! Nothing in the parse builds a canonical form any more.
//!
//! **The taint machinery is gone too** (con-leche task #292): `taintSentinel`,
//! `taintDetail` and `taintSummary` went with the parser's `sorryAx` pre-scan.
//! A `sorryAx` axiom record is now forwarded like any other record and
//! installs nothing, and a *use* of it declines at the record that uses it
//! (`core_k::unknown_const_error`, `checker_base::unresolved_consts_error`).
//! Nothing in the frontend looks at `sorryAx`.
//!
//! **Two items of the unverified twin are not here** (task #84, the crossing
//! into the core).  `cps`, the `&str`-to-code-points conversion, has no place
//! in the Aeneas subset — a message is a `const M: [u32; N]` and
//! `core_types::code_points(&M)` (DESIGN.md §3.4) — and `name_str`, the
//! driver's name rendering, is `frontend::text::name_str`, beside the other
//! two things a message interpolation does.
//!
//! Not ported, deliberately: the retired tree-size budget (a `/-! … -/`
//! section, not a declaration).

use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;

/// con-leche: ConLeche/Frontend/Export.lean:117 M
/// The parse's error monad: a message, which the caller pairs with the line
/// number it was read at.  A message is a `Vec<u32>` of code points
/// (DESIGN.md §3.3), as every Lean `String` is in the port.
pub type M<T> = Result<T, Vec<u32>>;

/// con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict
/// What a declaration record can carry out of the parse when it does not
/// produce a state: a positive DECLINE (a feature the checker does not
/// support) or a REJECT (the record's redundant fields contradict the block's
/// own declarations, which official's replay regenerates and compares).
pub enum RecordVerdict {
    Declined(Vec<u32>),
    Invalid(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Export.lean:81-85 RecordVerdict.toError
/// The checker error a record verdict becomes; the caller pairs it with the
/// line the record was read at.
pub fn record_verdict_to_error(v: RecordVerdict) -> CheckError {
    match v {
        RecordVerdict::Declined(what) => core_types::not_implemented(what),
        RecordVerdict::Invalid(what) => core_types::invalid(what),
    }
}

/// con-leche: none — `prop_when::names_beq` under a name the frontend's list
/// comparisons read as a list equality; re-exported so this module's callers
/// need not reach across the core for it.
pub fn names_beq(a: &Vec<Name>, b: &Vec<Name>) -> bool {
    prop_when::names_beq(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    /// A declined record becomes `notImplemented` and an invalid one
    /// `invalid`: the two classes the driver turns into exit 2 and exit 1.
    #[test]
    fn a_record_verdict_is_a_check_error() {
        match record_verdict_to_error(RecordVerdict::Declined(cp("nope"))) {
            CheckError::NotImplemented(m) => assert_eq!(m, cp("nope")),
            _ => panic!("a decline is not `notImplemented`"),
        }
        match record_verdict_to_error(RecordVerdict::Invalid(cp("bad"))) {
            CheckError::Invalid(m) => assert_eq!(m, cp("bad")),
            _ => panic!("an invalid record is not `invalid`"),
        }
    }
}
