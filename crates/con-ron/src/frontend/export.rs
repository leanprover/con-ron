//! `ConLeche/Frontend/Export.lean` — the representation-free half of the
//! parse: the parse's error monad, the record verdicts, and the driver's name
//! rendering.
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
//! to `ConLeche/Kernel/Canon.lean` — `con_ron_core::kernel::canon` in the
//! port.  Nothing in `crates/con-ron/src` builds a canonical form any more.
//!
//! **The taint machinery is gone too** (con-leche task #292): `taintSentinel`,
//! `taintDetail` and `taintSummary` went with the parser's `sorryAx` pre-scan.
//! A `sorryAx` axiom record is now forwarded like any other record and
//! installs nothing, and a *use* of it declines at the record that uses it
//! (`core_k::unknown_const_error`, `checker_base::unresolved_consts_error`).
//! Nothing in the frontend looks at `sorryAx`.
//!
//! Not ported, deliberately: the retired tree-size budget (a `/-! … -/`
//! section, not a declaration).

use con_ron_core::kernel::core_types;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::name::Name;
use con_ron_core::kernel::prop_when;

/// con-leche: ConLeche/Frontend/Export.lean:117 M
/// The parse's error monad: a message, which the caller pairs with the line
/// number it was read at.
pub type M<T> = Result<T, String>;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code
/// points (DESIGN.md §3.3), while the frontend's own messages are Rust
/// `String`s: this is the one conversion between them, at the boundary where a
/// frontend message becomes a `CheckError`.
pub fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// con-leche: ConLeche/Frontend/Export.lean:71-79 RecordVerdict
/// What a declaration record can carry out of the parse when it does not
/// produce a state: a positive DECLINE (a feature the checker does not
/// support) or a REJECT (the record's redundant fields contradict the block's
/// own declarations, which official's replay regenerates and compares).
#[derive(Debug, Clone)]
pub enum RecordVerdict {
    Declined(String),
    Invalid(String),
}

/// con-leche: ConLeche/Frontend/Export.lean:81-85 RecordVerdict.toError
/// The checker error a record verdict becomes; the caller pairs it with the
/// line the record was read at.
pub fn record_verdict_to_error(v: RecordVerdict) -> CheckError {
    match v {
        RecordVerdict::Declined(what) => core_types::not_implemented(cps(&what)),
        RecordVerdict::Invalid(what) => core_types::invalid(cps(&what)),
    }
}

/// con-leche: none — `Name.toString`, which DESIGN.md §3.7's skip list keeps
/// out of the verified core as driver-only rendering ("the theorem never
/// reads a message").  The frontend and the CLI *are* the driver, so the
/// rendering lives here: `anonymous` is `[anonymous]`, and a component is
/// appended after a dot.
pub fn name_str(n: &Name) -> String {
    match &n.0.kind {
        con_ron_core::kernel::name::NameKind::Anonymous => "[anonymous]".to_string(),
        con_ron_core::kernel::name::NameKind::Str(p, s) => {
            let tail: String = s.iter().filter_map(|c| char::from_u32(*c)).collect();
            match &p.0.kind {
                con_ron_core::kernel::name::NameKind::Anonymous => tail,
                _ => format!("{}.{}", name_str(p), tail),
            }
        }
        con_ron_core::kernel::name::NameKind::Num(p, k) => match &p.0.kind {
            con_ron_core::kernel::name::NameKind::Anonymous => format!("{}", k),
            _ => format!("{}.{}", name_str(p), k),
        },
    }
}

/// con-leche: none — `prop_when::names_beq` under a name the frontend's list
/// comparisons read as a list equality; re-exported so this module's callers
/// need not reach into the core for it.
pub fn names_beq(a: &Vec<Name>, b: &Vec<Name>) -> bool {
    prop_when::names_beq(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::basis_builder::bn;
    use con_ron_core::kernel::name;

    fn nm(s: &str) -> Name {
        bn(cps(s))
    }

    /// A declined record becomes `notImplemented` and an invalid one
    /// `invalid`: the two classes the driver turns into exit 2 and exit 1.
    #[test]
    fn a_record_verdict_is_a_check_error() {
        match record_verdict_to_error(RecordVerdict::Declined("nope".to_string())) {
            CheckError::NotImplemented(m) => assert_eq!(m, cps("nope")),
            _ => panic!("a decline is not `notImplemented`"),
        }
        match record_verdict_to_error(RecordVerdict::Invalid("bad".to_string())) {
            CheckError::Invalid(m) => assert_eq!(m, cps("bad")),
            _ => panic!("an invalid record is not `invalid`"),
        }
    }

    /// The driver's name rendering: the anonymous root prints as itself and a
    /// component is appended after a dot.
    #[test]
    fn name_str_renders_dotted_names() {
        assert_eq!(name_str(&name::anonymous()), "[anonymous]");
        assert_eq!(name_str(&nm("Nat")), "Nat");
        assert_eq!(name_str(&name::mk_str(nm("Nat"), cps("succ"))), "Nat.succ");
        assert_eq!(name_str(&name::mk_num(nm("Nat"), 3)), "Nat.3");
    }
}
