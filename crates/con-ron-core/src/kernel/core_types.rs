//! The checker's error type and its monad — the head of
//! `ConLeche/Kernel/Core.lean` (lines 45-59), ported ahead of the core
//! bodies themselves because every module below the core throws into it.
//!
//! The rest of `Core.lean` (the `CoreFns` record of closures and the check
//! bodies written against it) is a later task: DESIGN.md §3.1 ties that knot
//! with a mutually recursive block of wrappers rather than a record, so it is
//! not a type this module can carry.
//!
//! ## `CheckM` is Rust's `Result`
//!
//! con-leche's `abbrev CheckM := Except CheckError` is the error monad the
//! pure core runs in; the cached core runs in `StateT CState CheckM`
//! (`ConLeche/Cached/StateC.lean:166`).  The port's convention, as DESIGN.md
//! §3.4 fixes it:
//!
//! | Lean | Rust |
//! |---|---|
//! | `CheckM α` | `Result<A, CheckError>` |
//! | `pure a` | `Ok(a)` |
//! | `throw e` | `Err(e)` |
//! | `x ← m; k x` | `match m { Ok(x) => k(x), Err(e) => Err(e) }` |
//! | `CheckCM α` = `StateT CState CheckM α` | `fn(…, &mut CState) -> Result<A, CheckError>` |
//!
//! The `match` spelling is deliberate: §3.4 forbids `?`, so that the
//! generated Lean keeps the shape of con-leche's own `do` block, one bind per
//! bind.  Aeneas's `Result` (the failure monad every generated function
//! already lives in) is a *different* thing — it is where a Rust panic,
//! overflow or failed index lands — so a ported function's type is
//! `Result (core.result.Result A CheckError)` in the generated Lean: the
//! outer one is Rust failure (nothing is claimed about it, §3.5), the inner
//! one is con-leche's `Except`.
//!
//! ## Messages are `Vec<u32>` code points
//!
//! `CheckError`'s three payloads are `String` in Lean and `Vec<u32>` here,
//! as DESIGN.md §3.3 has every other string in the core.  The choice was
//! *measured* on a spike (task #14, `_tmp/strspike`), not assumed:
//!
//! * `String` payloads translate fine as a *type* (Aeneas prints Lean's own
//!   `String`), but every way of making one is an external hole —
//!   `String::from("…")` emits an axiom
//!   `alloc.string.String.Insts.CoreConvertFromShared0Str.from : Str →
//!   Result String` into `FunsExternal_Template.lean`, and `String::new()`
//!   emits `alloc.string.String.new`.  DESIGN.md §3.2's standing gate is
//!   that the external templates hold exactly the four pointer axioms, so a
//!   fifth, string-shaped one is not free.
//! * A `&'static str` payload is worse: Aeneas fails outright on a string
//!   literal (*"There should be no bottoms in the value"*) and emits a
//!   `sorry` for the constructing function.
//! * `Vec<u32>` adds **no** hole: `Vec::new`, a `[u32; N]` constant,
//!   `Array.to_slice` and a slice walk are all modeled already.
//!
//! Messages are never read by the theorem (§3.1: *"the same error kinds
//! (message strings need not match — the theorem never reads them)"*), so
//! the representation is free to be the cheap one.  The idiom for a throw
//! site is a `const M_…: [u32; N]` of ASCII code points next to it and
//! `code_points(&M_…)`; an empty `Vec::new()` is a legitimate message too.
//! `code_points` is the port's general spelling of a Lean string literal —
//! `env::proj_fn_name`'s `"proj"` goes through it too.

use crate::kernel::name;
use std::vec::Vec;

/// con-leche: ConLeche/Kernel/Core.lean:68-72 CheckError
/// The checker's error, in the cited constructor order, **plus a fourth
/// constructor the cited type does not have**.
///
/// Deviations: the `String` payloads are `Vec<u32>` code points (the module
/// note above), and `deriving Repr` is dropped — rendering only, and §3.4
/// forbids `derive(Debug)` on the core types anyway.  The `ToString`
/// instance at `Core.lean:53-57` is not ported for the same reason; the CLI
/// (`crates/con-ron`, outside the verified core) renders errors.
///
/// **`Native` (DESIGN.md §3, the ruling of 2026-09-13).**  The port throws
/// in places the cited checker cannot fail at all: a machine word overflows
/// where `Nat` grows, a shift amount leaves `u64`, an index does not fit a
/// `u32`.  Those failures have no con-leche counterpart, so they are not
/// `Invalid`/`Internal` — mixing them in would make the refinement claim
/// "con-leche throws here too", which is false.  `Native` is the port's own
/// decline: the refinement lemmas (`Refine/Core/Statements.lean`'s `Out`)
/// claim *nothing* about a run that ends in one, and `absErrKind` maps it to
/// `none`, while the three mirrored constructors keep con-leche's meaning
/// and are claimed exactly.  Every `Native` site is a documented
/// accept-direction deviation (§3's list): it declines a stream con-leche
/// might accept, and never accepts one con-leche declines.
pub enum CheckError {
    NotImplemented(Vec<u32>),
    Invalid(Vec<u32>),
    Internal(Vec<u32>),
    Native(Vec<u32>),
}

/// con-leche: ConLeche/Kernel/Core.lean:80 CheckM
/// `abbrev CheckM := Except CheckError`, as Rust's `Result` (the module note
/// above spells out the correspondence).  A type alias is erased before
/// Charon sees anything, so this costs the generated Lean nothing; it is
/// here so that a ported signature can *say* `CheckM<Expr>` where con-leche
/// says `CheckM Expr`.
pub type CheckM<T> = Result<T, CheckError>;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// Copy a `const …: [u32; N]` of code points into an owned `Vec<u32>`.  This
/// is how the port spells a Lean string *literal*: an error message here, a
/// `Name` component in `env::proj_fn_name` (`"proj"`), and so on.
pub fn code_points(codes: &[u32]) -> Vec<u32> {
    code_points_from(codes, 0, Vec::with_capacity(codes.len()))
}

/// con-leche: none — the index recursion behind `code_points`
/// The accumulator is passed by value and returned (§3.4 reserves `&mut` for
/// the state parameter; task #6's rule).
pub fn code_points_from(codes: &[u32], i: usize, out: Vec<u32>) -> Vec<u32> {
    if i >= codes.len() {
        out
    } else {
        let mut out = out;
        out.push(codes[i]);
        code_points_from(codes, i + 1, out)
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:68-72 CheckError
/// `throw (.notImplemented what)`'s payload, as a constructor function.
pub fn not_implemented(what: Vec<u32>) -> CheckError {
    CheckError::NotImplemented(what)
}

/// con-leche: ConLeche/Kernel/Core.lean:68-72 CheckError
/// `throw (.invalid msg)`'s payload, as a constructor function.
pub fn invalid(m: Vec<u32>) -> CheckError {
    CheckError::Invalid(m)
}

/// con-leche: ConLeche/Kernel/Core.lean:68-72 CheckError
/// `throw (.internal msg)`'s payload, as a constructor function.
pub fn internal(m: Vec<u32>) -> CheckError {
    CheckError::Internal(m)
}

/// con-leche: none — Rust-only failures, DESIGN.md §3
/// The port's own decline, with no `throw` behind it: a machine-word limit
/// or a width check the cited code does not have (the note on `CheckError`
/// above).  A site that throws this is *not* claimed to be a con-leche
/// throw; it is claimed to be a decline.
pub fn native(m: Vec<u32>) -> CheckError {
    CheckError::Native(m)
}

/// con-leche: ConLeche/Kernel/Checker.lean:333-337 divModAttemptReason
/// The message out of an error, by move.  The cited `divModAttemptReason ps
/// (some e)` renders `e` into the variant's decline reason with `toString`;
/// the port has no `ToString` instance (the note on `CheckError` above) and
/// no accumulator (`kernel::checker`'s module note 2), so the reason *is* the
/// payload, and `check_div_mod_pin_loop` carries it to the final
/// `notImplemented`.  The kind is dropped, which is what makes this the whole
/// of the cited rendering: the decline con-leche throws at the end of the
/// loop is a `notImplemented` whatever the variants threw.
pub fn message(e: CheckError) -> Vec<u32> {
    match e {
        CheckError::NotImplemented(m) => m,
        CheckError::Invalid(m) => m,
        CheckError::Internal(m) => m,
        CheckError::Native(m) => m,
    }
}

/// con-leche: none — a `Vec<u32>` copy; Lean's `String` is shared by value
/// The code-point copy a reused message needs.
pub fn str_copy(s: &Vec<u32>) -> Vec<u32> {
    code_points_from(s, 0, Vec::with_capacity(s.len()))
}

/// con-leche: none — the `dup` of `CheckError`, which Lean's value semantics hides
/// DESIGN.md §3.4: no `derive(Clone)` on the core types; an explicit copy per
/// type, as `nat.rs` and `name.rs` do.
pub fn dup(e: &CheckError) -> CheckError {
    match e {
        CheckError::NotImplemented(w) => CheckError::NotImplemented(str_copy(w)),
        CheckError::Invalid(m) => CheckError::Invalid(str_copy(m)),
        CheckError::Internal(m) => CheckError::Internal(str_copy(m)),
        CheckError::Native(m) => CheckError::Native(str_copy(m)),
    }
}

/// con-leche: ConLeche/Kernel/Core.lean:68-72 CheckError
/// The structural equality the cited `inductive` would derive; the payloads
/// are compared with `name::str_eq`, the port's code-point equality.  Nothing
/// in the checker branches on an error, so this exists for the tests and for
/// the differential harness's verdict comparison.
pub fn beq(a: &CheckError, b: &CheckError) -> bool {
    match a {
        CheckError::NotImplemented(x) => match b {
            CheckError::NotImplemented(y) => name::str_eq(x, y),
            CheckError::Invalid(_) => false,
            CheckError::Internal(_) => false,
            CheckError::Native(_) => false,
        },
        CheckError::Invalid(x) => match b {
            CheckError::NotImplemented(_) => false,
            CheckError::Invalid(y) => name::str_eq(x, y),
            CheckError::Internal(_) => false,
            CheckError::Native(_) => false,
        },
        CheckError::Internal(x) => match b {
            CheckError::NotImplemented(_) => false,
            CheckError::Invalid(_) => false,
            CheckError::Internal(y) => name::str_eq(x, y),
            CheckError::Native(_) => false,
        },
        CheckError::Native(x) => match b {
            CheckError::NotImplemented(_) => false,
            CheckError::Invalid(_) => false,
            CheckError::Internal(_) => false,
            CheckError::Native(y) => name::str_eq(x, y),
        },
    }
}

#[cfg(test)]
mod tests {
    use crate::kernel::core_types;
    use crate::kernel::core_types::CheckError;

    /// An ASCII message, spelled the way a throw site spells one.
    const M_DUP: [u32; 9] = [
        0x64, 0x75, 0x70, 0x6c, 0x69, 0x63, 0x61, 0x74, 0x65,
    ];
    const M_OTHER: [u32; 4] = [0x62, 0x61, 0x64, 0x21];

    #[test]
    fn code_points_is_the_code_points() {
        let v = core_types::code_points(&M_DUP);
        assert_eq!(v.len(), 9);
        assert_eq!(v, vec![0x64, 0x75, 0x70, 0x6c, 0x69, 0x63, 0x61, 0x74, 0x65]);
        assert_eq!(core_types::code_points(&[]), Vec::<u32>::new());
    }

    #[test]
    fn beq_separates_kind_and_payload() {
        let a = core_types::invalid(core_types::code_points(&M_DUP));
        let b = core_types::invalid(core_types::code_points(&M_DUP));
        let c = core_types::invalid(core_types::code_points(&M_OTHER));
        let d = core_types::internal(core_types::code_points(&M_DUP));
        let e = core_types::not_implemented(core_types::code_points(&M_DUP));
        assert!(core_types::beq(&a, &b));
        assert!(!core_types::beq(&a, &c));
        assert!(!core_types::beq(&a, &d));
        assert!(!core_types::beq(&a, &e));
        assert!(!core_types::beq(&d, &e));
        assert!(core_types::beq(&a, &core_types::dup(&a)));
    }

    /// The `CheckM` convention of the module note: `Ok`/`Err`, no `?`.
    #[test]
    fn check_m_is_result() {
        fn ok_or_bad(b: bool) -> core_types::CheckM<u64> {
            if b {
                Ok(7)
            } else {
                Err(core_types::invalid(core_types::code_points(&M_OTHER)))
            }
        }
        assert!(matches!(ok_or_bad(true), Ok(7)));
        match ok_or_bad(false) {
            Ok(_) => panic!("expected an error"),
            Err(CheckError::Invalid(m)) => assert_eq!(m.len(), 4),
            Err(_) => panic!("wrong error kind"),
        }
    }
}
