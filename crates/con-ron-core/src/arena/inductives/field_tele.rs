//! `arena::inductives::field_tele` — constructor fields' telescopes.
//!
//! The Rust twin of `proof/ConRon/Arena/Inductives/FieldTele.lean`, which is
//! `ConLeche/Kernel/Inductives/FieldTele.lean` over handles.
//!
//! ## What is ported, and what is not
//!
//! con-leche's module is the field-level vocabulary the uniform installer AND
//! its model share.  The executed checker reads exactly one of its
//! declarations, `Expr.piBinders` (the recogniser's telescope reading, the
//! positivity check's container telescopes, the recursor pre-pass).  The rest
//! — `RecFieldKind`, `recIdxOf`, `Expr.mkPisOf`, `Expr.mentionsFvar` and its
//! memo — is read by con-leche's model tier only (the uniform route's
//! positivity function classifies fields as `NestFieldKind`s and the
//! generated recursor stage as `ClassField`s), so it has no Rust counterpart;
//! `scripts/provenance-skip.txt` names each with this reason.

use crate::arena::handle::{EIdx, ETAG_FORALL_E};
use crate::arena::monad::{fail, fail_dangling_e, view_bind, AState};
use crate::arena::store::PersTier;
use crate::kernel::core_types;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::expr::BinderMeta;
use crate::ron::hashmap::Dup;

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code points (DESIGN.md §3.3)
/// `fuel exhausted: piBinders`, as code points.
pub const M_FUEL_PI_BINDERS: [u32; 25] = [
    102, 117, 101, 108, 32, 101, 120, 104, 97, 117, 115, 116, 101, 100, 58, 32, 112, 105, 66, 105,
    110, 100, 101, 114, 115,
];

/// con-leche: ConLeche/Kernel/Inductives/FieldTele.lean:45-52 Expr.piBinders
/// Lean twin: `proof/ConRon/Arena/Inductives/FieldTele.lean piBinders` — all
/// leading `∀` binders of an expression (outermost first) and the body.  Lean
/// conses on the way out; the port pushes on the way in, which is the same
/// list.  The fuel is the store walk's (the telescope is a chain of nodes).
pub fn pi_binders(
    pers: &PersTier,
    st: &AState,
    fuel: u64,
    h: &EIdx,
    out: Vec<(EIdx, BinderMeta)>,
) -> Result<(Vec<(EIdx, BinderMeta)>, EIdx), CheckError> {
    if fuel == 0 {
        fail(core_types::internal(code_points(&M_FUEL_PI_BINDERS)))
    } else if h.tag() == ETAG_FORALL_E {
        match view_bind(pers, st, h) {
            None => fail_dangling_e(),
            Some((ty, b, m)) => {
                let mut o: Vec<(EIdx, BinderMeta)> = out;
                o.push((ty, m));
                pi_binders(pers, st, fuel - 1, &b, o)
            }
        }
    } else {
        Ok((out, h.dup2()))
    }
}
