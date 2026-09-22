//! `arena::core_gated` — the gated (proof-tier) knot, over handles.
//!
//! The Rust twin of `proof/ConRon/Arena/CoreGated.lean`, itself
//! `ConLeche/Kernel/CoreGated.lean`'s: `whnfCoreBody` with one clause changed
//! — the `.app` clause's β certificate is skipped when the λ-binder's
//! validated annotation licenses it — and the knot that ties it.  Every other
//! clause (iota, the projection rule, the value clauses) is `whnfCoreBody`'s,
//! verbatim, and is *called* here rather than copied: `arena::core`'s
//! `whnf_core_proj` and `whnf_core_app`'s ι half are the same functions both
//! bodies run.
//!
//! **Class (S) in the census, twinned anyway**, for the same reason as
//! `arena::core_io`: con-leche's Rust port skips the gated variants because it
//! has one knot, and so does the arena; what these declarations are is the
//! *subject* a gated-lane claims tower would be stated at, and P3 will want
//! them to exist in the arena's own spelling rather than have to invent one.
//!
//! **Unlike the io knot, this one is not a leaf**: reduction sits under
//! definitional equality and inference, so a gated `whnfCore` propagates
//! through the whole knot.  It is therefore a duplicated KNOT rather than a
//! duplicated clause — and, as in con-leche, it carries no memo: the executed
//! core is `arena::core`'s `LANE_FULL`, and a second memoized knot over the
//! same state would let one lane's table answer the other lane's query, which
//! DESIGN.md §8.3's lesson 9 forbids.  `arena::core`'s six `knot_*` functions
//! read `LANE_GATED` for exactly that: the gated body in the `whnfCore` slot
//! and no probe in any slot.
//!
//! The two β arms differ from `arena::core`'s in one further way that is
//! con-leche's, not the arena's: the gated body's certificate infers at the
//! FULL grade (`r.infer`), where `whnf_core_app`'s infers at the io grade
//! (`r.inferIO`, con-leche's task #172 B4).  Kept verbatim.

use crate::arena::core::{
    ensure_sort, intern_app_rebuilt, knot_defeq, knot_infer, knot_whnf, knot_whnf_core,
    whnf_core_proj, whnf_core_stuck_app, CORE_WALK_FUEL, LANE_GATED, M_BVAR_WHNF,
    M_LET_WHNF,
};
use crate::arena::env::IFEnv;
use crate::arena::expr_ops::instantiate1_fast;
use crate::arena::handle::{EIdx, LIdx, ETAG_LAM};
use crate::arena::monad::{fail, view, AState, fail_dangling_e, view_bind};
use crate::arena::store::ENodeView;
use crate::kernel::core_types::{code_points, CheckError};
use crate::kernel::env::CheckMode;
use crate::kernel::prop_when;
use crate::ron::hashmap::{Dup, Eq2};
use crate::arena::store::PersTier;

/// con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:50-66 whnfCoreBodyGated` —
/// **THE β SITE** of the gated body: the gate wraps the *test* only, and both
/// arms are `whnfCoreBody`'s verbatim.  The gate is `mode.verifiedChecks &&
/// mb.pw.isNever`, con-leche's own spelling, which differs from the plain
/// body's `betaGateFires` (`mode.betaGate && …`) only at `.trusted`; and the
/// certificate infers at the FULL grade, where the plain body's infers at the
/// io grade.
pub fn whnf_core_app_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    h: &EIdx,
    same: bool,
    fp: &EIdx,
    a: &EIdx,
) -> Result<EIdx, CheckError> {
    if fp.tag() == ETAG_LAM {
        match view_bind(pers, st, fp) {
            None => fail_dangling_e(),
            Some((ty, body, mb)) => {
                let ok = if crate::kernel::env::verified_checks(mode)
                    && prop_when::is_never(&mb.pw)
                {
                    Ok(true)
                } else {
                    match knot_infer(pers, vis, st, mode, lane, fuel, fe, depth, a) {
                        Err(e) => Err(e),
                        Ok(ta) => knot_defeq(pers, vis, st, mode, lane, fuel, fe, depth, &ta, &ty),
                    }
                };
                match ok {
                    Err(e) => Err(e),
                    Ok(true) => match instantiate1_fast(pers, st, CORE_WALK_FUEL, &body, a, 0) {
                        Err(e) => Err(e),
                        Ok(b) => knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &b),
                    },
                    Ok(false) => intern_app_rebuilt(pers, st, h, same, fp, a),
                }
            },
        }
    } else {
        whnf_core_stuck_app(pers, vis, st, mode, lane, fuel, fe, depth, h, same, fp, a)
    }
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:61-115 whnfCoreBodyGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:41-92 whnfCoreBodyGated` —
/// **the gated head-normalization body**: `whnfCoreBody` with the `.app`
/// clause's β certificate skipped at a `.never` binder under
/// `mode.verifiedChecks`.  The projection certificate is NOT gated — the
/// asymmetry fence keeps every zero-kind certificate, and the projection slot
/// has no `pw` datum of its own — so the `.proj` clause is `arena::core`'s,
/// called and not copied.
pub fn whnf_core_body_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    lane: u32,
    fuel: u64,
    fe: &IFEnv,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    match view(pers, st, e) {
        Err(er) => Err(er),
        Ok(ENodeView::Sort(_)) => Ok(e.dup2()),
        Ok(ENodeView::FVar(_, _)) => Ok(e.dup2()),
        Ok(ENodeView::ForallE(_, _, _)) => Ok(e.dup2()),
        Ok(ENodeView::Lam(_, _, _)) => Ok(e.dup2()),
        Ok(ENodeView::Const(_, _)) => Ok(e.dup2()),
        Ok(ENodeView::Lit(_)) => Ok(e.dup2()),
        Ok(ENodeView::App(f, a)) => {
            match knot_whnf_core(pers, vis, st, mode, lane, fuel, fe, depth, &f) {
                Err(er) => Err(er),
                Ok(fp) => {
                    let same: bool = fp.eq2(&f);
                    whnf_core_app_gated(pers, vis, st, mode, lane, fuel, fe, depth, e, same, &fp, &a)
                }
            }
        }
        Ok(ENodeView::Proj(sn, i, pe)) => {
            whnf_core_proj(pers, vis, st, mode, lane, fuel, fe, depth, &sn, i, &pe)
        }
        Ok(ENodeView::LetE(_, _, _)) => {
            fail(CheckError::Internal(code_points(&M_LET_WHNF)))
        }
        Ok(ENodeView::BVar(_)) => {
            fail(CheckError::NotImplemented(code_points(&M_BVAR_WHNF)))
        }
    }
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:117-150 coreKnotGated
/// con-leche: ConLeche/Kernel/CoreGated.lean:152-155 pureFnsGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:98-118 coreKnotGated`
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:122-123 pureFnsGated` — **the
/// P knot**, tied at `AM`: `coreKnot`'s tie with `whnfCoreBodyGated` in the
/// `whnfCore` slot; `whnf`, `infer`, `defeq` and `annotate` are the *same
/// bodies*, tied to this knot one fuel level down, and no slot carries a memo.
/// The twin's record has no Rust counterpart (§3.4 rules out a record of
/// functions); this lane tag is what `arena::core`'s `knot_*` functions read
/// instead.
pub const CORE_KNOT_GATED: u32 = LANE_GATED;

/// con-leche: ConLeche/Kernel/CoreGated.lean:157-159 whnfCoreGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:127-129 whnfCoreGated` — head
/// normalization with the β-cert gate (fueled).
pub fn whnf_core_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_whnf_core(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:161-163 whnfGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:133-135 whnfGated` — the full
/// reduction loop over the gated knot (fueled).
pub fn whnf_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_whnf(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:165-168 inferTypeCoreGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:139-141 inferTypeCoreGated` —
/// type inference over the gated knot (fueled).
pub fn infer_type_core_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    knot_infer(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:170-173 isDefEqCoreGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:145-147 isDefEqCoreGated` —
/// definitional equality over the gated knot (fueled).
pub fn is_def_eq_core_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    a: &EIdx,
    b: &EIdx,
) -> Result<bool, CheckError> {
    knot_defeq(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, a, b)
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:175-178 annotateCoreGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:151-153 annotateCoreGated` —
/// the annotation pass over the gated knot (fueled).
pub fn annotate_core_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<EIdx, CheckError> {
    crate::arena::core::knot_annotate(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, e)
}

/// con-leche: ConLeche/Kernel/CoreGated.lean:180-183 ensureSortCoreGated
/// Lean twin: `proof/ConRon/Arena/CoreGated.lean:157-159 ensureSortCoreGated` —
/// `ensureSort` over the gated knot (fueled).
pub fn ensure_sort_core_gated(
    pers: &PersTier,
    vis: u64,
    st: &mut AState,
    mode: &CheckMode,
    fe: &IFEnv,
    fuel: u64,
    depth: u64,
    e: &EIdx,
) -> Result<LIdx, CheckError> {
    ensure_sort(pers, vis, st, mode, CORE_KNOT_GATED, fuel, fe, depth, e)
}
